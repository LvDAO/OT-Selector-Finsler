"""Durable, detached embedding jobs for committed proof-atlas DAG snapshots.

Run ``python3 -m tools.proof_atlas.embedding_queue {submit,status,work}``.
Submission never loads a model or reads the working tree. The existing vector
builder owns chunking, cache recovery and atomic publication. Each build reads
one SQLite WAL snapshot, so later DAG imports can commit while inference runs.
"""
from __future__ import annotations

import argparse
from contextlib import contextmanager
from datetime import datetime, timezone
import fcntl
import hashlib
import json
import os
from pathlib import Path
import sqlite3
import subprocess
import sys
import time
import traceback
from typing import Any, Callable
from urllib.parse import quote

from .embedding import default_qwen_model_directory
from .store import Store

ROOT = Path(__file__).resolve().parents[2]
DEFAULT_DATA = ROOT.parent / "otselector-index"
DEFAULT_VIEWS = ("conditions", "objects", "proof_detail", "full_proof", "proof_state")
SUPPORTED_VIEWS = {*DEFAULT_VIEWS, "statement"}


def _json(value: Any) -> str:
    return json.dumps(value, ensure_ascii=False, sort_keys=True, separators=(",", ":"))


def _now() -> str:
    return datetime.now(timezone.utc).isoformat()


def _hash(value: Any) -> str:
    return hashlib.sha256(_json(value).encode()).hexdigest()


def normalize_options(options: dict[str, Any] | None = None) -> dict[str, Any]:
    options = dict(options or {})
    allowed = {"embedding", "model_dir", "embedding_url", "device", "worker_python",
               "views", "batch_size", "chunk_tokens", "include_internal", "pending_buffer"}
    if options.keys() - allowed:
        raise ValueError("unknown embedding options: " + ", ".join(sorted(options.keys() - allowed)))
    backend = options.get("embedding", "qwen")
    if backend not in {"qwen", "tei"}:
        raise ValueError("embedding must be qwen or tei")
    model = options.get("model_dir") or os.getenv(
        "PROOF_ATLAS_QWEN_MODEL_DIR" if backend == "qwen" else "PROOF_ATLAS_EMBEDDING_MODEL_DIR")
    if backend == "qwen" and not model:
        model = default_qwen_model_directory()
    views = options.get("views")
    if isinstance(views, str):
        views = [views]
    views = sorted(set(DEFAULT_VIEWS if views is None else views))
    if not views or not set(views) <= SUPPORTED_VIEWS:
        raise ValueError("select one or more supported proof views")
    result = {"embedding": backend,
              "model_dir": str(Path(model).expanduser().resolve()) if model else None,
              "embedding_url": options.get("embedding_url") or os.getenv("PROOF_ATLAS_EMBEDDING_URL"),
              "device": options.get("device", "auto"),
              "worker_python": options.get("worker_python") or os.getenv("PROOF_ATLAS_WORKER_PYTHON")
              or sys.executable,
              "views": views, "include_internal": bool(options.get("include_internal", False))}
    for key, default in (("batch_size", 16), ("chunk_tokens", 1024), ("pending_buffer", 512)):
        result[key] = int(options.get(key, default))
        if result[key] < 1:
            raise ValueError(key + " must be positive")
    return result


class SnapshotStore(Store):
    """Store's read API over a genuinely read-only connection, without schema writes."""

    def __init__(self, path: Path):
        self.path = path
        self.conn = sqlite3.connect("file:" + quote(str(path)) + "?mode=ro", uri=True, timeout=10)
        self.conn.row_factory = sqlite3.Row
        self.conn.execute("PRAGMA query_only=ON")
        self.conn.execute("PRAGMA busy_timeout=10000")


@contextmanager
def dag_snapshot(data_dir: Path):
    """Pin the first read until build finishes; WAL writers remain independent."""
    with SnapshotStore(data_dir / "atlas.sqlite3") as store:
        store.conn.execute("BEGIN")
        try:
            state = store.snapshot_status()  # First SELECT fixes the WAL read view.
            if not state.get("source_bound") or state.get("stale") is True:
                raise ValueError("DAG snapshot is empty, unbound or incompletely merged")
            source = {key: state[key] for key in ("snapshot_id", "content_hash", "imported_at")}
            yield store, source
        finally:
            store.conn.rollback()


def _source_key(source: dict[str, Any]) -> str:
    return _hash({key: source[key] for key in ("snapshot_id", "content_hash")})


class EmbeddingQueue:
    def __init__(self, data_dir: str | Path, project_root: str | Path = ROOT):
        self.data_dir = Path(data_dir).expanduser().resolve()
        self.project_root = Path(project_root).expanduser().resolve()
        if self.data_dir == self.project_root or self.project_root in self.data_dir.parents:
            raise ValueError("choose --data-dir outside the repository")
        self.data_dir.mkdir(parents=True, exist_ok=True)
        self.path = self.data_dir / "embedding-queue.sqlite3"
        self.lock_path = self.data_dir / "embedding-worker.lock"
        self.conn = sqlite3.connect(self.path, timeout=10)
        self.conn.row_factory = sqlite3.Row
        self.conn.execute("PRAGMA journal_mode=WAL")
        self.conn.execute("PRAGMA busy_timeout=10000")
        self.conn.executescript("""
            CREATE TABLE IF NOT EXISTS jobs (
                id INTEGER PRIMARY KEY, source_key TEXT NOT NULL, source_json TEXT NOT NULL,
                config_hash TEXT NOT NULL, options_json TEXT NOT NULL,
                state TEXT NOT NULL CHECK(state IN ('queued','running','succeeded','failed','superseded')),
                created_at TEXT NOT NULL, updated_at TEXT NOT NULL, started_at TEXT, finished_at TEXT,
                attempts INTEGER NOT NULL DEFAULT 0, superseded_by INTEGER,
                last_error TEXT, result_json TEXT, UNIQUE(source_key,config_hash));
            CREATE INDEX IF NOT EXISTS jobs_ready ON jobs(state,id);
            CREATE TABLE IF NOT EXISTS attempts (
                id INTEGER PRIMARY KEY, job_id INTEGER NOT NULL, number INTEGER NOT NULL,
                state TEXT NOT NULL, started_at TEXT NOT NULL, finished_at TEXT,
                error TEXT, result_json TEXT, UNIQUE(job_id,number));
            CREATE TABLE IF NOT EXISTS events (
                id INTEGER PRIMARY KEY, job_id INTEGER, at TEXT NOT NULL,
                kind TEXT NOT NULL, details_json TEXT NOT NULL);
            CREATE TABLE IF NOT EXISTS followups (
                config_hash TEXT PRIMARY KEY, options_json TEXT NOT NULL,
                after_source_key TEXT NOT NULL);
        """)

    def close(self):
        self.conn.close()

    def __enter__(self):
        return self

    def __exit__(self, *_):
        self.close()

    def _event(self, kind: str, job_id: int | None = None, **details):
        self.conn.execute("INSERT INTO events(job_id,at,kind,details_json) VALUES (?,?,?,?)",
                          (job_id, _now(), kind, _json(details)))

    @staticmethod
    def _job(row) -> dict[str, Any]:
        result = dict(row)
        for name in ("source", "options", "result"):
            raw = result.pop(name + "_json")
            result[name] = json.loads(raw) if raw else None
        return result

    def job(self, job_id: int) -> dict[str, Any]:
        row = self.conn.execute("SELECT * FROM jobs WHERE id=?", (job_id,)).fetchone()
        if row is None:
            raise ValueError(f"unknown job {job_id}")
        return self._job(row)

    def _enqueue(self, source: dict[str, Any], options: dict[str, Any], *, retry=False):
        """Called only inside a short queue transaction, never during inference."""
        key, config, now = _source_key(source), _hash(options), _now()
        existing = self.conn.execute("SELECT * FROM jobs WHERE source_key=? AND config_hash=?",
                                     (key, config)).fetchone()
        deduplicated = existing is not None
        if existing is None:
            cursor = self.conn.execute("""INSERT INTO jobs
                (source_key,source_json,config_hash,options_json,state,created_at,updated_at)
                VALUES (?,?,?,?,'queued',?,?)""", (key, _json(source), config, _json(options), now, now))
            job_id = cursor.lastrowid
            self._event("submitted", job_id)
        else:
            job_id = existing["id"]
            if existing["state"] == "superseded" or (retry and existing["state"] == "failed"):
                self.conn.execute("""UPDATE jobs SET state='queued',superseded_by=NULL,
                    updated_at=?,finished_at=NULL WHERE id=?""", (now, job_id))
                self._event("retry" if retry else "reactivated", job_id)
        pending = self.conn.execute("""SELECT id FROM jobs WHERE config_hash=?
            AND state='queued' AND id!=?""", (config, job_id)).fetchall()
        for old in pending:
            self.conn.execute("""UPDATE jobs SET state='superseded',superseded_by=?,
                updated_at=?,finished_at=? WHERE id=?""", (job_id, now, now, old["id"]))
            self._event("coalesced", old["id"], latest_job_id=job_id)
        return self.job(job_id), deduplicated

    def submit(self, options=None, *, retry_job: int | None = None):
        if retry_job is not None:
            previous = self.job(retry_job)
            if previous["state"] != "failed":
                raise ValueError("only failed jobs need an explicit retry")
            options = previous["options"]
        # Retry exactly the saved configuration, including deliberately unset fields.
        options = options if retry_job is not None else normalize_options(options)
        with dag_snapshot(self.data_dir) as (_, source):
            pass
        with self.conn:
            job, duplicate = self._enqueue(source, options, retry=retry_job is not None)
        return {"job": job, "deduplicated": duplicate, "retry_of": retry_job}

    def claim(self):
        with self.conn:
            self.conn.execute("BEGIN IMMEDIATE")
            row = self.conn.execute("SELECT * FROM jobs WHERE state='queued' ORDER BY id LIMIT 1").fetchone()
            if row is None:
                return None
            now, number = _now(), row["attempts"] + 1
            self.conn.execute("""UPDATE jobs SET state='running',attempts=?,started_at=?,
                finished_at=NULL,updated_at=? WHERE id=?""", (number, now, now, row["id"]))
            self.conn.execute("""INSERT INTO attempts(job_id,number,state,started_at)
                VALUES (?,?,'running',?)""", (row["id"], number, now))
            self._event("claimed", row["id"], attempt=number)
        return self.job(row["id"])

    def recover(self):
        # The process-wide worker lock proves that no live worker owns these jobs.
        with self.conn:
            running = self.conn.execute("SELECT id FROM jobs WHERE state='running'").fetchall()
            for row in running:
                now = _now()
                self.conn.execute("UPDATE jobs SET state='queued',updated_at=? WHERE id=?", (now, row["id"]))
                self.conn.execute("""UPDATE attempts SET state='interrupted',finished_at=?,
                    error='worker exited before recording completion' WHERE job_id=? AND state='running'""",
                                  (now, row["id"]))
                self._event("recovered", row["id"])

    def finish(self, job, state, *, result=None, error=None, latest=None, follow_latest=False):
        now = _now()
        with self.conn:
            self.conn.execute("""UPDATE jobs SET state=?,updated_at=?,finished_at=?,last_error=?,
                result_json=? WHERE id=?""", (state, now, now, error,
                                             _json(result) if result is not None else None, job["id"]))
            self.conn.execute("""UPDATE attempts SET state=?,finished_at=?,error=?,result_json=?
                WHERE job_id=? AND number=?""", (state, now, error,
                                                _json(result) if result is not None else None,
                                                job["id"], job["attempts"]))
            self._event(state, job["id"], error=error)
            if follow_latest:
                self.conn.execute("""INSERT INTO followups VALUES (?,?,?)
                    ON CONFLICT(config_hash) DO UPDATE SET options_json=excluded.options_json,
                    after_source_key=excluded.after_source_key""",
                                  (job["config_hash"], _json(job["options"]), job["source_key"]))
            if latest is not None and _source_key(latest) != job["source_key"]:
                successor, _ = self._enqueue(latest, job["options"])
                if state == "superseded":
                    self.conn.execute("UPDATE jobs SET superseded_by=? WHERE id=?",
                                      (successor["id"], job["id"]))

    def resume_followups(self):
        """A completed old build can outlive a temporarily unmerged newer DAG."""
        waiting = self.conn.execute("SELECT * FROM followups").fetchall()
        if not waiting:
            return
        try:
            with dag_snapshot(self.data_dir) as (_, latest):
                pass
        except (OSError, ValueError, sqlite3.Error):
            return
        with self.conn:
            for row in waiting:
                if _source_key(latest) != row["after_source_key"]:
                    self._enqueue(latest, json.loads(row["options_json"]))
                self.conn.execute("DELETE FROM followups WHERE config_hash=?", (row["config_hash"],))

    def status(self, limit=20):
        if limit < 1:
            raise ValueError("limit must be positive")
        counts = dict(self.conn.execute("SELECT state,COUNT(*) FROM jobs GROUP BY state"))
        jobs = [self._job(row) for row in self.conn.execute(
            "SELECT * FROM jobs ORDER BY id DESC LIMIT ?", (limit,))]
        try:
            with dag_snapshot(self.data_dir) as (_, source):
                pass
            source_error = None
        except (OSError, ValueError, sqlite3.Error) as exc:
            source, source_error = None, str(exc)
        pointer = self.data_dir / "vector-index.json"
        vectors = {"status": "missing"}
        if pointer.exists():
            try:
                metadata = json.loads(pointer.read_text())
                matches = source is not None and metadata.get("source_manifest_hash") == source["content_hash"]
                files_ok = all(metadata.get(key) and (self.data_dir / metadata[key]).is_file()
                               for key in ("rows_file", "matrix_file"))
                vectors = {"status": ("ready" if matches else "stale") if files_ok else "incomplete",
                           "source_current": matches,
                           "source_manifest_hash": metadata.get("source_manifest_hash"),
                           "source_set_hash": metadata.get("source_set_hash"),
                           "built_at": metadata.get("built_at")}
            except (OSError, ValueError) as exc:
                vectors = {"status": "invalid", "error": str(exc)}
        active = False
        if self.lock_path.exists():
            with self.lock_path.open("a+") as lock:
                try:
                    fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
                except BlockingIOError:
                    active = True
                finally:
                    if not active:
                        fcntl.flock(lock, fcntl.LOCK_UN)
                lock.seek(0)
                try:
                    worker = json.load(lock)
                except (ValueError, OSError):
                    worker = {}
        else:
            worker = {}
        return {"schema_version": 1, "queue_db": str(self.path), "counts": counts, "jobs": jobs,
                "waiting_for_merged_dag": self.conn.execute("SELECT COUNT(*) FROM followups").fetchone()[0],
                "worker": {**worker, "active": active}, "dag_source": source,
                "dag_source_error": source_error, "vectors": vectors}


def start_worker(data_dir: Path, project_root: Path = ROOT, poll_seconds=1.0):
    logs = data_dir / "logs"
    logs.mkdir(parents=True, exist_ok=True)
    path = logs / "embedding-worker.log"
    with path.open("ab", buffering=0) as output:
        child = subprocess.Popen(
            [sys.executable, "-m", "tools.proof_atlas.embedding_queue", "work", "--data-dir", str(data_dir),
             "--project-root", str(project_root), "--poll-seconds", str(poll_seconds)],
            cwd=ROOT, stdin=subprocess.DEVNULL, stdout=output, stderr=subprocess.STDOUT,
            start_new_session=True, close_fds=True,
            env={**os.environ, "PYTHONUNBUFFERED": "1"})
    return {"pid": child.pid, "log": str(path), "detached": True}


def _make_client(options):
    from .embedding import QwenEmbeddingClient, TEIEmbeddingClient
    if options["embedding"] == "qwen":
        return QwenEmbeddingClient(model_dir=options["model_dir"], device=options["device"],
                                   worker_python=options["worker_python"], batch_size=options["batch_size"])
    return TEIEmbeddingClient(url=options["embedding_url"], model_dir=options["model_dir"])


def work(data_dir, *, project_root=ROOT, once=False, poll_seconds=1.0,
         client_factory: Callable = _make_client, after_claim: Callable | None = None):
    """One persistent model client and worker; queue SQL locks never span a build.

    The separate advisory *worker ownership* lock lasts for the process lifetime.
    It does not lock the queue database, DAG database, or GPU service.
    """
    if poll_seconds <= 0:
        raise ValueError("poll-seconds must be positive")
    from .vectors import VectorIndex
    processed, client, client_key = 0, None, None
    with EmbeddingQueue(data_dir, project_root) as queue, queue.lock_path.open("a+") as lock:
        try:
            fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
        except BlockingIOError:
            return {"status": "already_running", "processed": 0}
        lock.seek(0)
        lock.truncate()
        lock.write(_json({"pid": os.getpid(), "started_at": _now()}))
        lock.flush()
        queue.recover()
        try:
            while True:
                queue.resume_followups()
                job = queue.claim()
                if job is None:
                    if once:
                        return {"status": "idle", "processed": processed}
                    time.sleep(poll_seconds)
                    continue
                try:
                    if after_claim is not None:
                        after_claim(job)
                    with dag_snapshot(queue.data_dir) as (store, source):
                        if _source_key(source) != job["source_key"]:
                            queue.finish(job, "superseded", latest=source)
                        else:
                            options = job["options"]
                            key = _hash({k: options[k] for k in (
                                "embedding", "model_dir", "device", "worker_python", "embedding_url", "batch_size")})
                            if key != client_key or client is None:
                                if hasattr(client, "close"):
                                    client.close()
                                client, client_key = client_factory(options), key
                            result = VectorIndex(queue.data_dir).build(store, client, **{k: options[k] for k in (
                                "views", "batch_size", "include_internal", "chunk_tokens", "pending_buffer")})
                    if _source_key(source) == job["source_key"]:
                        try:
                            with dag_snapshot(queue.data_dir) as (_, latest):
                                pass
                            latest_error = None
                        except (OSError, ValueError, sqlite3.Error) as exc:
                            latest, latest_error = None, str(exc)
                        result = {**result, "read_source": source,
                                  "current_at_completion": latest is not None and
                                  _source_key(source) == _source_key(latest),
                                  "latest_source_error": latest_error}
                        queue.finish(job, "succeeded", result=result, latest=latest,
                                     follow_latest=latest is None)
                except Exception:
                    error = traceback.format_exc()
                    queue.finish(job, "failed", error=error)
                    print(error, file=sys.stderr, flush=True)
                    if hasattr(client, "close"):
                        client.close()
                    client, client_key = None, None
                processed += 1
                if once:
                    return {"status": "processed", "processed": processed}
        finally:
            if hasattr(client, "close"):
                client.close()


def parser():
    p = argparse.ArgumentParser(description=__doc__)
    commands = p.add_subparsers(dest="command", required=True)
    for name in ("submit", "status", "work"):
        cmd = commands.add_parser(name)
        cmd.add_argument("--data-dir", type=Path,
                         default=Path(os.getenv("PROOF_ATLAS_DATA", str(DEFAULT_DATA))))
        cmd.add_argument("--project-root", type=Path, default=ROOT)
        if name == "submit":
            cmd.add_argument("--embedding", choices=["qwen", "tei"], default="qwen")
            for option in ("model-dir", "embedding-url", "device", "worker-python"):
                cmd.add_argument("--" + option, default="auto" if option == "device" else None)
            cmd.add_argument("--views", nargs="+")
            cmd.add_argument("--batch-size", type=int, default=16)
            cmd.add_argument("--chunk-tokens", type=int, default=1024)
            cmd.add_argument("--pending-buffer", type=int, default=512)
            cmd.add_argument("--include-internal", action="store_true")
            cmd.add_argument("--retry", type=int, metavar="FAILED_JOB_ID")
            cmd.add_argument("--start", action="store_true")
        elif name == "status":
            cmd.add_argument("--limit", type=int, default=20)
        else:
            cmd.add_argument("--once", action="store_true")
            cmd.add_argument("--poll-seconds", type=float, default=1.0)
    return p


def main(argv=None):
    args = parser().parse_args(argv)
    try:
        if args.command == "work":
            result = work(args.data_dir, project_root=args.project_root,
                          once=args.once, poll_seconds=args.poll_seconds)
        else:
            with EmbeddingQueue(args.data_dir, args.project_root) as queue:
                if args.command == "status":
                    result = queue.status(args.limit)
                else:
                    options = {k: getattr(args, k) for k in (
                        "embedding", "model_dir", "embedding_url", "device", "worker_python", "views",
                        "batch_size", "chunk_tokens", "pending_buffer", "include_internal")}
                    result = queue.submit(options, retry_job=args.retry)
                    if args.start:
                        result["worker"] = start_worker(queue.data_dir, queue.project_root)
        print(json.dumps(result, ensure_ascii=False, indent=2))
        return 0
    except (ValueError, OSError, sqlite3.Error) as exc:
        print(f"proof-atlas embedding queue: {exc}", file=sys.stderr)
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
