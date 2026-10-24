"""Durable queue and real SQLite WAL snapshots, without model or GPU access."""
import contextlib
import fcntl
import io
import json
from pathlib import Path
import sqlite3
import tempfile
import unittest
from unittest.mock import patch

import numpy as np

from tools.proof_atlas import embedding_queue as queue_module
from tools.proof_atlas.embedding import EmbeddingChunk
from tools.proof_atlas.embedding_queue import EmbeddingQueue, dag_snapshot, work
from tools.proof_atlas.store import Store


class Client:
    fingerprint = {"model_revision": "queue-test", "dimension": 2, "normalize": True}

    def __init__(self, fail_after=None, callback=None):
        self.calls = []
        self.fail_after = fail_after
        self.callback = callback
        self.closed = False

    def chunk_text(self, text, context="", max_tokens=None):
        return [EmbeddingChunk(context + "\n\n" + text, 0, len(text), 0, len(text), len(text))]

    def embed_texts(self, texts, batch_size=16):
        if self.fail_after is not None and len(self.calls) >= self.fail_after:
            raise RuntimeError("fake inference interrupted")
        self.calls.append(list(texts))
        if self.callback:
            self.callback(self)
        return np.asarray([[1., 0.] for _ in texts], dtype=np.float32)

    def close(self):
        self.closed = True


class EmbeddingQueueTests(unittest.TestCase):
    def setUp(self):
        temporary = tempfile.TemporaryDirectory()
        self.addCleanup(temporary.cleanup)
        self.root = Path(temporary.name)
        self.data = self.root / "data"
        self.data.mkdir()
        self.options = {"views": ["objects"], "batch_size": 1, "pending_buffer": 1}
        self.ingest("one")

    def ingest(self, version):
        records = []
        for name, text in (("Demo.alpha", "stable alpha"), ("Demo.beta", "beta " + version)):
            records.extend([
                {"record_type": "declaration", "name": name, "module": "Demo.Core",
                 "kind": "theorem", "type_text": "Nat", "proof_dependencies": []},
                {"record_type": "triad", "declaration": name, "ordered_telescope": [],
                 "target_text": text, "proof_skeleton": {"expression_text": "proof " + text}},
            ])
        export = self.root / (version + ".jsonl")
        export.write_text("".join(json.dumps(row) + "\n" for row in records))
        manifest = {"content_hash": "source-" + version,
                    "sources": {"Demo/Core.lean": "hash-" + version},
                    "toolchain": "lean-test", "mathlib_revision": "mathlib-test"}
        with Store(self.data / "atlas.sqlite3") as store:
            store.import_jsonl(export, manifest)

    def submit(self, options=None, **kwargs):
        with EmbeddingQueue(self.data) as queue:
            return queue.submit(self.options if options is None else options, **kwargs)

    def jobs(self):
        with EmbeddingQueue(self.data) as queue:
            return queue.status()["jobs"]

    def run_once(self, client=None, **kwargs):
        client = client or Client()
        with contextlib.redirect_stderr(io.StringIO()):
            return work(self.data, once=True, client_factory=lambda _: client, **kwargs)

    def test_submit_is_model_free_deduplicates_and_coalesces_pending_snapshots(self):
        with patch.object(queue_module, "_make_client", side_effect=AssertionError("loaded model")):
            first = self.submit()
            duplicate = self.submit({**self.options, "views": ["objects", "objects"]})
        self.assertTrue(duplicate["deduplicated"])
        self.assertEqual(first["job"]["id"], duplicate["job"]["id"])
        self.ingest("two")
        latest = self.submit()
        changed_config = self.submit({**self.options, "chunk_tokens": 512})
        with EmbeddingQueue(self.data) as queue:
            self.assertEqual(queue.job(first["job"]["id"])["state"], "superseded")
            self.assertEqual(queue.job(first["job"]["id"])["superseded_by"], latest["job"]["id"])
            self.assertEqual(queue.job(latest["job"]["id"])["state"], "queued")
            self.assertNotEqual(latest["job"]["config_hash"], changed_config["job"]["config_hash"])
            self.assertFalse(queue.status()["worker"]["active"])

    def test_claimed_older_snapshot_is_superseded_without_loading_client(self):
        old = self.submit()["job"]
        work(self.data, once=True, client_factory=lambda _: self.fail("loaded superseded source"),
             after_claim=lambda _: self.ingest("two"))
        with EmbeddingQueue(self.data) as queue:
            self.assertEqual(queue.job(old["id"])["state"], "superseded")
            pending = [job for job in queue.status()["jobs"] if job["state"] == "queued"]
        self.assertEqual([job["source"]["content_hash"] for job in pending], ["source-two"])
        self.assertFalse((self.data / "vector-index.json").exists())

    def test_worker_lock_is_exclusive_but_submit_is_not_blocked(self):
        self.submit()
        with (self.data / "embedding-worker.lock").open("a+") as lock:
            fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
            with EmbeddingQueue(self.data) as queue:
                self.assertTrue(queue.status()["worker"]["active"])
            with patch.object(queue_module, "_make_client", side_effect=AssertionError("loaded model")):
                result = self.run_once()
            self.assertEqual(result["status"], "already_running")
            self.assertTrue(self.submit()["deduplicated"])
        self.assertEqual(self.jobs()[0]["state"], "queued")

    def test_restart_recovers_interrupted_running_attempt(self):
        job = self.submit()["job"]
        def crash(_):
            raise SystemExit("simulated worker crash")
        with self.assertRaises(SystemExit):
            work(self.data, once=True, client_factory=crash)
        with EmbeddingQueue(self.data) as queue:
            self.assertEqual(queue.job(job["id"])["state"], "running")
        self.run_once()
        with EmbeddingQueue(self.data) as queue:
            recovered = queue.job(job["id"])
            attempts = list(queue.conn.execute("SELECT state FROM attempts ORDER BY id"))
        self.assertEqual(recovered["state"], "succeeded")
        self.assertEqual(recovered["attempts"], 2)
        self.assertEqual([row[0] for row in attempts], ["interrupted", "succeeded"])

    def test_failure_is_persistent_and_explicit_retry_reuses_vector_cache(self):
        job = self.submit()["job"]
        failed_client = Client(fail_after=1)
        self.run_once(failed_client)
        with EmbeddingQueue(self.data) as queue:
            self.assertEqual(queue.job(job["id"])["state"], "failed")
            self.assertIn("fake inference interrupted", queue.job(job["id"])["last_error"])
            self.assertEqual(queue.submit(self.options)["job"]["state"], "failed")
            self.assertEqual(queue.submit(retry_job=job["id"])["job"]["state"], "queued")
        resumed = Client()
        self.run_once(resumed)
        with EmbeddingQueue(self.data) as queue:
            finished = queue.job(job["id"])
        self.assertEqual(finished["state"], "succeeded")
        self.assertGreaterEqual(finished["result"]["cached_embeddings"], 1)
        self.assertLess(len(resumed.calls), finished["result"]["chunks"])
        self.assertTrue(failed_client.closed)

    def test_snapshot_is_read_only_and_other_connection_can_commit(self):
        with dag_snapshot(self.data) as (store, source):
            self.assertTrue(store.conn.in_transaction)
            before = list(store.iter_views())
            with self.assertRaises(sqlite3.OperationalError):
                store.conn.execute("DELETE FROM documents")
            self.ingest("two")
            self.assertEqual(list(store.iter_views()), before)
            self.assertEqual(store.snapshot_status()["content_hash"], source["content_hash"])
        with dag_snapshot(self.data) as (_, latest):
            self.assertEqual(latest["content_hash"], "source-two")

    def test_running_snapshot_publishes_old_binding_and_enqueues_latest(self):
        job = self.submit()["job"]
        def import_while_embedding(client):
            if len(client.calls) == 1:
                self.ingest("two")
                submitted = self.submit()
                self.assertEqual(submitted["job"]["state"], "queued")
                with EmbeddingQueue(self.data) as queue:
                    self.assertEqual(queue.job(job["id"])["state"], "running")
        self.run_once(Client(callback=import_while_embedding))
        with EmbeddingQueue(self.data) as queue:
            old = queue.job(job["id"])
            status = queue.status()
        self.assertEqual(old["state"], "succeeded")
        self.assertEqual(old["result"]["source_manifest_hash"], "source-one")
        self.assertFalse(old["result"]["current_at_completion"])
        self.assertEqual(status["vectors"]["status"], "stale")
        pending = [job for job in status["jobs"] if job["state"] == "queued"]
        self.assertEqual(len(pending), 1)
        self.assertEqual(pending[0]["source"]["content_hash"], "source-two")
        self.run_once()
        with EmbeddingQueue(self.data) as queue:
            self.assertEqual(queue.status()["vectors"]["status"], "ready")

    def test_one_persistent_client_is_reused_across_successive_snapshots(self):
        self.submit()
        def enqueue_latest(client):
            if len(client.calls) == 1:
                self.ingest("two")
                self.submit()
        client = Client(callback=enqueue_latest)
        factory_calls = []
        def factory(options):
            factory_calls.append(options)
            return client
        # Stop at the idle wait only after both genuinely queued builds finish.
        with patch.object(queue_module.time, "sleep", side_effect=KeyboardInterrupt), \
                contextlib.redirect_stderr(io.StringIO()), self.assertRaises(KeyboardInterrupt):
            work(self.data, client_factory=factory)
        self.assertEqual(len(factory_calls), 1)
        self.assertEqual({job["state"] for job in self.jobs()}, {"succeeded"})
        self.assertTrue(client.closed)

    def test_publication_during_partial_merge_remains_successful_and_follows_later(self):
        job = self.submit()["job"]
        def start_incomplete_merge(client):
            if len(client.calls) == 1:
                with Store(self.data / "atlas.sqlite3") as store, store.conn:
                    store.conn.execute("UPDATE declarations SET source_hash='unmerged'")
        self.run_once(Client(callback=start_incomplete_merge))
        with EmbeddingQueue(self.data) as queue:
            finished = queue.job(job["id"])
            status = queue.status()
        self.assertEqual(finished["state"], "succeeded")
        self.assertFalse(finished["result"]["current_at_completion"])
        self.assertEqual(status["waiting_for_merged_dag"], 1)
        self.assertEqual(status["vectors"]["status"], "stale")
        self.ingest("two")
        self.run_once()
        with EmbeddingQueue(self.data) as queue:
            self.assertEqual(queue.status()["waiting_for_merged_dag"], 0)
            self.assertEqual(queue.status()["vectors"]["status"], "ready")

    def test_retry_after_source_advanced_queues_latest_and_keeps_failed_history(self):
        failed = self.submit()["job"]
        self.run_once(Client(fail_after=0))
        self.ingest("two")
        with EmbeddingQueue(self.data) as queue:
            latest = queue.submit(retry_job=failed["id"])
            self.assertEqual(queue.job(failed["id"])["state"], "failed")
        self.assertEqual(latest["job"]["source"]["content_hash"], "source-two")
        self.assertNotEqual(latest["job"]["id"], failed["id"])

    def test_detached_start_and_cli_do_not_wait_for_inference(self):
        with patch.object(queue_module.subprocess, "Popen") as popen:
            popen.return_value.pid = 12345
            output = io.StringIO()
            with contextlib.redirect_stdout(output):
                code = queue_module.main(["submit", "--data-dir", str(self.data), "--start"])
        self.assertEqual(code, 0)
        result = json.loads(output.getvalue())
        self.assertEqual(result["worker"]["pid"], 12345)
        self.assertTrue(popen.call_args.kwargs["start_new_session"])
        self.assertTrue(popen.call_args.kwargs["close_fds"])
        self.assertIn("work", popen.call_args.args[0])
        self.assertEqual(result["job"]["state"], "queued")

    def test_rejects_incomplete_dag_and_repository_data_directory(self):
        with Store(self.data / "atlas.sqlite3") as store, store.conn:
            store.conn.execute("UPDATE declarations SET source_hash='unmerged'")
        with self.assertRaisesRegex(ValueError, "incompletely merged"):
            self.submit()
        with self.assertRaisesRegex(ValueError, "outside the repository"):
            EmbeddingQueue(queue_module.ROOT / "generated-queue")


if __name__ == "__main__":
    unittest.main()
