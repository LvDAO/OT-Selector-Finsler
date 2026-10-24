"""Resumable semantic embeddings, with source-bound atomic index generations.

SQLite stores completed input embeddings and prepared chunks independently from
published NumPy matrices. An interrupted build preserves its completed batches
and leaves the previous complete generation available. Retrieval uses cosine
similarity of normalized embeddings without a lexical/semantic fusion score.
"""
from __future__ import annotations

from collections import deque
from concurrent.futures import Future, ThreadPoolExecutor
from datetime import datetime, timezone
import hashlib
import heapq
import json
import os
from pathlib import Path
import sqlite3
import sys
import time
from typing import Any, Iterable, Mapping
import uuid

import numpy as np

from .embedding import EmbeddingError, assert_fingerprint

DEFAULT_VIEWS = ("conditions", "objects", "proof_detail", "full_proof", "proof_state")
SUPPORTED_VIEWS = set(DEFAULT_VIEWS) | {"statement"}
CHUNK_SCHEMA = "proof-view-context-v1"
PREPARED_KEY_SCHEMA = "proof-view-content-v1"


class VectorIndexError(RuntimeError):
    """A vector generation is absent, corrupt or incompatible with its source."""


class StaleVectorIndex(VectorIndexError):
    """Rebuild vectors for the current set of source-bound proof views."""


def _json(value: Any) -> str:
    return json.dumps(value, ensure_ascii=False, sort_keys=True, separators=(",", ":"))


def _sha(value: str) -> str:
    return hashlib.sha256(value.encode("utf-8")).hexdigest()


def _source_identity(row: Mapping[str, Any]) -> dict[str, Any]:
    return {key: row.get(key) for key in (
        "id", "name", "view", "record_key", "content_hash", "module", "namespace",
        "source_path", "source_hash", "metadata", "kind", "private", "internal_detail",
    )}


def _rows(store: Any, views: Iterable[str], include_internal: bool, *, include_text: bool = True):
    selected = set(views)
    for row in store.iter_views(include_internal=include_internal, include_text=include_text):
        if row["view"] in selected:
            yield row


def _source_hasher(store: Any):
    status = store.snapshot_status()
    if status.get("stale") is True:
        raise StaleVectorIndex("Store declaration sources are stale; re-export/import them before vector indexing")
    manifest = status.get("manifest", {})
    hasher = hashlib.sha256()
    hasher.update(_json({key: manifest.get(key) for key in ("toolchain", "mathlib_revision")}).encode())
    return hasher, status


def _source_digest(store: Any, views: Iterable[str], include_internal: bool) -> str:
    hasher, _ = _source_hasher(store)
    for row in _rows(store, views, include_internal, include_text=False):
        hasher.update(_json(_source_identity(row)).encode("utf-8") + b"\n")
    return hasher.hexdigest()


def _context(row: Mapping[str, Any]) -> str:
    return "\n".join((
        "Declaration: " + str(row.get("name", "")),
        "Module: " + str(row.get("module", "")),
        "Namespace: " + str(row.get("namespace", "")),
        "Proof view: " + str(row["view"]),
    ))


def _prepared_document_hash(row: Mapping[str, Any], chunk_tokens: int) -> str:
    # Source IDs, ranges and file hashes remain bound to each published row, but
    # do not change the text sent to the tokenizer or embedding model.
    return _sha(_json({"context": _context(row), "content_hash": row["content_hash"],
                       "chunk_schema": CHUNK_SCHEMA, "chunk_tokens": chunk_tokens}))


def _legacy_document_hash(row: Mapping[str, Any], chunk_tokens: int) -> str:
    return _sha(_json({"source": _source_identity(row), "chunk_schema": CHUNK_SCHEMA,
                       "chunk_tokens": chunk_tokens}))


def _validated_matrix(values: Any, rows: int, dimension: int) -> np.ndarray:
    array = np.asarray(values, dtype=np.float32)
    if array.shape != (rows, dimension) or not np.isfinite(array).all():
        raise VectorIndexError("Embedding batch has invalid dimensions or non-finite values")
    norms = np.linalg.norm(array, axis=1)
    if np.any(np.abs(norms - 1) > 1e-3):
        raise VectorIndexError("Semantic indexing requires normalized nonzero embedding vectors")
    return array


class VectorIndex:
    def __init__(self, data_dir: str | Path):
        self.data_dir = Path(data_dir)
        self.pointer = self.data_dir / "vector-index.json"
        self.cache_path = self.data_dir / "vector-cache.sqlite3"

    def _cache(self) -> sqlite3.Connection:
        self.data_dir.mkdir(parents=True, exist_ok=True)
        connection = sqlite3.connect(self.cache_path, timeout=60)
        connection.execute("PRAGMA journal_mode=WAL")
        connection.execute("PRAGMA busy_timeout=60000")
        connection.executescript("""
            CREATE TABLE IF NOT EXISTS embedding_cache (
                model_hash TEXT NOT NULL, input_hash TEXT NOT NULL,
                dimension INTEGER NOT NULL, vector BLOB NOT NULL,
                PRIMARY KEY(model_hash,input_hash)) WITHOUT ROWID;
            CREATE TABLE IF NOT EXISTS prepared_views (
                model_hash TEXT NOT NULL, document_hash TEXT NOT NULL,
                chunks_json TEXT NOT NULL,
                PRIMARY KEY(model_hash,document_hash)) WITHOUT ROWID;
            CREATE TABLE IF NOT EXISTS prepared_view_aliases (
                model_hash TEXT NOT NULL, document_hash TEXT NOT NULL,
                prepared_hash TEXT NOT NULL,
                PRIMARY KEY(model_hash,document_hash)) WITHOUT ROWID;
            CREATE TABLE IF NOT EXISTS prepared_view_migrations (
                model_hash TEXT NOT NULL, migration_hash TEXT NOT NULL,
                PRIMARY KEY(model_hash,migration_hash)) WITHOUT ROWID;
        """)
        return connection

    def _migrate_legacy_prepared_views(self, connection: sqlite3.Connection,
                                      model_hash: str, chunk_tokens: int) -> None:
        """Recover content keys once from a checksum-verified old generation.

        Aliases point to existing prepared lists without copying their text or
        invoking the tokenizer/model. New generations already use content keys.
        """
        if not self.pointer.is_file():
            return
        try:
            metadata = self._metadata()
        except VectorIndexError:
            return  # A rebuild may repair an unreadable old generation.
        if (metadata.get("prepared_key_schema") == PREPARED_KEY_SCHEMA or
                metadata.get("model_hash") != model_hash or
                metadata.get("chunk_schema") != CHUNK_SCHEMA or
                metadata.get("chunk_tokens") != chunk_tokens):
            return
        rows_sha256 = metadata.get("rows_sha256")
        if not isinstance(rows_sha256, str):
            return
        migration_hash = _sha(_json({"rows_sha256": rows_sha256, "chunk_schema": CHUNK_SCHEMA,
                                    "chunk_tokens": chunk_tokens}))
        if connection.execute(
                "SELECT 1 FROM prepared_view_migrations WHERE model_hash=? AND migration_hash=?",
                (model_hash, migration_hash)).fetchone():
            return
        connection.execute("SAVEPOINT prepared_view_migration")
        try:
            hasher = hashlib.sha256()
            previous_id = object()
            with (self.data_dir / metadata["rows_file"]).open("rb") as source:
                for line in source:
                    hasher.update(line)
                    row = json.loads(line)
                    if row["document_id"] == previous_id:
                        continue
                    previous_id = row["document_id"]
                    connection.execute("""
                        INSERT OR IGNORE INTO prepared_view_aliases
                        SELECT model_hash,?,document_hash FROM prepared_views
                        WHERE model_hash=? AND document_hash=?
                    """, (_prepared_document_hash(row, chunk_tokens), model_hash,
                          _legacy_document_hash(row, chunk_tokens)))
            if hasher.hexdigest() != rows_sha256:
                raise ValueError("Old semantic row checksum changed")
            connection.execute("INSERT INTO prepared_view_migrations VALUES (?,?)",
                               (model_hash, migration_hash))
        except (OSError, ValueError, KeyError, TypeError):
            # Never use unverified provenance to alias prepared inputs. Current
            # source text can still be prepared normally to repair the index.
            connection.execute("ROLLBACK TO prepared_view_migration")
        except BaseException:
            connection.execute("ROLLBACK TO prepared_view_migration")
            raise
        finally:
            connection.execute("RELEASE prepared_view_migration")
        connection.commit()

    def _metadata(self) -> dict[str, Any]:
        if not self.pointer.is_file():
            raise VectorIndexError("Semantic index is missing; run the vector build command first")
        try:
            metadata = json.loads(self.pointer.read_text(encoding="utf-8"))
            if metadata["schema_version"] != 1:
                raise ValueError("unsupported vector schema")
            for key in ("matrix_file", "rows_file"):
                name = metadata[key]
                if not isinstance(name, str) or Path(name).name != name:
                    raise ValueError("invalid generation filename")
            return metadata
        except (OSError, ValueError, TypeError, KeyError) as exc:
            raise VectorIndexError("Semantic index metadata is unreadable or incompatible; rebuild it") from exc

    def status(self, store: Any = None) -> dict[str, Any]:
        if not self.pointer.exists():
            return {"status": "missing", "path": str(self.pointer), "cache_exists": self.cache_path.exists()}
        metadata = self._metadata()
        result = {"status": "ready", "path": str(self.pointer), **metadata}
        if not all((self.data_dir / metadata[key]).is_file() for key in ("matrix_file", "rows_file")):
            result["status"] = "incomplete"
        if store is not None:
            try:
                current = _source_digest(store, metadata["views"], metadata["include_internal"])
                result["source_set_current"] = current == metadata["source_set_hash"]
                if not result["source_set_current"]:
                    result["status"] = "stale"
            except StaleVectorIndex:
                result.update(status="stale", source_set_current=False)
        return result

    def build(self, store: Any, client: Any, views: Iterable[str] | None = None,
              batch_size: int = 16, include_internal: bool = False,
              chunk_tokens: int = 1024, pending_buffer: int = 512) -> dict[str, Any]:
        if batch_size < 1 or chunk_tokens < 1 or pending_buffer < 1:
            raise ValueError("Vector build batch size, buffer and chunk token budget must be positive")
        pending_buffer = max(batch_size, pending_buffer)
        if isinstance(views, str):
            views = [views]
        selected = tuple(sorted(set(DEFAULT_VIEWS if views is None else views)))
        if not selected or not set(selected) <= SUPPORTED_VIEWS:
            raise ValueError("Select one or more supported proof views: " + ", ".join(sorted(SUPPORTED_VIEWS)))
        fingerprint = dict(client.fingerprint)
        dimension = int(fingerprint["dimension"])
        if dimension < 1:
            raise ValueError("Embedding fingerprint must contain a positive dimension")
        model_hash = _sha(_json(fingerprint))
        started = time.monotonic()
        hasher, snapshot = _source_hasher(store)
        connection = self._cache()
        generation = uuid.uuid4().hex
        rows_name, matrix_name = f"vector-rows-{generation}.jsonl", f"vectors-{generation}.npy"
        rows_temp = self.data_dir / (rows_name + ".tmp")
        matrix_temp = self.data_dir / (matrix_name + ".tmp")
        pointer_temp = self.data_dir / ("vector-index-" + generation + ".tmp")
        pending: dict[str, tuple[str, int]] = {}
        # Only a client with independent CPU preparation may use its worker
        # from this thread. IPC-only tokenizers must keep the serial protocol.
        parallel = getattr(client, "supports_parallel_preparation", False) is True
        embed_prepared = getattr(client, "embed_prepared", None)
        parallel = parallel and callable(embed_prepared)
        executor = (ThreadPoolExecutor(max_workers=1, thread_name_prefix="proof-atlas-embedding")
                    if parallel else None)
        active: deque[tuple[list[str], Future[Any]]] = deque()
        active_keys: set[str] = set()
        documents = chunks_count = generated = reused = prepared = 0
        legacy_migration_checked = False
        last_progress = started
        rows_hasher = hashlib.sha256()

        def cache_batch(keys: list[str], values: Any) -> None:
            nonlocal generated
            vectors = _validated_matrix(values, len(keys), dimension)
            connection.executemany(
                "INSERT OR REPLACE INTO embedding_cache VALUES (?,?,?,?)",
                ((model_hash, key, dimension, vector.tobytes())
                 for key, vector in zip(keys, vectors)),
            )
            # SQLite and source iteration belong to the main thread. Every
            # completed batch is durable even if a later batch fails.
            connection.commit()
            generated += len(keys)

        def collect(*, wait: bool = False) -> None:
            failure = None
            while active and (wait or active[0][1].done()):
                keys, future = active[0]
                try:
                    cache_batch(keys, future.result())
                except Exception as exc:
                    if failure is None:
                        failure = exc
                # Leave a future queued if waiting was interrupted, so the
                # finalizer can still await and cache its completed result.
                active.popleft()
                active_keys.difference_update(keys)
            if failure is not None:
                raise failure

        def flush() -> None:
            if not pending:
                return
            # At most one buffer is submitted, while the main thread prepares
            # the next buffer. Wait before submitting another, bounding both
            # queued GPU work and prepared text without sharing a connection.
            if executor is not None:
                collect(wait=True)
            # Length grouping is a resource optimization only. Matrix rows keep
            # source order and are assembled by input hash after all batches.
            ordered = sorted(pending, key=lambda key: (pending[key][1], key))
            for start in range(0, len(ordered), batch_size):
                keys = ordered[start:start + batch_size]
                texts = [pending[key][0] for key in keys]
                if executor is None:
                    cache_batch(keys, client.embed_texts(texts, batch_size=batch_size))
                else:
                    counts = [pending[key][1] for key in keys]
                    future = executor.submit(embed_prepared, texts, counts, batch_size=batch_size)
                    active.append((keys, future))
                    active_keys.update(keys)
                for key in keys:
                    del pending[key]

        try:
            with rows_temp.open("w", encoding="utf-8") as output:
                for row in _rows(store, selected, include_internal):
                    documents += 1
                    identity = _source_identity(row)
                    hasher.update(_json(identity).encode("utf-8") + b"\n")
                    document_hash = _prepared_document_hash(row, chunk_tokens)
                    cached = connection.execute(
                        """SELECT chunks_json FROM prepared_views
                        WHERE model_hash=? AND document_hash=? UNION ALL
                        SELECT p.chunks_json FROM prepared_view_aliases a JOIN prepared_views p
                          ON p.model_hash=a.model_hash AND p.document_hash=a.prepared_hash
                        WHERE a.model_hash=? AND a.document_hash=? LIMIT 1""",
                        (model_hash, document_hash, model_hash, document_hash),
                    ).fetchone()
                    if cached is None:
                        # A matching old identity is a cheap migration path for
                        # unchanged source rows, including interrupted builds.
                        legacy_hash = _legacy_document_hash(row, chunk_tokens)
                        cached = connection.execute(
                            "SELECT chunks_json FROM prepared_views WHERE model_hash=? AND document_hash=?",
                            (model_hash, legacy_hash),
                        ).fetchone()
                        if cached is not None:
                            connection.execute("INSERT OR IGNORE INTO prepared_view_aliases VALUES (?,?,?)",
                                               (model_hash, document_hash, legacy_hash))
                    if cached is None and not legacy_migration_checked:
                        self._migrate_legacy_prepared_views(connection, model_hash, chunk_tokens)
                        legacy_migration_checked = True
                        cached = connection.execute("""
                            SELECT p.chunks_json FROM prepared_view_aliases a JOIN prepared_views p
                              ON p.model_hash=a.model_hash AND p.document_hash=a.prepared_hash
                            WHERE a.model_hash=? AND a.document_hash=?
                        """, (model_hash, document_hash)).fetchone()
                    if cached:
                        chunks = json.loads(cached[0])
                        prepared += 1
                    else:
                        chunks = [chunk.to_dict() for chunk in client.chunk_text(
                            row["text"], context=_context(row), max_tokens=chunk_tokens)]
                        connection.execute("INSERT OR REPLACE INTO prepared_views VALUES (?,?,?)",
                                           (model_hash, document_hash, _json(chunks)))
                    for chunk in chunks:
                        collect()
                        input_hash = _sha(chunk["text"])
                        found = connection.execute(
                            "SELECT dimension,length(vector) FROM embedding_cache WHERE model_hash=? AND input_hash=?",
                            (model_hash, input_hash),
                        ).fetchone()
                        if found:
                            if found != (dimension, dimension * 4):
                                raise VectorIndexError("Cached vector shape is corrupt; remove the affected cache and rebuild")
                            reused += 1
                        elif input_hash not in pending and input_hash not in active_keys:
                            pending[input_hash] = (chunk["text"], chunk["token_count"])
                        metadata = {
                            **identity, "document_id": row["id"], "declaration": row["name"],
                            "chunk_start": chunk["start"], "chunk_end": chunk["end"],
                            "parent_start": chunk["parent_start"], "parent_end": chunk["parent_end"],
                            "token_count": chunk["token_count"], "chunk_boundary": chunk["boundary"],
                            "embedding_input_hash": input_hash, "text": chunk["text"],
                        }
                        encoded = _json(metadata) + "\n"
                        output.write(encoded)
                        rows_hasher.update(encoded.encode("utf-8"))
                        chunks_count += 1
                        if len(pending) >= pending_buffer:
                            flush()
                    now = time.monotonic()
                    if documents % 100 == 0 or now - last_progress >= 10:
                        # Complete, content-keyed chunk lists remain resumable
                        # even when too few new inputs trigger an embedding batch.
                        connection.commit()
                        print(f"proof-atlas vectors: {documents} views, {chunks_count} chunks, "
                              f"{generated} new embeddings, {reused} cached; "
                              f"{now - started:.1f}s", file=sys.stderr, flush=True)
                        last_progress = now
                flush()
                collect(wait=True)
                connection.commit()
                output.flush()
                os.fsync(output.fileno())
            source_hash = hasher.hexdigest()
            if source_hash != _source_digest(store, selected, include_internal):
                raise StaleVectorIndex("Proof views changed during vector build; rerun to reuse completed batches")
            # Construct the matrix once, after all durable embedding batches exist.
            matrix = np.lib.format.open_memmap(matrix_temp, mode="w+", dtype=np.float32,
                                               shape=(chunks_count, dimension))
            with rows_temp.open(encoding="utf-8") as source:
                for index, line in enumerate(source):
                    record = json.loads(line)
                    found = connection.execute(
                        "SELECT vector FROM embedding_cache WHERE model_hash=? AND input_hash=?",
                        (model_hash, record["embedding_input_hash"]),
                    ).fetchone()
                    if found is None:
                        raise VectorIndexError("A prepared chunk lacks its durable embedding; rerun the build")
                    value = np.frombuffer(found[0], dtype=np.float32)
                    _validated_matrix(value.reshape(1, -1), 1, dimension)
                    matrix[index] = value
            matrix.flush()
            del matrix
            with matrix_temp.open("rb") as source:
                os.fsync(source.fileno())
            metadata = {
                "schema_version": 1, "embedding_fingerprint": fingerprint, "model_hash": model_hash,
                "dimension": dimension, "documents": documents, "chunks": chunks_count,
                "views": list(selected), "include_internal": include_internal,
                "source_set_hash": source_hash, "source_manifest_hash": snapshot.get("content_hash"),
                "source_bound": bool(snapshot.get("source_bound")), "chunk_schema": CHUNK_SCHEMA,
                "prepared_key_schema": PREPARED_KEY_SCHEMA,
                "chunk_tokens": chunk_tokens, "pending_buffer": pending_buffer,
                "embedding_batch_size": batch_size, "rows_sha256": rows_hasher.hexdigest(),
                "parallel_preparation": parallel,
                "rows_file": rows_name, "matrix_file": matrix_name,
                "built_at": datetime.now(timezone.utc).isoformat(),
            }
            os.replace(rows_temp, self.data_dir / rows_name)
            os.replace(matrix_temp, self.data_dir / matrix_name)
            with pointer_temp.open("w", encoding="utf-8") as output:
                output.write(_json(metadata) + "\n")
                output.flush()
                os.fsync(output.fileno())
            os.replace(pointer_temp, self.pointer)
            return {**metadata, "status": "ready", "new_embeddings": generated,
                    "cached_embeddings": reused, "prepared_documents_reused": prepared,
                    "seconds": round(time.monotonic() - started, 3), "path": str(self.pointer)}
        finally:
            # A source/preparation failure may leave submitted batches running.
            # Save their successful results before releasing resources, retaining
            # the original exception when cleanup also encounters a failed batch.
            failure_in_progress = sys.exc_info()[0] is not None
            try:
                if executor is not None:
                    try:
                        collect(wait=True)
                    except BaseException:
                        if not failure_in_progress:
                            raise
                    finally:
                        executor.shutdown(wait=True)
            finally:
                connection.close()
                for temporary in (rows_temp, matrix_temp, pointer_temp):
                    temporary.unlink(missing_ok=True)

    def search(self, query: str, client: Any, store: Any, limit: int = 10,
               view: str | None = None, module: str | None = None,
               namespace: str | None = None) -> list[dict[str, Any]]:
        if not query.strip():
            raise ValueError("Semantic query must contain text")
        if limit < 1:
            return []
        metadata = self._metadata()
        assert_fingerprint(metadata["embedding_fingerprint"], client.fingerprint)
        if _source_digest(store, metadata["views"], metadata["include_internal"]) != metadata["source_set_hash"]:
            raise StaleVectorIndex("Indexed proof views changed; rebuild vectors to reuse unchanged cached embeddings")
        try:
            matrix = np.load(self.data_dir / metadata["matrix_file"], mmap_mode="r", allow_pickle=False)
            if matrix.shape != (metadata["chunks"], metadata["dimension"]) or matrix.dtype != np.float32:
                raise VectorIndexError("Semantic vector matrix shape or dtype does not match its metadata")
            query_vector = _validated_matrix(client.embed_texts([query]), 1, metadata["dimension"])[0]
            scores = matrix @ query_vector
            if not np.isfinite(scores).all():
                raise VectorIndexError("Semantic vector matrix contains non-finite coordinates")
            eligible = []
            rows_hasher = hashlib.sha256()
            with (self.data_dir / metadata["rows_file"]).open(encoding="utf-8") as source:
                count = 0
                for index, line in enumerate(source):
                    count += 1
                    rows_hasher.update(line.encode("utf-8"))
                    row = json.loads(line)
                    if view is not None and row["view"] != view:
                        continue
                    if module is not None and row["module"] != module:
                        continue
                    ns = row.get("namespace") or ""
                    if namespace is not None and ns != namespace and not ns.startswith(namespace + "."):
                        continue
                    score = float(scores[index])
                    candidate = (score, -index, row)
                    if len(eligible) < limit:
                        heapq.heappush(eligible, candidate)
                    elif candidate[:2] > eligible[0][:2]:
                        heapq.heapreplace(eligible, candidate)
                if count != metadata["chunks"]:
                    raise VectorIndexError("Semantic row metadata count does not match the vector matrix")
                if rows_hasher.hexdigest() != metadata["rows_sha256"]:
                    raise VectorIndexError("Semantic row metadata checksum changed; rebuild vectors")
            # Exact cosine ordering, with generation row order breaking equal ties.
            eligible.sort(key=lambda item: (-item[0], -item[1]))
            return [{**row, "cosine_similarity": max(-1.0, min(1.0, score))}
                    for score, _, row in eligible]
        except (OSError, ValueError, KeyError, IndexError) as exc:
            if isinstance(exc, VectorIndexError):
                raise
            raise VectorIndexError("Semantic generation is unreadable or corrupt; rebuild vectors") from exc
