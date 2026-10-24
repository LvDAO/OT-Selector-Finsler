"""Durable resume, source binding and semantic retrieval contracts."""
import copy
import hashlib
import json
from pathlib import Path
import sqlite3
import tempfile
import threading
import unittest
from unittest.mock import patch

import numpy as np

from tools.proof_atlas.embedding import EmbeddingChunk, EmbeddingModelMismatch
from tools.proof_atlas.vectors import (StaleVectorIndex, VectorIndex, VectorIndexError,
                                       _legacy_document_hash, _source_digest)
from tools.proof_atlas.store import Store


def row(index, text, view="objects", namespace="Demo", module="Demo.Core", private=False):
    return {"id": index, "name": f"{namespace}.lemma{index}", "view": view,
            "record_key": "", "text": text,
            "content_hash": hashlib.sha256(text.encode()).hexdigest(),
            "module": module, "namespace": namespace, "source_path": "Demo/Core.lean",
            "source_hash": "source-1", "metadata": {}, "kind": "theorem",
            "private": int(private), "internal_detail": 0}


class SourceStore:
    def __init__(self, rows):
        self.rows = rows
        self.snapshot = "snapshot-1"

    def iter_views(self, include_internal=False, *, include_text=True):
        for item in self.rows:
            if include_internal or not item["private"]:
                result = copy.deepcopy(item)
                if not include_text:
                    result.pop("text")
                yield result

    def snapshot_status(self):
        return {"stale": None, "source_bound": True, "content_hash": self.snapshot,
                "manifest": {"toolchain": "lean-test", "mathlib_revision": "mathlib-test"}}


class Client:
    def __init__(self, revision="one", fail_after=None):
        self.fingerprint = {"model_revision": revision, "dimension": 2, "normalize": True}
        self.calls = []
        self.fail_after = fail_after

    def chunk_text(self, text, context="", max_tokens=None):
        return [EmbeddingChunk(context + "\n\n" + text[start:start + 40], start,
                               min(start + 40, len(text)), 0, len(text),
                               len(text[start:start + 40]), "character")
                for start in range(0, len(text), 40)]

    def embed_texts(self, texts, batch_size=16):
        if self.fail_after is not None and len(self.calls) >= self.fail_after:
            raise RuntimeError("interrupted inference")
        self.calls.append(list(texts))
        return np.asarray([[1., 0.] if "alpha" in text else [0., 1.] for text in texts], dtype=np.float32)


class ParallelClient(Client):
    supports_parallel_preparation = True

    def __init__(self, **kwargs):
        super().__init__(**kwargs)
        self.embedding_threads = set()
        self.preparation_threads = set()
        self.prepared_counts = []

    def chunk_text(self, *args, **kwargs):
        self.preparation_threads.add(threading.get_ident())
        return super().chunk_text(*args, **kwargs)

    def embed_prepared(self, texts, token_counts, batch_size=16):
        self.embedding_threads.add(threading.get_ident())
        self.prepared_counts.extend(token_counts)
        return super().embed_texts(texts, batch_size=batch_size)

    def embed_texts(self, *args, **kwargs):
        raise AssertionError("Parallel build must use previously counted inputs")


class VectorIndexTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.index = VectorIndex(Path(self.temp.name))
        self.store = SourceStore([row(1, "alpha"), row(2, "beta", "conditions")])

    def test_actual_store_rows_bind_sources_and_produce_semantic_views(self):
        root = Path(self.temp.name)
        export = root / "source.jsonl"
        records = [
            {"record_type": "declaration", "name": "Demo.alpha", "module": "Demo.Core",
             "kind": "theorem", "range": {"start": {"line": 1}, "end": {"line": 3}}},
            {"record_type": "triad", "declaration": "Demo.alpha", "ordered_telescope": [],
             "target_text": "alpha", "proof_skeleton": {"expression_text": "alpha_proof"}},
        ]
        export.write_text("".join(json.dumps(record) + "\n" for record in records))
        with Store(root / "source.sqlite3") as store:
            store.import_jsonl(export, {"sources": {"Demo/Core.lean": "source-1"},
                                       "toolchain": "lean-test", "mathlib_revision": "mathlib-test"})
            built = self.index.build(store, Client())
            self.assertGreaterEqual(built["documents"], 3)
            found = self.index.search("alpha", Client(), store)
            self.assertEqual({item["name"] for item in found}, {"Demo.alpha"})
            self.assertTrue(all(item["source_hash"] == "source-1" for item in found))

    def test_source_digest_matches_full_views_without_reading_proof_text(self):
        root = Path(self.temp.name)
        export = root / "source.jsonl"
        records = []
        for name, private in (("Demo.z", False), ("Demo.a", False), ("Demo.hidden", True)):
            records.extend((
                {"record_type": "declaration", "name": name, "module": "Demo.Core",
                 "kind": "theorem", "private": private},
                {"record_type": "triad", "declaration": name, "ordered_telescope": [],
                 "target_text": "alpha", "proof_skeleton": {"expression_text": "alpha proof " * 10000}},
            ))
        export.write_text("".join(json.dumps(record) + "\n" for record in records))
        with Store(root / "source.sqlite3") as store:
            store.import_jsonl(export, {"sources": {"Demo/Core.lean": "source-1"},
                                       "toolchain": "lean-test", "mathlib_revision": "mathlib-test"})
            original_views = store.iter_views

            def full_views(*args, **kwargs):
                kwargs["include_text"] = True
                return original_views(*args, **kwargs)

            combinations = [(views, internal) for views in
                            (("objects", "full_proof"), ("conditions",), ("proof_state",))
                            for internal in (False, True)]
            with patch.object(store, "iter_views", side_effect=full_views):
                expected = [_source_digest(store, views, internal) for views, internal in combinations]

            def deny_proof_text(action, table, column, database, trigger):
                if action == sqlite3.SQLITE_READ and table == "documents" and column == "text":
                    return sqlite3.SQLITE_DENY
                return sqlite3.SQLITE_OK

            store.conn.set_authorizer(deny_proof_text)
            try:
                actual = [_source_digest(store, views, internal) for views, internal in combinations]
            finally:
                store.conn.set_authorizer(None)
            self.assertEqual(actual, expected)

    def test_complete_index_reopens_and_uses_cosine_with_view_filters(self):
        built = self.index.build(self.store, Client(), batch_size=1)
        self.assertEqual((built["documents"], built["chunks"], built["new_embeddings"]), (2, 2, 2))
        reopened = VectorIndex(self.temp.name)
        found = reopened.search("alpha", Client(), self.store)
        self.assertEqual(found[0]["name"], "Demo.lemma1")
        self.assertAlmostEqual(found[0]["cosine_similarity"], 1.)
        filtered = reopened.search("alpha", Client(), self.store, view="conditions")
        self.assertEqual([item["name"] for item in filtered], ["Demo.lemma2"])
        self.assertTrue(reopened.status(self.store)["source_set_current"])

    def test_interruption_reuses_completed_batches_without_publishing_partial_index(self):
        self.store.rows = [row(i, f"alpha {i}") for i in range(6)]
        with self.assertRaisesRegex(RuntimeError, "interrupted inference"):
            self.index.build(self.store, Client(fail_after=1), batch_size=2)
        self.assertEqual(self.index.status()["status"], "missing")
        rebuilt = self.index.build(self.store, Client(), batch_size=2)
        self.assertEqual(rebuilt["new_embeddings"], 4)
        self.assertEqual(rebuilt["cached_embeddings"], 2)
        self.assertGreaterEqual(rebuilt["prepared_documents_reused"], 2)
        self.assertEqual(rebuilt["chunks"], 6)

    def test_progress_preserves_complete_preparation_before_any_embedding_batch(self):
        self.index.build(self.store, Client())
        previous = self.index.pointer.read_bytes()
        self.store.rows = [row(3, "alpha prepared"), row(4, "incomplete view")]

        class InterruptedPreparation(Client):
            def chunk_text(inner, text, **kwargs):
                for chunk in super().chunk_text(text, **kwargs):
                    yield chunk
                    if text == "incomplete view":
                        raise RuntimeError("interrupted preparation")

        client = InterruptedPreparation()
        with patch("tools.proof_atlas.vectors.time.monotonic", side_effect=[0., 11.]):
            with self.assertRaisesRegex(RuntimeError, "interrupted preparation"):
                self.index.build(self.store, client, pending_buffer=512)
        self.assertEqual(client.calls, [])
        self.assertEqual(self.index.pointer.read_bytes(), previous)
        with sqlite3.connect(self.index.cache_path) as connection:
            prepared = connection.execute("SELECT chunks_json FROM prepared_views").fetchall()
        self.assertEqual(len(prepared), 3)  # Two previous views and the completed new view.
        self.assertFalse(any("incomplete view" in chunks for (chunks,) in prepared))
        rebuilt = self.index.build(self.store, Client(), pending_buffer=512)
        self.assertEqual(rebuilt["prepared_documents_reused"], 1)
        self.assertEqual((rebuilt["documents"], rebuilt["new_embeddings"]), (2, 2))
        self.assertEqual(rebuilt["status"], "ready")

    def test_changed_source_invalidates_search_then_reuses_unchanged_inputs(self):
        self.index.build(self.store, Client())
        self.store.rows[0] = row(1, "alpha changed")
        with self.assertRaises(StaleVectorIndex):
            self.index.search("alpha", Client(), self.store)
        self.assertEqual(self.index.status(self.store)["status"], "stale")
        rebuilt = self.index.build(self.store, Client())
        self.assertEqual((rebuilt["new_embeddings"], rebuilt["cached_embeddings"]), (1, 1))
        self.assertIn("changed", self.index.search("alpha", Client(), self.store)[0]["text"])

    def test_metadata_only_changes_reuse_preparation_and_vectors_with_fresh_bindings(self):
        self.index.build(self.store, Client())
        for item in self.store.rows:
            item.update(id=item["id"] + 100, source_hash="source-2", source_path="Moved/Core.lean",
                        record_key="new-record", metadata={"range": {"line": 100}})
        self.store.snapshot = "snapshot-2"
        with self.assertRaises(StaleVectorIndex):
            self.index.search("alpha", Client(), self.store)
        client = Client()
        with patch.object(client, "chunk_text", side_effect=AssertionError("Unchanged text was chunked")):
            built = self.index.build(self.store, client)
        self.assertEqual((built["prepared_documents_reused"], built["new_embeddings"]), (2, 0))
        self.assertEqual(client.calls, [])
        self.assertEqual(built["source_manifest_hash"], "snapshot-2")
        found = self.index.search("alpha", Client(), self.store)
        self.assertEqual({item["document_id"] for item in found}, {101, 102})
        self.assertTrue(all(item["source_hash"] == "source-2" and
                            item["metadata"] == {"range": {"line": 100}} for item in found))
        self.assertTrue(self.index.status(self.store)["source_set_current"])

    def test_changed_parent_embeds_only_changed_chunk_and_preserves_other_chunks(self):
        text = "alpha" + "x" * 35 + "b" * 40 + "c" * 40
        self.store.rows = [row(1, text, "full_proof")]
        before = self.index.build(self.store, Client())
        old_rows = [json.loads(line) for line in
                    (self.index.data_dir / before["rows_file"]).read_text().splitlines()]
        self.store.rows = [row(1, text[:40] + "y" * 40 + text[80:], "full_proof")]
        client = Client()
        with patch.object(client, "chunk_text", wraps=client.chunk_text) as prepare:
            rebuilt = self.index.build(self.store, client)
        self.assertEqual(prepare.call_count, 1)
        self.assertEqual((rebuilt["chunks"], rebuilt["new_embeddings"], rebuilt["cached_embeddings"]),
                         (3, 1, 2))
        self.assertEqual(sum(len(call) for call in client.calls), 1)
        new_rows = [json.loads(line) for line in
                    (self.index.data_dir / rebuilt["rows_file"]).read_text().splitlines()]
        self.assertEqual(len({item["embedding_input_hash"] for item in old_rows} &
                             {item["embedding_input_hash"] for item in new_rows}), 2)
        self.assertTrue(all(item["content_hash"] == self.store.rows[0]["content_hash"]
                            for item in new_rows))

    def test_deleted_document_disappears_while_retained_vectors_are_reused(self):
        self.index.build(self.store, Client())
        self.store.rows.pop(0)
        client = Client()
        with patch.object(client, "chunk_text", side_effect=AssertionError("Retained text was chunked")):
            rebuilt = self.index.build(self.store, client)
        self.assertEqual((rebuilt["chunks"], rebuilt["new_embeddings"], rebuilt["cached_embeddings"]),
                         (1, 0, 1))
        self.assertEqual(client.calls, [])
        self.assertEqual([item["document_id"] for item in self.index.search("alpha", Client(), self.store)], [2])

    def test_context_change_prepares_and_embeds_new_model_input(self):
        self.index.build(self.store, Client())
        self.store.rows[0]["namespace"] = "Moved"
        client = Client()
        with patch.object(client, "chunk_text", wraps=client.chunk_text) as prepare:
            rebuilt = self.index.build(self.store, client)
        self.assertEqual(prepare.call_count, 1)
        self.assertEqual((rebuilt["prepared_documents_reused"], rebuilt["new_embeddings"]), (1, 1))
        self.assertIn("Namespace: Moved", client.calls[0][0])

    def _legacy_index(self):
        with patch("tools.proof_atlas.vectors._prepared_document_hash", side_effect=_legacy_document_hash):
            built = self.index.build(self.store, Client())
        metadata = json.loads(self.index.pointer.read_text())
        metadata.pop("prepared_key_schema")
        self.index.pointer.write_text(json.dumps(metadata))
        return built

    def test_legacy_cache_migrates_changed_metadata_without_tokenizing_or_copying_chunks(self):
        self._legacy_index()
        for item in self.store.rows:
            item.update(id=item["id"] + 100, source_hash="source-2")
        client = Client()
        with patch.object(client, "chunk_text", side_effect=AssertionError("Legacy text was chunked")):
            rebuilt = self.index.build(self.store, client)
        self.assertEqual((rebuilt["prepared_documents_reused"], rebuilt["new_embeddings"]), (2, 0))
        self.assertEqual(client.calls, [])
        with sqlite3.connect(self.index.cache_path) as connection:
            self.assertEqual(connection.execute("SELECT COUNT(*) FROM prepared_views").fetchone()[0], 2)
            self.assertEqual(connection.execute("SELECT COUNT(*) FROM prepared_view_aliases").fetchone()[0], 2)
            self.assertEqual(connection.execute("SELECT COUNT(*) FROM prepared_view_migrations").fetchone()[0], 1)
        # Future changes bind current metadata without revisiting the old rows.
        self.store.rows[0]["source_hash"] = "source-3"
        with patch.object(self.index, "_migrate_legacy_prepared_views",
                          side_effect=AssertionError("Migration repeated")):
            rebuilt = self.index.build(self.store, Client())
        self.assertEqual((rebuilt["prepared_documents_reused"], rebuilt["new_embeddings"]), (2, 0))
        self.assertEqual(self.index.search("alpha", Client(), self.store)[0]["source_hash"], "source-3")

    def test_unmodified_legacy_cache_reuses_preparation_without_reading_old_rows(self):
        self._legacy_index()
        client = Client()
        with patch.object(self.index, "_migrate_legacy_prepared_views",
                          side_effect=AssertionError("Unnecessary legacy scan")), \
                patch.object(client, "chunk_text", side_effect=AssertionError("Legacy text was chunked")):
            rebuilt = self.index.build(self.store, client)
        self.assertEqual((rebuilt["prepared_documents_reused"], rebuilt["new_embeddings"]), (2, 0))

    def test_legacy_migration_rejects_changed_old_row_checksum(self):
        built = self._legacy_index()
        old_rows = self.index.data_dir / built["rows_file"]
        old_rows.write_text(old_rows.read_text().replace("Demo.lemma1", "Forged.lemma1"))
        for item in self.store.rows:
            item["source_hash"] = "source-2"
        client = Client()
        with patch.object(client, "chunk_text", wraps=client.chunk_text) as prepare:
            rebuilt = self.index.build(self.store, client)
        self.assertEqual(prepare.call_count, 2)
        self.assertEqual((rebuilt["prepared_documents_reused"], rebuilt["new_embeddings"]), (0, 0))
        with sqlite3.connect(self.index.cache_path) as connection:
            self.assertEqual(connection.execute("SELECT COUNT(*) FROM prepared_view_aliases").fetchone()[0], 0)
            self.assertEqual(connection.execute("SELECT COUNT(*) FROM prepared_view_migrations").fetchone()[0], 0)
        self.assertEqual(len(self.index.search("alpha", Client(), self.store)), 2)

    def test_interrupted_legacy_migration_rolls_back_unverified_aliases(self):
        self._legacy_index()
        original = self.index.pointer.read_bytes()
        for item in self.store.rows:
            item["source_hash"] = "source-2"
        loads = json.loads
        seen_rows = 0

        def interrupted_loads(value, *args, **kwargs):
            nonlocal seen_rows
            if isinstance(value, bytes):
                seen_rows += 1
                if seen_rows == 2:
                    raise KeyboardInterrupt("migration interrupted")
            return loads(value, *args, **kwargs)

        with patch("tools.proof_atlas.vectors.json.loads", side_effect=interrupted_loads):
            with self.assertRaisesRegex(KeyboardInterrupt, "migration interrupted"):
                self.index.build(self.store, Client())
        self.assertEqual(self.index.pointer.read_bytes(), original)
        with sqlite3.connect(self.index.cache_path) as connection:
            self.assertEqual(connection.execute("SELECT COUNT(*) FROM prepared_view_aliases").fetchone()[0], 0)
            self.assertEqual(connection.execute("SELECT COUNT(*) FROM prepared_view_migrations").fetchone()[0], 0)
        client = Client()
        with patch.object(client, "chunk_text", side_effect=AssertionError("Legacy text was chunked")):
            rebuilt = self.index.build(self.store, client)
        self.assertEqual((rebuilt["prepared_documents_reused"], rebuilt["new_embeddings"]), (2, 0))

    def test_same_dimensions_different_model_revision_rejected_and_separate_cache(self):
        self.index.build(self.store, Client())
        with self.assertRaises(EmbeddingModelMismatch):
            self.index.search("alpha", Client(revision="two"), self.store)
        rebuilt = self.index.build(self.store, Client(revision="two"))
        self.assertEqual(rebuilt["new_embeddings"], 2)
        self.assertEqual(rebuilt["cached_embeddings"], 0)

    def test_failed_rebuild_preserves_previous_complete_generation(self):
        self.index.build(self.store, Client())
        original = self.index.pointer.read_bytes()
        with self.assertRaisesRegex(RuntimeError, "interrupted inference"):
            self.index.build(self.store, Client(revision="two", fail_after=0))
        self.assertEqual(self.index.pointer.read_bytes(), original)
        self.assertEqual(len(self.index.search("alpha", Client(), self.store)), 2)

    def test_changes_outside_selected_view_set_do_not_invalidate_index(self):
        self.index.build(self.store, Client(), views=["objects"])
        self.store.rows.append(row(3, "new trace", "proof_state"))
        self.store.snapshot = "snapshot-with-new-trace"
        self.assertEqual(len(self.index.search("alpha", Client(), self.store)), 1)
        self.assertTrue(self.index.status(self.store)["source_set_current"])

    def test_new_trace_inside_default_view_set_requires_rebuild(self):
        self.index.build(self.store, Client())
        self.store.rows.append(row(3, "new trace", "proof_state"))
        with self.assertRaises(StaleVectorIndex):
            self.index.search("alpha", Client(), self.store)

    def test_length_bucketing_preserves_source_vector_row_alignment(self):
        self.store.rows = [row(1, "alpha " + "x" * 80), row(2, "beta"),
                           row(3, "alpha short"), row(4, "beta " + "y" * 70)]
        client = Client()
        built = self.index.build(self.store, client, batch_size=2, pending_buffer=8)
        records = [json.loads(line) for line in
                   (self.index.data_dir / built["rows_file"]).read_text().splitlines()]
        matrix = np.load(self.index.data_dir / built["matrix_file"])
        for record, vector in zip(records, matrix):
            expected = [1., 0.] if "alpha" in record["text"] else [0., 1.]
            np.testing.assert_array_equal(vector, expected)
        self.assertEqual([item["document_id"] for item in records], [1, 1, 1, 2, 3, 4, 4])
        self.assertEqual(sum(len(call) for call in client.calls), built["new_embeddings"])

    def test_parallel_preparation_overlaps_embedding_and_retains_row_order(self):
        started, prepared_next = threading.Event(), threading.Event()
        owner_thread = threading.get_ident()

        class OverlapClient(ParallelClient):
            def chunk_text(inner, text, **kwargs):
                if text == "beta next":
                    if not started.wait(5):
                        raise AssertionError("Embedding did not start before next buffer preparation")
                    prepared_next.set()
                return super().chunk_text(text, **kwargs)

            def embed_prepared(inner, texts, token_counts, batch_size=16):
                started.set()
                if not prepared_next.wait(5):
                    raise AssertionError("Next buffer was not prepared while embedding was in flight")
                return super().embed_prepared(texts, token_counts, batch_size=batch_size)

        self.store.rows = [row(1, "alpha"), row(2, "beta"), row(3, "beta next"), row(4, "alpha last")]
        client = OverlapClient()
        built = self.index.build(self.store, client, batch_size=1, pending_buffer=2)
        self.assertTrue(built["parallel_preparation"])
        self.assertEqual(client.preparation_threads, {owner_thread})
        self.assertEqual(len(client.embedding_threads), 1)
        self.assertNotIn(owner_thread, client.embedding_threads)
        self.assertEqual(sorted(client.prepared_counts), [4, 5, 9, 10])
        records = [json.loads(line) for line in
                   (self.index.data_dir / built["rows_file"]).read_text().splitlines()]
        self.assertEqual([record["document_id"] for record in records], [1, 2, 3, 4])
        matrix = np.load(self.index.data_dir / built["matrix_file"])
        np.testing.assert_array_equal(matrix, [[1., 0.], [0., 1.], [0., 1.], [1., 0.]])

    def test_parallel_failure_caches_completed_batches_and_preserves_generation(self):
        self.index.build(self.store, Client())
        original = self.index.pointer.read_bytes()
        self.store.rows = [row(i, f"alpha {i}") for i in range(6)]
        with self.assertRaisesRegex(RuntimeError, "interrupted inference"):
            self.index.build(self.store, ParallelClient(revision="two", fail_after=1),
                             batch_size=2, pending_buffer=4)
        self.assertEqual(self.index.pointer.read_bytes(), original)
        rebuilt = self.index.build(self.store, ParallelClient(revision="two"),
                                   batch_size=2, pending_buffer=4)
        self.assertEqual(rebuilt["new_embeddings"], 4)
        self.assertEqual(rebuilt["cached_embeddings"], 2)

    def test_preparation_failure_waits_for_active_batches_and_saves_them(self):
        started, release = threading.Event(), threading.Event()

        class PreparationFailure(ParallelClient):
            def chunk_text(inner, text, **kwargs):
                if text == "preparation fails":
                    if not started.wait(5):
                        raise AssertionError("No active embedding batch")
                    release.set()
                    raise ValueError("preparation failed")
                return super().chunk_text(text, **kwargs)

            def embed_prepared(inner, texts, token_counts, batch_size=16):
                started.set()
                if not release.wait(5):
                    raise AssertionError("Preparation failure did not release embedding")
                return super().embed_prepared(texts, token_counts, batch_size=batch_size)

        self.store.rows = [row(1, "alpha"), row(2, "beta"), row(3, "preparation fails")]
        client = PreparationFailure()
        with self.assertRaisesRegex(ValueError, "preparation failed"):
            self.index.build(self.store, client, batch_size=2, pending_buffer=2)
        self.assertEqual(len(client.calls), 1)
        self.assertEqual(self.index.status()["status"], "missing")
        rebuilt = self.index.build(self.store, Client(), batch_size=2, pending_buffer=2)
        self.assertEqual((rebuilt["cached_embeddings"], rebuilt["new_embeddings"]), (2, 1))

    def test_inflight_duplicate_input_is_embedded_once(self):
        started, prepared_duplicate = threading.Event(), threading.Event()

        class DuplicateClient(ParallelClient):
            def chunk_text(inner, text, **kwargs):
                inner.preparation_threads.add(threading.get_ident())
                if text == "alpha duplicate":
                    if not started.wait(5):
                        raise AssertionError("Embedding did not start")
                    prepared_duplicate.set()
                    text = "alpha"
                return [EmbeddingChunk(text, 0, len(text), 0, len(text), len(text), "character")]

            def embed_prepared(inner, texts, token_counts, batch_size=16):
                started.set()
                if not prepared_duplicate.wait(5):
                    raise AssertionError("Duplicate was not prepared during inference")
                return super().embed_prepared(texts, token_counts, batch_size=batch_size)

        self.store.rows = [row(1, "alpha"), row(2, "beta"), row(3, "alpha duplicate")]
        client = DuplicateClient()
        built = self.index.build(self.store, client, batch_size=2, pending_buffer=2)
        self.assertEqual((built["chunks"], built["new_embeddings"]), (3, 2))
        self.assertEqual(sum(len(call) for call in client.calls), 2)

    def test_client_without_parallel_preparation_keeps_serial_protocol(self):
        client = Client()
        client.supports_parallel_preparation = False
        client.embed_prepared = lambda *args, **kwargs: self.fail("Serial client used prepared embedding")
        owner_thread = threading.get_ident()
        embed = client.embed_texts

        def serial(*args, **kwargs):
            self.assertEqual(threading.get_ident(), owner_thread)
            return embed(*args, **kwargs)

        client.embed_texts = serial
        built = self.index.build(self.store, client, batch_size=1, pending_buffer=1)
        self.assertFalse(built["parallel_preparation"])

    def test_private_declarations_require_explicit_opt_in(self):
        self.store.rows.append(row(3, "alpha private", private=True))
        built = self.index.build(self.store, Client())
        self.assertEqual(built["documents"], 2)
        built = self.index.build(self.store, Client(), include_internal=True)
        self.assertEqual(built["documents"], 3)

    def test_namespace_filter_matches_segments_and_module_filter_is_exact(self):
        self.store.rows = [row(1, "alpha", namespace="A"), row(2, "alpha", namespace="A.B"),
                           row(3, "alpha", namespace="AB"), row(4, "alpha", module="Other")]
        self.index.build(self.store, Client())
        found = self.index.search("alpha", Client(), self.store, namespace="A", module="Demo.Core")
        self.assertEqual({item["name"] for item in found}, {"A.lemma1", "A.B.lemma2"})

    def test_long_source_retains_parent_and_exact_source_spans(self):
        text = "alpha " + "z" * 120
        self.store.rows = [row(1, text, "full_proof")]
        built = self.index.build(self.store, Client())
        self.assertEqual(built["chunks"], 4)
        found = self.index.search("alpha", Client(), self.store, limit=10)
        found.sort(key=lambda item: item["chunk_start"])
        self.assertEqual("".join(text[item["chunk_start"]:item["chunk_end"]] for item in found), text)
        self.assertTrue(all(item["parent_end"] == len(text) for item in found))

    def test_invalid_embedding_response_is_not_cached_or_published(self):
        client = Client()
        client.embed_texts = lambda *a, **kw: np.asarray([[float("nan"), 0.], [0., 1.]])
        with self.assertRaises(VectorIndexError):
            self.index.build(self.store, client)
        self.assertEqual(self.index.status()["status"], "missing")
        self.assertEqual(self.index.build(self.store, Client())["new_embeddings"], 2)

    def test_modified_row_metadata_cannot_silently_rebind_vectors(self):
        built = self.index.build(self.store, Client())
        rows_file = self.index.data_dir / built["rows_file"]
        rows_file.write_text(rows_file.read_text().replace("alpha", "other"))
        with self.assertRaisesRegex(VectorIndexError, "checksum changed"):
            self.index.search("alpha", Client(), self.store)

    def test_chunk_budget_is_persisted_and_invalidates_prepared_chunks(self):
        self.index.build(self.store, Client(), chunk_tokens=100)
        rebuilt = self.index.build(self.store, Client(), chunk_tokens=200)
        self.assertEqual(rebuilt["chunk_tokens"], 200)
        self.assertEqual(rebuilt["prepared_documents_reused"], 0)
        self.assertEqual(rebuilt["new_embeddings"], 0)

    def test_empty_source_set_is_a_valid_empty_semantic_index(self):
        self.store.rows = []
        self.index.build(self.store, Client())
        self.assertEqual(self.index.search("alpha", Client(), self.store), [])


if __name__ == "__main__":
    unittest.main()
