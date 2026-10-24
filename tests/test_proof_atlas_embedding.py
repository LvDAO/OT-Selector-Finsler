"""Contract checks for model identity, complete text coverage and service failures."""
import unittest
import hashlib
import json
from pathlib import Path
import subprocess
import tempfile
import threading
from types import SimpleNamespace
from unittest.mock import patch

import numpy as np

from tools.proof_atlas.embedding import (
    EmbeddingError, EmbeddingInputTooLong, EmbeddingModelMismatch,
    QwenEmbeddingClient, TEIEmbeddingClient, _local_identity, assert_fingerprint,
    discover_embedding_url,
)


class FakeTEI:
    def __init__(self, limit=120):
        self.limit = limit
        self.calls = []
        self.embedding_result = None
        self.failure = None

    def __call__(self, path, payload):
        self.calls.append((path, payload))
        if self.failure and path == "/embed":
            raise self.failure
        if path == "/info":
            return {
                "model_id": "test/model", "model_sha": "revision-1",
                "model_dtype": "float32", "model_type": {"embedding": {"pooling": "cls"}},
                "max_input_length": self.limit, "max_client_batch_size": 4, "version": "test",
            }
        if path == "/tokenize":
            return [[{"id": 1}] * (len(text) + 2) for text in payload["inputs"]]
        if self.embedding_result is not None:
            return self.embedding_result
        return [[0.6, 0.8] for _ in payload["inputs"]]


class EmbeddingContractTests(unittest.TestCase):
    def client(self, service=None):
        service = service or FakeTEI()
        return TEIEmbeddingClient("http://test", transport=service), service

    def test_same_dimension_different_revision_cannot_reuse_index(self):
        client, _ = self.client()
        changed = client.fingerprint | {"model_revision": "revision-2"}
        with self.assertRaises(EmbeddingModelMismatch):
            client.assert_fingerprint(changed)
        assert_fingerprint(client.fingerprint, client.fingerprint)

    def test_modified_local_weights_change_identity_under_same_revision(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / "config.json").write_text(json.dumps({"hidden_size": 2}))
            metadata = root / ".cache/huggingface/download"
            metadata.mkdir(parents=True)
            (metadata / "config.json.metadata").write_text("same-upstream-revision\n")
            (root / "model.bin").write_bytes(b"original weights")
            before = _local_identity(root)
            (root / "model.bin").write_bytes(b"modified weights")
            after = _local_identity(root)
            self.assertEqual(before[0], after[0])
            self.assertEqual(before[2], after[2])
            self.assertNotEqual(before[1], after[1])

    def test_pooling_change_cannot_reuse_index(self):
        client, _ = self.client()
        with self.assertRaises(EmbeddingModelMismatch):
            client.assert_fingerprint(client.fingerprint | {"pooling": "last_token"})

    def test_overlength_never_reaches_embedding_even_after_valid_input(self):
        client, service = self.client(FakeTEI(limit=80))
        service.calls.clear()
        with self.assertRaises(EmbeddingInputTooLong):
            client.embed_texts(["short", "x" * 81], batch_size=1)
        self.assertFalse(any(path == "/embed" for path, _ in service.calls))

    def test_embedding_explicitly_disables_truncation_and_normalizes(self):
        client, service = self.client()
        service.calls.clear()
        vectors = client.embed_texts(["a", "b"])
        self.assertEqual(vectors.shape, (2, 2))
        self.assertEqual(vectors.dtype, np.float32)
        request = next(body for path, body in service.calls if path == "/embed")
        self.assertIs(request["truncate"], False)
        self.assertIs(request["normalize"], True)

    def test_prepared_embeddings_do_not_repeat_tokenization(self):
        client, service = self.client()
        counts = client.token_counts(["first", "second"])
        service.calls.clear()
        with patch.object(client, "token_counts", side_effect=AssertionError("recounted")):
            result = client.embed_prepared(["first", "second"], counts, batch_size=1)
        self.assertEqual(result.shape, (2, 2))
        self.assertEqual([path for path, _ in service.calls], ["/embed", "/embed"])

    def test_exact_token_counts_are_reused_only_within_each_client(self):
        client, service = self.client()
        other, other_service = self.client()
        service.calls.clear()
        other_service.calls.clear()
        text = "∀ x, λ x"
        self.assertEqual(client.count_tokens(text), len(text) + 2)
        self.assertEqual(client.count_tokens(text), len(text) + 2)
        self.assertEqual(client.count_tokens(text + " "), len(text) + 3)
        self.assertEqual(other.count_tokens(text), len(text) + 2)
        self.assertEqual([body["inputs"] for path, body in service.calls
                          if path == "/tokenize"], [[text], [text + " "]])
        self.assertEqual([body["inputs"] for path, body in other_service.calls
                          if path == "/tokenize"], [[text]])

    def test_prepared_invalid_or_long_counts_fail_before_any_embedding(self):
        client, service = self.client(FakeTEI(limit=80))
        for counts in ([1], [1, True], [1, 0], [1, 2.5], [1, 81]):
            with self.subTest(counts=counts):
                service.calls.clear()
                with self.assertRaises(EmbeddingError):
                    client.embed_prepared(["first", "second"], counts, batch_size=1)
                self.assertEqual(service.calls, [])

    def test_wrong_dimension_nonfinite_and_bad_row_count_fail(self):
        for response in ([[1.0, 0.0, 0.0]], [[float("nan"), 0]], [[1, 0], [1, 0]]):
            with self.subTest(response=response):
                client, service = self.client()
                service.embedding_result = response
                with self.assertRaises(EmbeddingError):
                    client.embed_texts(["a"])

    def test_zero_or_unnormalized_vectors_fail(self):
        for response in ([[0, 0]], [[1, 1]]):
            client, service = self.client()
            service.embedding_result = response
            with self.assertRaises(EmbeddingError):
                client.embed_texts(["a"])

    def test_chunking_covers_original_without_clipping_context(self):
        client, _ = self.client(FakeTEI(limit=80))
        text = "theorem p\n" + "  (binder : Type)\n" * 7 + ":= by\n  rfl\n"
        context = "namespace Test"
        chunks = client.chunk_text(text, context=context, source_start=100)
        self.assertGreater(len(chunks), 1)
        self.assertEqual("".join(text[c.start:c.end] for c in chunks), text)
        self.assertEqual(chunks[0].start, 0)
        self.assertEqual(chunks[-1].end, len(text))
        for chunk in chunks:
            self.assertTrue(chunk.text.startswith(context + "\n\n"))
            self.assertEqual(chunk.text, context + "\n\n" + text[chunk.start:chunk.end])
            self.assertLessEqual(chunk.token_count, 80)
            self.assertEqual((chunk.parent_start, chunk.parent_end), (100, 100 + len(text)))

    def test_long_single_line_uses_checked_character_spans(self):
        client, _ = self.client(FakeTEI(limit=80))
        text = "λ" * 200
        chunks = client.chunk_text(text)
        self.assertEqual("".join(c.text for c in chunks), text)
        self.assertTrue(any(c.boundary == "character" for c in chunks))
        self.assertTrue(all(c.token_count <= 80 for c in chunks))

    def test_long_single_line_tokenizes_bounded_local_prefixes(self):
        client, service = self.client(FakeTEI(limit=80))
        service.calls.clear()
        text = "x" * 10000
        chunks = client.chunk_text(text)
        tokenized = [body["inputs"][0] for path, body in service.calls if path == "/tokenize"]
        self.assertEqual("".join(chunk.text for chunk in chunks), text)
        # A failing 4 * token-budget probe bounds later probes independently
        # of total source length. Calls grow with chunks, not suffix length.
        self.assertLessEqual(max(map(len, tokenized)), 4 * 80)
        self.assertLessEqual(len(tokenized), 14 * len(chunks))
        self.assertLessEqual(sum(map(len, tokenized)), 20 * len(text))
        self.assertTrue(all(chunk.token_count <= 80 for chunk in chunks))

    def test_oversized_whole_context_is_rejected(self):
        client, _ = self.client(FakeTEI(limit=80))
        with self.assertRaises(EmbeddingInputTooLong):
            client.chunk_text("proof", context="c" * 80)

    def test_network_timeout_becomes_actionable_embedding_error(self):
        client, _ = self.client()
        client._transport = None
        with patch.object(client._opener, "open", side_effect=TimeoutError):
            with self.assertRaisesRegex(EmbeddingError, "request failed: TimeoutError"):
                client.embed_texts(["proof"])

    def test_failed_later_batch_cannot_return_a_partial_matrix(self):
        client, service = self.client()
        original = service.__call__
        completed = []
        def fail_second(path, body):
            if path == "/embed":
                completed.append(body["inputs"])
                if len(completed) == 2:
                    raise EmbeddingError("second batch failed")
            return original(path, body)
        client._transport = fail_second
        with self.assertRaisesRegex(EmbeddingError, "second batch failed"):
            client.embed_texts(["first", "second"], batch_size=1)
        self.assertEqual(len(completed), 2)

    def test_url_override_does_not_need_docker(self):
        with patch.dict("os.environ", {"PROOF_ATLAS_EMBEDDING_URL": "http://localhost:8123"}):
            with patch("tools.proof_atlas.embedding._docker_service", side_effect=AssertionError):
                self.assertEqual(discover_embedding_url(), "http://localhost:8123")

    def test_container_network_address_is_discovered_each_time(self):
        def inspected(ip):
            result = [{"State": {"Running": True}, "Config": {"Cmd": ["--port", "9001"]},
                       "NetworkSettings": {"Ports": {}, "Networks": {"test": {"IPAddress": ip}}}}]
            return subprocess.CompletedProcess([], 0, stdout=json.dumps(result))
        with patch.dict("os.environ", {}, clear=True):
            with patch("tools.proof_atlas.embedding.subprocess.run",
                       side_effect=[inspected("10.0.0.1"), inspected("10.0.0.2")]):
                self.assertEqual(discover_embedding_url(), "http://10.0.0.1:9001")
                self.assertEqual(discover_embedding_url(), "http://10.0.0.2:9001")

    def test_service_without_known_revision_is_rejected(self):
        service = FakeTEI()
        def transport(path, body):
            result = service(path, body)
            if path == "/info":
                result["model_sha"] = None
            return result
        with self.assertRaisesRegex(EmbeddingError, "Unknown model revision"):
            TEIEmbeddingClient("http://test", transport=transport)

    def test_verified_local_tokenizer_preserves_whole_ids_and_fingerprint(self):
        class RawTokenizer:
            def __init__(self):
                self.padding_disabled = self.truncation_disabled = False
            def to_str(self):
                return '{"unicode":"λ", "post_processor":{"end":1}}'
            def no_padding(self):
                self.padding_disabled = True
            def no_truncation(self):
                self.truncation_disabled = True
            def encode_batch(self, texts, *, add_special_tokens):
                self_test.assertTrue(add_special_tokens)
                self_test.assertTrue(self.padding_disabled and self.truncation_disabled)
                return [SimpleNamespace(ids=list(range(len(text) + 1))) for text in texts]
        self_test = self
        tokenizer = RawTokenizer()
        canonical = json.dumps(json.loads(tokenizer.to_str()), sort_keys=True,
                               separators=(",", ":"), ensure_ascii=False).encode()
        client = QwenEmbeddingClient.__new__(QwenEmbeddingClient)
        client._local_tokenizer = None
        client._fingerprint = {"base": "unchanged"}
        client.info = {"tokenizer_backend_sha256": hashlib.sha256(canonical).hexdigest()}
        module = SimpleNamespace(Tokenizer=SimpleNamespace(from_file=lambda path: tokenizer))
        with patch.dict("sys.modules", {"tokenizers": module}):
            client._configure_local_tokenizer(Path("/offline/model"))
        self.assertTrue(client.supports_parallel_preparation)
        with patch.object(client, "_request", side_effect=AssertionError("GPU tokenization")):
            self.assertEqual(client.token_counts(["", "λ中文"]), [1, 4])
        self.assertEqual(client.fingerprint, {"base": "unchanged"})

    def test_unverified_or_missing_local_tokenizer_keeps_safe_worker_path(self):
        client = QwenEmbeddingClient.__new__(QwenEmbeddingClient)
        client._local_tokenizer = None
        client.info = {"tokenizer_backend_sha256": "wrong-backend"}
        tokenizer = SimpleNamespace(to_str=lambda: '{}')
        module = SimpleNamespace(Tokenizer=SimpleNamespace(from_file=lambda path: tokenizer))
        with patch.dict("sys.modules", {"tokenizers": module}):
            with self.assertRaisesRegex(EmbeddingError, "tokenizer backend differs"):
                client._configure_local_tokenizer(Path("/offline/model"))
        self.assertFalse(client.supports_parallel_preparation)
        with patch.dict("sys.modules", {"tokenizers": None}):
            client._configure_local_tokenizer(Path("/offline/model"))
        with patch.object(client, "_request", return_value={"counts": [2, 4]}) as worker:
            self.assertEqual(client.token_counts(["a", "abc"]), [2, 4])
        worker.assert_called_once_with("/tokenize", {"inputs": ["a", "abc"]})

    def test_local_preparation_does_not_wait_for_busy_gpu_channel(self):
        client = QwenEmbeddingClient.__new__(QwenEmbeddingClient)
        client._request_lock = threading.Lock()
        client._local_tokenizer = SimpleNamespace(encode_batch=lambda texts, **kw: [
            SimpleNamespace(ids=[1, 2]) for _ in texts])
        started, release = threading.Event(), threading.Event()
        def busy_gpu(path, payload):
            started.set()
            if not release.wait(5):
                raise AssertionError("test GPU release timed out")
            return [[0.6, 0.8]]
        with patch.object(client, "_worker_request", side_effect=busy_gpu):
            thread = threading.Thread(target=lambda: client._request("/embed", {}))
            thread.start()
            try:
                self.assertTrue(started.wait(2))
                self.assertEqual(client.token_counts(["proof"]), [2])
                self.assertTrue(thread.is_alive())
            finally:
                release.set()
                thread.join(5)
            self.assertFalse(thread.is_alive())


if __name__ == "__main__":
    unittest.main()
