"""Local TEI embeddings with exact length checks and immutable model identity.

All chunk offsets are Python character offsets in the unmodified parent text.
``EmbeddingChunk.text`` is the actual model input: optional context followed by
that exact parent slice. No source characters are discarded between chunks.
"""
from __future__ import annotations

from dataclasses import asdict, dataclass
from functools import cached_property, lru_cache
from bisect import bisect_right
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys
from typing import Any, Callable, Mapping, Sequence
from urllib.error import HTTPError, URLError
from urllib.parse import urlparse
from urllib.request import ProxyHandler, Request, build_opener

import numpy as np


def default_qwen_model_directory() -> Path:
    """Locate the pinned snapshot in the standard local Hugging Face cache.

    This only constructs a path; the caller validates local files and never
    downloads missing weights.
    """
    cache = os.environ.get("HF_HUB_CACHE")
    if cache:
        hub = Path(cache).expanduser()
    else:
        hf_home = os.environ.get("HF_HOME")
        home = Path(hf_home).expanduser() if hf_home else (
            Path(os.environ.get("XDG_CACHE_HOME", str(Path.home() / ".cache"))).expanduser()
            / "huggingface"
        )
        hub = home / "hub"
    return (hub / "models--Qwen--Qwen3-Embedding-0.6B" / "snapshots"
            / "97b0c614be4d77ee51c0cef4e5f07c00f9eb65b3")


class EmbeddingError(RuntimeError):
    """The embedding service or its response violates the indexing contract."""


class EmbeddingInputTooLong(EmbeddingError):
    """Input exceeds the model limit; chunk it before embedding."""


class EmbeddingModelMismatch(EmbeddingError):
    """An existing index was encoded with a different model fingerprint."""


@dataclass(frozen=True)
class EmbeddingChunk:
    text: str
    start: int
    end: int
    parent_start: int
    parent_end: int
    token_count: int
    boundary: str = "semantic"

    def to_dict(self) -> dict[str, Any]:
        return asdict(self)


def _docker_service() -> tuple[str, Mapping[str, Any]]:
    try:
        result = subprocess.run(
            ["docker", "inspect", "vllm-embed"], capture_output=True, text=True,
            timeout=10, check=True,
        )
        service = json.loads(result.stdout)[0]
        if not service["State"]["Running"]:
            raise EmbeddingError("Docker embedding service vllm-embed is stopped")
        args = service["Config"].get("Cmd") or []
        port = 8001
        if "--port" in args:
            port = int(args[args.index("--port") + 1])
        if not 1 <= port <= 65535:
            raise ValueError("invalid service port")
        mappings = service["NetworkSettings"].get("Ports") or {}
        for mapping in mappings.get(f"{port}/tcp") or []:
            host = mapping.get("HostIp") or "127.0.0.1"
            if host in ("0.0.0.0", "::"):
                host = "127.0.0.1"
            return f"http://{host}:{int(mapping['HostPort'])}", service
        for network in service["NetworkSettings"].get("Networks", {}).values():
            if network.get("IPAddress"):
                return f"http://{network['IPAddress']}:{port}", service
        raise EmbeddingError("Docker embedding service has no reachable network address")
    except EmbeddingError:
        raise
    except (OSError, ValueError, KeyError, IndexError, subprocess.SubprocessError) as exc:
        raise EmbeddingError(
            "Cannot discover vllm-embed; set PROOF_ATLAS_EMBEDDING_URL explicitly"
        ) from exc


def discover_embedding_url() -> str:
    """Use the explicit override or discover the running container's address."""
    return os.environ.get("PROOF_ATLAS_EMBEDDING_URL") or _docker_service()[0]


def _model_directory(service: Mapping[str, Any] | None, model_id: str) -> Path | None:
    override = os.environ.get("PROOF_ATLAS_EMBEDDING_MODEL_DIR")
    if override:
        return Path(override)
    if service is None:
        return None
    for mount in service.get("Mounts", []):
        destination = str(mount.get("Destination", "")).rstrip("/")
        if model_id == destination or model_id.startswith(destination + "/"):
            suffix = model_id[len(destination):].lstrip("/")
            return Path(mount["Source"]) / suffix
    return None


def _local_identity(directory: Path) -> tuple[str | None, str, int | None]:
    """Hash the actual local weights, tokenizer, pooling and configuration files.

    Metadata gives a readable upstream revision, while the content digest also
    distinguishes modified weights under the same revision/name/dimension.
    """
    if not directory.is_dir():
        raise EmbeddingError(f"Local embedding model directory is missing: {directory}")
    weight_files = sorted(set(directory.glob("*.safetensors")) | set(directory.glob("*.bin")))
    if not weight_files:
        raise EmbeddingError("Local model identity requires actual model weight files")
    files = set(weight_files)
    for pattern in ("*.json", "*.model", "vocab.txt", "vocab.json", "merges.txt", "*/config.json"):
        files.update(directory.glob(pattern))
    digest = hashlib.sha256()
    for path in sorted(files):
        if not path.is_file():
            continue
        digest.update(str(path.relative_to(directory)).encode("utf-8") + b"\0")
        file_hash = hashlib.sha256()
        with path.open("rb") as source:
            for block in iter(lambda: source.read(8 * 1024 * 1024), b""):
                file_hash.update(block)
        digest.update(file_hash.digest())
    revisions = set()
    for path in (directory / ".cache/huggingface/download").glob("*.metadata"):
        lines = path.read_text().splitlines()
        if lines:
            revisions.add(lines[0])
    revision = next(iter(revisions)) if len(revisions) == 1 else None
    config_path = directory / "config.json"
    config = json.loads(config_path.read_text()) if config_path.is_file() else {}
    dimension = config.get("hidden_size") or config.get("d_model")
    return revision, digest.hexdigest(), int(dimension) if dimension is not None else None


def assert_fingerprint(expected: Mapping[str, Any], actual: Mapping[str, Any]) -> None:
    """Reject reuse across revisions even when embedding dimensions agree."""
    if dict(expected) != dict(actual):
        differences = sorted(k for k in set(expected) | set(actual) if expected.get(k) != actual.get(k))
        raise EmbeddingModelMismatch("Embedding fingerprint changed: " + ", ".join(differences))


class TEIEmbeddingClient:
    """Strict, offline-service client; construction probes one short embedding.

    Fingerprint keys are ``schema_version``, ``model_name``, ``model_revision``,
    ``artifact_sha256``, ``pooling``, ``dimension``, ``dtype``, ``normalize``,
    and ``tei_version``. The URL is deliberately excluded from model identity.
    An overridden service must expose ``model_sha`` or have an explicit local
    ``model_dir`` / ``PROOF_ATLAS_EMBEDDING_MODEL_DIR`` to identify its weights.
    """

    def __init__(
        self, url: str | None = None, *, model_dir: str | Path | None = None,
        timeout: float = 180, transport: Callable[[str, Any], Any] | None = None,
    ) -> None:
        service = None
        override = url or os.environ.get("PROOF_ATLAS_EMBEDDING_URL")
        if override:
            self.url = override.rstrip("/")
        else:
            self.url, service = _docker_service()
        parsed = urlparse(self.url)
        if parsed.scheme not in ("http", "https") or not parsed.hostname or parsed.username:
            raise EmbeddingError("Embedding URL must be an HTTP(S) URL without embedded credentials")
        if timeout <= 0:
            raise ValueError("Embedding timeout must be positive")
        self.timeout = timeout
        self._transport = transport
        self._opener = build_opener(ProxyHandler({}))
        self.info = self._request("/info")
        if not isinstance(self.info, dict):
            raise EmbeddingError("TEI /info did not return an object")
        try:
            self.max_input_length = int(self.info["max_input_length"])
            self.max_client_batch_size = int(self.info.get("max_client_batch_size", 32))
            pooling = self.info["model_type"]["embedding"]["pooling"]
        except (KeyError, TypeError, ValueError) as exc:
            raise EmbeddingError("TEI /info does not describe a bounded embedding model") from exc
        if self.max_input_length < 1 or self.max_client_batch_size < 1 or not isinstance(pooling, str):
            raise EmbeddingError("Invalid TEI token/batch limits or pooling")
        directory = Path(model_dir) if model_dir else _model_directory(service, self.info.get("model_id", ""))
        local_revision = artifact_hash = dimension = None
        if directory is not None:
            local_revision, artifact_hash, dimension = _local_identity(directory)
        revision = self.info.get("model_sha") or local_revision
        if not revision and not artifact_hash:
            raise EmbeddingError("Unknown model revision: supply the local model directory for fingerprinting")
        self._dimension = dimension
        self._fingerprint = {
            "schema_version": 1,
            "model_name": self.info.get("served_model_name") or self.info.get("model_id"),
            "model_revision": revision,
            "artifact_sha256": artifact_hash,
            "pooling": pooling,
            "dimension": dimension,
            "dtype": self.info.get("model_dtype"),
            "normalize": True,
            "tei_version": self.info.get("version"),
            "tei_sha": self.info.get("sha"),
        }
        self.embed_texts(["theorem identity (a : α) : a = a := by rfl"])
        self._fingerprint["dimension"] = self._dimension

    @property
    def fingerprint(self) -> dict[str, Any]:
        return dict(self._fingerprint)

    @property
    def dimension(self) -> int:
        assert self._dimension is not None
        return self._dimension

    @property
    def supports_parallel_preparation(self) -> bool:
        """Whether tokenization can run while a separate embedding call runs."""
        return False

    def assert_fingerprint(self, expected: Mapping[str, Any]) -> None:
        assert_fingerprint(expected, self.fingerprint)

    def _request(self, path: str, payload: Any = None) -> Any:
        if self._transport:
            return self._transport(path, payload)
        body = json.dumps(payload).encode("utf-8") if payload is not None else None
        request = Request(self.url + path, data=body, headers={"Content-Type": "application/json"})
        try:
            with self._opener.open(request, timeout=self.timeout) as response:
                return json.load(response)
        except HTTPError as exc:
            detail = exc.read(2000).decode("utf-8", errors="replace")
            raise EmbeddingError(f"TEI {path} HTTP {exc.code}: {detail}") from exc
        except (OSError, URLError, TimeoutError, ValueError) as exc:
            raise EmbeddingError(f"TEI {path} request failed: {type(exc).__name__}") from exc

    def token_counts(self, texts: Sequence[str]) -> list[int]:
        if not texts:
            return []
        result = self._request("/tokenize", {
            "inputs": list(texts), "add_special_tokens": True, "truncate": False,
        })
        if not isinstance(result, list) or len(result) != len(texts):
            raise EmbeddingError("TEI tokenization returned the wrong number of inputs")
        counts = []
        for row in result:
            if not isinstance(row, list) or not row or any(
                not isinstance(token, dict) or not isinstance(token.get("id"), int) for token in row
            ):
                raise EmbeddingError("TEI tokenization returned malformed tokens")
            counts.append(len(row))
        return counts

    @cached_property
    def _cached_token_count(self) -> Callable[[str], int]:
        """Keep exact probe counts local to this immutable model client."""
        return lru_cache(maxsize=16384)(lambda text: self.token_counts([text])[0])

    def count_tokens(self, text: str) -> int:
        return self._cached_token_count(text)

    def embed_texts(self, texts: Sequence[str], *, batch_size: int = 8) -> np.ndarray:
        """Embed complete inputs; overlength inputs fail before any embedding call.

        Prior successful batches are never returned as a complete result after a
        later failure. Callers persist completed shard batches explicitly.
        """
        if isinstance(texts, str) or any(not isinstance(text, str) for text in texts):
            raise TypeError("Embedding inputs must be a sequence of strings")
        if batch_size < 1:
            raise ValueError("Embedding batch size must be positive")
        if not texts:
            return np.empty((0, self._dimension or 0), dtype=np.float32)
        batch_size = min(batch_size, self.max_client_batch_size)
        # Validate every input first: partial output cannot conceal a long input.
        counts = []
        for start in range(0, len(texts), batch_size):
            counts.extend(self.token_counts(texts[start:start + batch_size]))
        return self.embed_prepared(texts, counts, batch_size=batch_size)

    def embed_prepared(
        self, texts: Sequence[str], token_counts: Sequence[int], *, batch_size: int = 8,
    ) -> np.ndarray:
        """Embed inputs whose exact counts were already obtained by this client.

        This avoids repeating chunk tokenization and permits CPU preparation
        during GPU inference. The backend still receives ``truncate:false``;
        the Qwen worker checks actual lengths again before its forward pass.
        Counts must describe these exact complete inputs, including context.
        """
        if isinstance(texts, str) or any(not isinstance(text, str) for text in texts):
            raise TypeError("Embedding inputs must be a sequence of strings")
        if batch_size < 1:
            raise ValueError("Embedding batch size must be positive")
        if len(token_counts) != len(texts) or any(
            isinstance(count, bool) or not isinstance(count, int) or count < 1
            for count in token_counts
        ):
            raise EmbeddingError("Prepared token counts must be positive integers for every input")
        for index, count in enumerate(token_counts):
            if count > self.max_input_length:
                raise EmbeddingInputTooLong(
                    f"Input {index} has {count} tokens; model limit is {self.max_input_length}"
                )
        if not texts:
            return np.empty((0, self._dimension or 0), dtype=np.float32)
        batch_size = min(batch_size, self.max_client_batch_size)
        matrices = []
        for start in range(0, len(texts), batch_size):
            batch = texts[start:start + batch_size]
            result = self._request("/embed", {
                "inputs": list(batch), "truncate": False, "normalize": True,
            })
            try:
                values = np.asarray(result, dtype=np.float64)
            except (TypeError, ValueError) as exc:
                raise EmbeddingError("TEI returned a malformed embedding matrix") from exc
            if values.ndim != 2 or values.shape[0] != len(batch) or values.shape[1] == 0:
                raise EmbeddingError("TEI embedding row count or dimensions are invalid")
            if not np.isfinite(values).all():
                raise EmbeddingError("TEI returned non-finite embedding coordinates")
            if self._dimension is None:
                self._dimension = values.shape[1]
            if values.shape[1] != self._dimension:
                raise EmbeddingError("TEI embedding dimension changed within one model fingerprint")
            norms = np.linalg.norm(values, axis=1)
            if not np.isfinite(norms).all() or np.any(norms < 1e-12):
                raise EmbeddingError("TEI returned an invalid or zero embedding vector")
            if np.any(np.abs(norms - 1) > 1e-3):
                raise EmbeddingError("TEI ignored normalize:true or returned unnormalized embeddings")
            matrices.append(values.astype(np.float32))
        return np.concatenate(matrices, axis=0)

    def chunk_text(
        self, text: str, *, context: str = "", source_start: int = 0,
        max_tokens: int | None = None,
    ) -> list[EmbeddingChunk]:
        """Split only as necessary, preferring field, binder and proof-line ends.

        A single oversized line falls back to exact-token-checked character
        spans, marked ``character``. Context is repeated whole and never clipped.
        ``start/end`` locate each original slice; ``parent_start/parent_end``
        locate the complete parent view in its caller's coordinate system.
        """
        limit = min(self.max_input_length if max_tokens is None else max_tokens, self.max_input_length)
        if limit < 1:
            raise ValueError("Chunk token limit must be positive")
        prefix = context + "\n\n" if context else ""
        context_count = self.count_tokens(prefix) if context else 0
        if context_count >= limit:
            raise EmbeddingInputTooLong("Whole chunk context leaves no room for source text")
        parent_end = source_start + len(text)
        if not text:
            count = self.count_tokens(prefix)
            return [EmbeddingChunk(prefix, 0, 0, source_start, parent_end, count, "whole")]
        # Four characters per available token seeds the search only. Every
        # accepted span is checked by the exact tokenizer. Exponential growth
        # keeps large compressible inputs possible without repeatedly tokenizing
        # an entire long suffix when its first line already exceeds the limit.
        seed = max(1, 4 * (limit - context_count))
        boundaries = sorted({m.end() for m in re.finditer(r"\n|(?<=:= by )", text)} | {len(text)})
        chunks = []
        start = 0
        while start < len(text):
            counts: dict[int, int] = {}

            def count_to(end: int) -> int:
                if end not in counts:
                    counts[end] = self.count_tokens(prefix + text[start:end])
                return counts[end]

            # Locate a bounded local envelope before searching within it.
            # Successful probes may double; the first failing probe bounds all
            # subsequent tokenization calls for this chunk.
            step = min(seed, len(text) - start)
            candidate = start + step
            best = None
            if count_to(candidate) <= limit:
                best = candidate
                while candidate < len(text):
                    step = min(step * 2, len(text) - start)
                    candidate = start + step
                    if count_to(candidate) > limit:
                        break
                    best = candidate
            if best != len(text):
                low = start + 1 if best is None else best + 1
                high = candidate - 1
                while low <= high:
                    middle = (low + high) // 2
                    if count_to(middle) <= limit:
                        best = middle
                        low = middle + 1
                    else:
                        high = middle - 1
            if best is None or best <= start:
                raise EmbeddingInputTooLong("A source character cannot fit beside the whole context")

            # Prefer a complete field, binder or tactic line inside the checked
            # envelope. Check that exact boundary too: tokenizer prefix lengths
            # need not be strictly monotone near subword merges.
            first = bisect_right(boundaries, start)
            last = bisect_right(boundaries, best) - 1
            boundary = "character"
            low, high = first, last
            semantic_end = None
            while low <= high:
                middle = (low + high) // 2
                end = boundaries[middle]
                if count_to(end) <= limit:
                    semantic_end = end
                    low = middle + 1
                else:
                    high = middle - 1
            if semantic_end is not None:
                best = semantic_end
                boundary = "semantic"
            if start == 0 and best == len(text):
                boundary = "whole"
            value = prefix + text[start:best]
            chunks.append(EmbeddingChunk(value, start, best, source_start, parent_end,
                                         count_to(best), boundary))
            start = best
        return chunks



class QwenEmbeddingClient(TEIEmbeddingClient):
    """Persistent offline worker for the cached Qwen3-Embedding-0.6B base.

    Torch stays in the worker interpreter. No fine-tuned adapters,
    checkpoints, or network model downloads are used. Use ``close()`` or a
    context manager to release the model and GPU after an indexing run.
    """

    def __init__(
        self, model_dir: str | Path | None = None, *,
        worker_python: str | None = None,
        device: str = "auto", timeout: float = 180, batch_size: int = 16,
    ) -> None:
        if timeout <= 0 or batch_size < 1:
            raise ValueError("Worker timeout and batch size must be positive")
        worker_python = worker_python or os.environ.get("PROOF_ATLAS_WORKER_PYTHON") or sys.executable
        directory = Path(model_dir or os.environ.get("PROOF_ATLAS_QWEN_MODEL_DIR")
                         or default_qwen_model_directory()).expanduser()
        revision, artifact_hash, dimension = _local_identity(directory)
        if revision is None and re.fullmatch(r"[0-9a-f]{40}", directory.name):
            revision = directory.name
        self.timeout = timeout
        self._stdout_buffer = b""
        self._local_tokenizer = None
        import threading
        self._request_lock = threading.Lock()
        environment = dict(os.environ)
        environment.update({
            "HF_HUB_OFFLINE": "1", "TRANSFORMERS_OFFLINE": "1",
            "HF_HUB_DISABLE_PROGRESS_BARS": "1", "PYTHONDONTWRITEBYTECODE": "1",
        })
        script = Path(__file__).with_name("qwen_worker.py")
        self._worker = subprocess.Popen(
            [worker_python, "-B", str(script), "--model-dir", str(directory),
             "--device", device, "--batch-size", str(batch_size)],
            stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=sys.stderr,
            env=environment, bufsize=0,
        )
        try:
            ready = self._read_worker_line()
            if not isinstance(ready, dict) or not isinstance(ready.get("ready"), dict):
                raise EmbeddingError("Qwen worker did not return its model identity")
            self.info = ready["ready"]
            self.max_input_length = int(self.info["max_input_length"])
            self.max_client_batch_size = int(self.info["max_client_batch_size"])
            self._dimension = dimension
            if dimension != self.info["dimension"]:
                raise EmbeddingError("Qwen model config and worker embedding dimensions disagree")
            self._fingerprint = {
                "schema_version": 1, "backend": "qwen-transformers-last-token-v1",
                "model_name": self.info["served_model_name"], "model_revision": revision,
                "artifact_sha256": artifact_hash, "pooling": "last_token",
                "dimension": dimension, "dtype": self.info["model_dtype"], "normalize": True,
                "torch_version": self.info["torch_version"],
                "transformers_version": self.info["transformers_version"],
                "device_type": self.info["device"],
            }
            self._configure_local_tokenizer(directory)
            self.embed_texts(["theorem identity (a : α) : a = a := by rfl"])
        except BaseException:
            self.close()
            raise

    def _configure_local_tokenizer(self, directory: Path) -> None:
        """Use Rust tokenization only after exact backend identity is verified.

        Python environments without the optional ``tokenizers`` package keep
        the worker IPC path. This resource choice does not change model identity
        or the cached embeddings. No torch/transformers import occurs here.
        """
        expected = self.info.get("tokenizer_backend_sha256")
        if not expected:
            return
        try:
            from tokenizers import Tokenizer
        except ImportError:
            return
        tokenizer = Tokenizer.from_file(str(directory / "tokenizer.json"))
        canonical = json.dumps(
            json.loads(tokenizer.to_str()), sort_keys=True,
            separators=(",", ":"), ensure_ascii=False,
        ).encode("utf-8")
        if hashlib.sha256(canonical).hexdigest() != expected:
            raise EmbeddingError("Local tokenizer backend differs from the Qwen worker tokenizer")
        tokenizer.no_padding()
        tokenizer.no_truncation()
        self._local_tokenizer = tokenizer

    @property
    def supports_parallel_preparation(self) -> bool:
        return self._local_tokenizer is not None

    def _read_worker_line(self) -> Any:
        import selectors
        import time
        deadline = time.monotonic() + self.timeout
        stdout = self._worker.stdout
        assert stdout is not None
        with selectors.DefaultSelector() as selector:
            selector.register(stdout, selectors.EVENT_READ)
            while b"\n" not in self._stdout_buffer:
                remaining = deadline - time.monotonic()
                if remaining <= 0 or not selector.select(remaining):
                    raise EmbeddingError("Qwen embedding worker timed out")
                block = os.read(stdout.fileno(), 65536)
                if not block:
                    raise EmbeddingError("Qwen embedding worker exited before returning a result")
                self._stdout_buffer += block
        line, self._stdout_buffer = self._stdout_buffer.split(b"\n", 1)
        try:
            return json.loads(line)
        except ValueError as exc:
            raise EmbeddingError("Qwen worker returned malformed JSON") from exc

    def _request(self, path: str, payload: Any = None) -> Any:
        # Preparation uses an independent local tokenizer. Serializing the GPU
        # channel also protects it from accidental concurrent query callers.
        with self._request_lock:
            return self._worker_request(path, payload)

    def _worker_request(self, path: str, payload: Any = None) -> Any:
        if self._worker.poll() is not None or self._worker.stdin is None:
            raise EmbeddingError("Qwen embedding worker is no longer running")
        try:
            self._worker.stdin.write(json.dumps({"path": path, "payload": payload}).encode() + b"\n")
            self._worker.stdin.flush()
            response = self._read_worker_line()
        except (OSError, BrokenPipeError) as exc:
            self.close()
            raise EmbeddingError("Qwen embedding worker connection failed") from exc
        except EmbeddingError:
            self.close()
            raise
        if not isinstance(response, dict):
            raise EmbeddingError("Qwen embedding worker returned a malformed response")
        if "error" in response or "result" not in response:
            raise EmbeddingError("Qwen embedding worker failed: " + str(response.get("error")))
        return response["result"]

    def token_counts(self, texts: Sequence[str]) -> list[int]:
        if isinstance(texts, str) or any(not isinstance(text, str) for text in texts):
            raise TypeError("Tokenization inputs must be a sequence of strings")
        if not texts:
            return []
        if self._local_tokenizer is not None:
            return [len(row.ids) for row in self._local_tokenizer.encode_batch(
                list(texts), add_special_tokens=True,
            )]
        result = self._request("/tokenize", {"inputs": list(texts)})
        counts = result.get("counts") if isinstance(result, dict) else None
        if not isinstance(counts, list) or len(counts) != len(texts) or any(
            isinstance(count, bool) or not isinstance(count, int) or count < 1 for count in counts
        ):
            raise EmbeddingError("Qwen worker returned malformed token counts")
        return counts

    def close(self) -> None:
        worker = getattr(self, "_worker", None)
        if worker is None:
            return
        if worker.poll() is None:
            worker.terminate()
            try:
                worker.wait(timeout=10)
            except subprocess.TimeoutExpired:
                worker.kill()
                worker.wait(timeout=5)
        for stream in (worker.stdin, worker.stdout):
            if stream:
                stream.close()

    def __enter__(self) -> "QwenEmbeddingClient":
        return self

    def __exit__(self, *_: Any) -> None:
        self.close()
