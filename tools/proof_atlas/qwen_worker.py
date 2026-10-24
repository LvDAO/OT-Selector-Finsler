"""Offline Qwen base-model embedding worker; stdout is JSONL protocol only."""
from __future__ import annotations

import argparse
import hashlib
import json
import os
import sys


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--model-dir", required=True)
    parser.add_argument("--device", default="auto", choices=("auto", "cuda", "cpu"))
    parser.add_argument("--batch-size", type=int, default=16)
    args = parser.parse_args()
    os.environ["HF_HUB_OFFLINE"] = "1"
    os.environ["TRANSFORMERS_OFFLINE"] = "1"
    os.environ["HF_HUB_DISABLE_PROGRESS_BARS"] = "1"
    import torch
    import transformers
    from transformers import AutoModel, AutoTokenizer
    transformers.logging.set_verbosity_error()
    torch.set_grad_enabled(False)
    device = "cuda" if args.device == "auto" and torch.cuda.is_available() else args.device
    if device == "auto":
        device = "cpu"
    if device == "cuda" and not torch.cuda.is_available():
        raise RuntimeError("CUDA was requested but is unavailable")
    dtype = torch.bfloat16 if device == "cuda" else torch.float32
    tokenizer = AutoTokenizer.from_pretrained(
        args.model_dir, local_files_only=True, trust_remote_code=False, padding_side="left",
    )
    tokenizer_backend_sha256 = hashlib.sha256(json.dumps(
        json.loads(tokenizer.backend_tokenizer.to_str()),
        sort_keys=True, separators=(",", ":"), ensure_ascii=False,
    ).encode("utf-8")).hexdigest()
    if tokenizer.pad_token_id is None:
        tokenizer.pad_token = tokenizer.eos_token
    model = AutoModel.from_pretrained(
        args.model_dir, local_files_only=True, trust_remote_code=False,
        torch_dtype=dtype, attn_implementation="sdpa",
    ).to(device).eval()
    model.config.use_cache = False
    limit = int(model.config.max_position_embeddings)
    info = {
        "model_id": args.model_dir,
        "tokenizer_backend_sha256": tokenizer_backend_sha256,
        "served_model_name": "Qwen/Qwen3-Embedding-0.6B",
        "model_sha": getattr(model.config, "_commit_hash", None),
        "model_dtype": str(dtype).removeprefix("torch."),
        "model_type": {"embedding": {"pooling": "last_token"}},
        "max_input_length": limit,
        "max_client_batch_size": args.batch_size,
        "dimension": int(model.config.hidden_size),
        "device": device,
        "torch_version": torch.__version__,
        "transformers_version": transformers.__version__,
    }
    print(json.dumps({"ready": info}), flush=True)
    for line in sys.stdin:
        try:
            request = json.loads(line)
            path, payload = request["path"], request.get("payload")
            if path == "/info":
                result = info
            elif path == "/tokenize":
                rows = tokenizer(payload["inputs"], add_special_tokens=True, truncation=False)["input_ids"]
                result = {"counts": [len(row) for row in rows]}
                if payload.get("return_ids") is True:
                    result["input_ids"] = rows
            elif path == "/embed":
                if payload.get("truncate") is not False or payload.get("normalize") is not True:
                    raise ValueError("Embedding protocol requires truncate:false and normalize:true")
                inputs = payload["inputs"]
                if not inputs or len(inputs) > args.batch_size:
                    raise ValueError("Embedding request violates the worker batch limit")
                tokens = tokenizer(
                    inputs, padding=True, truncation=False, return_tensors="pt",
                )
                if int(tokens["attention_mask"].sum(1).max()) > limit:
                    raise ValueError("Embedding input exceeds the model token limit")
                tokens = tokens.to(device)
                with torch.inference_mode():
                    hidden = model(**tokens, use_cache=False, return_dict=True).last_hidden_state
                    mask = tokens["attention_mask"]
                    positions = torch.arange(hidden.shape[1], device=hidden.device)
                    last = positions.expand_as(mask).masked_fill(~mask.bool(), -1).max(1).values
                    pooled = hidden[torch.arange(hidden.shape[0], device=hidden.device), last]
                    result = torch.nn.functional.normalize(pooled.float(), p=2, dim=-1).cpu().tolist()
            elif path == "/close":
                print(json.dumps({"result": None}), flush=True)
                break
            else:
                raise ValueError("Unknown embedding worker command")
            print(json.dumps({"result": result}, allow_nan=False), flush=True)
        except Exception as exc:
            print(json.dumps({"error": f"{type(exc).__name__}: {exc}"}), flush=True)


if __name__ == "__main__":
    main()
