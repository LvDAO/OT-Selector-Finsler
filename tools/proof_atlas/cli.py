"""Command-line entry point; generated databases and model state stay outside Git."""

from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys

from .manifest import save_json, source_manifest
from .retrieval import context_packet, query_text, search, transfer
from .store import Store
from .structure import anti_unify, compare_structure, exact_clusters
from .verify import elaborate_state, load_patterns, verify_candidate

ROOT = Path(__file__).resolve().parents[2]


def _emit(value):
    print(json.dumps(value, ensure_ascii=False, indent=2))


def _compact(value):
    """Keep typed Lean text and source; raw expression DAGs remain in `show`."""
    if isinstance(value, list):
        return [_compact(item) for item in value]
    if isinstance(value, dict):
        return {key: _compact(item) for key, item in value.items()
                if key not in {"expr", "type_expr", "target_expr", "value_expr", "assignment_expr"}}
    return value


def _read(path):
    return json.loads(Path(path).read_text(encoding="utf-8"))


def _progress(message):
    print(message, file=sys.stderr, flush=True)


def _stats(store):
    result = store.stats()
    result.get("snapshot", {}).pop("manifest", None)
    return result


def _completed(path):
    """An EOF summary distinguishes a finished export from an interrupted file."""
    with path.open("rb") as stream:
        stream.seek(max(0, path.stat().st_size - 16384))
        lines = stream.read().splitlines()
    try:
        last = json.loads(lines[-1])
    except (ValueError, IndexError):
        return False
    return isinstance(last, dict) and last.get("record_type") == "summary" and last.get("complete") is True


def _client(args):
    from .embedding import QwenEmbeddingClient, TEIEmbeddingClient
    if args.embedding == "qwen":
        options = {"model_dir": args.model_dir, "device": args.device}
        if getattr(args, "worker_python", None):
            options["worker_python"] = args.worker_python
        if hasattr(args, "batch_size"):
            options["batch_size"] = args.batch_size
        return QwenEmbeddingClient(**options)
    if args.embedding == "tei":
        return TEIEmbeddingClient(url=args.embedding_url, model_dir=args.model_dir)
    return None


def _extract(args, command, output, extra):
    from .exporting import run_extract
    _progress("Lean extraction: " + command)
    run_extract(args.project_root, args.data_dir, command, output, extra)


def _current(store, args):
    status = store.snapshot_status(source_manifest(args.project_root))
    if status.get("stale") is not False:
        raise ValueError("index is empty, unbound or stale; run build for the current source tree")
    return {k: v for k, v in status.items() if k != "manifest"}


def _embed(args, store):
    if args.embedding == "none":
        return {"status": "disabled"}
    from .vectors import VectorIndex
    client = _client(args)
    try:
        _progress("Building semantic views with " + args.embedding + "; completed batches are resumable")
        return VectorIndex(args.data_dir).build(
            store, client, views=args.views, batch_size=args.batch_size,
            include_internal=args.include_internal, chunk_tokens=args.chunk_tokens)
    finally:
        if hasattr(client, "close"):
            client.close()


def _query(args, store, state=None):
    _current(store, args)
    client = _client(args) if args.semantic else None
    try:
        if client:
            from .vectors import VectorIndex
            index = VectorIndex(args.data_dir)
        else:
            index = None
        text = query_text(state) if state is not None else args.query
        return search(store, text, limit=args.limit, view=args.view, module=args.module,
                      namespace=args.namespace, vector_index=index, client=client)
    finally:
        if hasattr(client, "close"):
            client.close()


def dispatch(args):
    args.project_root = args.project_root.resolve()
    args.data_dir = args.data_dir.resolve()
    if args.data_dir == args.project_root or args.project_root in args.data_dir.parents:
        raise ValueError("choose --data-dir outside the repository for generated indexes")
    if args.command == "verify":
        return verify_candidate(_read(args.request), args.project_root, timeout_seconds=args.timeout)
    if args.command == "state":
        return elaborate_state(_read(args.request), args.project_root, timeout_seconds=args.timeout)
    if args.command == "patterns":
        patterns = load_patterns()
        return next(p for p in patterns if p["id"] == args.id) if args.id else patterns
    if args.command == "match" and args.pattern:
        return transfer(None, _read(args.state), pattern_id=args.pattern,
                        check=args.check, root=args.project_root, timeout=args.timeout)
    args.data_dir.mkdir(parents=True, exist_ok=True)
    with Store(args.data_dir / "atlas.sqlite3") as store:
        if args.command == "build":
            before = source_manifest(args.project_root)
            output = args.data_dir / "export.jsonl"
            receipt = args.data_dir / "export.sources.json"
            selection = {"module": args.module, "triads": args.triads,
                         "extractor_sha256": hashlib.sha256(
                             (Path(__file__).with_name("lean") / "ProofAtlas.lean").read_bytes()).hexdigest()}
            reusable = (output.is_file() and receipt.is_file() and
                        _read(receipt).get("content_hash") == before["content_hash"] and
                        _read(receipt).get("selection") == selection and _completed(output))
            if args.refresh or not reusable:
                _progress("Compiling the selected library before reading its Lean environment")
                subprocess.run(["lake", "build", args.module], cwd=args.project_root, check=True)
                temporary = args.data_dir / "export.pending.jsonl"
                if args.jobs == 1:
                    _extract(args, "export", temporary, ["--module", args.module, "--triads", args.triads])
                else:
                    from .exporting import export_corpus
                    export_corpus(args, temporary, args.module, args.triads, jobs=args.jobs)
                after = source_manifest(args.project_root)
                if after["content_hash"] != before["content_hash"]:
                    raise ValueError("mathematical sources changed during extraction; rerun build")
                if not _completed(temporary):
                    raise ValueError("export is missing a complete summary")
                temporary.replace(output)
                save_json(receipt, {**before, "selection": selection})
            else:
                _progress("Reusing completed export for this exact source snapshot")
            imported = store.import_jsonl(output, source_manifest=before, replace=True)
            # Import prior traces only when they are bound to this exact source snapshot.
            for folder in ("details", "traces"):
                for cached in sorted((args.data_dir / folder).glob("*.jsonl")):
                    binding = cached.with_suffix(".sources.json")
                    if (binding.exists() and _completed(cached) and
                            _read(binding).get("content_hash") == before["content_hash"]):
                        store.import_jsonl(cached, source_manifest=before)
            return {"import": imported, "stats": _stats(store), "embedding": _embed(args, store)}
        if args.command == "trace":
            _current(store, args)
            before = source_manifest(args.project_root)
            source = args.file.resolve()
            source.relative_to(args.project_root)
            cache_key = str(source.relative_to(args.project_root)) + ":" + str(args.name or "")
            output = args.data_dir / "traces" / (source.stem + "-" +
                     hashlib.sha256(cache_key.encode()).hexdigest()[:16] + ".jsonl")
            pending = output.with_suffix(".pending.jsonl")
            extra = ["--file", str(source), "--module",
                     str(source.relative_to(args.project_root).with_suffix("")).replace(os.sep, ".")]
            if args.name:
                extra.extend(["--name", args.name])
            _extract(args, "trace", pending, extra)
            after = source_manifest(args.project_root)
            if before["content_hash"] != after["content_hash"]:
                raise ValueError("sources changed during trace extraction; rerun trace")
            if not _completed(pending):
                raise ValueError("trace is missing a complete summary")
            pending.replace(output)
            save_json(output.with_suffix(".sources.json"), before)
            return store.import_jsonl(output, source_manifest=before)
        if args.command == "detail":
            _current(store, args)
            manifest = source_manifest(args.project_root)
            key = hashlib.sha256((args.module + ":" + args.name).encode()).hexdigest()[:20]
            output = args.data_dir / "details" / (key + ".jsonl")
            pending = output.with_suffix(".pending.jsonl")
            _extract(args, "detail", pending, ["--module", args.module, "--name", args.name,
                                               "--proof-budget", str(args.proof_budget)])
            if source_manifest(args.project_root)["content_hash"] != manifest["content_hash"]:
                raise ValueError("sources changed during extraction")
            if not _completed(pending):
                raise ValueError("detail is missing a complete summary")
            pending.replace(output)
            save_json(output.with_suffix(".sources.json"), manifest)
            return store.import_jsonl(output, source_manifest=manifest)
        if args.command == "embed":
            _current(store, args)
            return _embed(args, store)
        if args.command == "status":
            from .vectors import VectorIndex
            snapshot = store.snapshot_status(source_manifest(args.project_root))
            snapshot.pop("manifest", None)
            return {"snapshot": snapshot, "stats": _stats(store),
                    "vectors": VectorIndex(args.data_dir).status(store)}
        if args.command in ("search", "context"):
            state = _read(args.state) if args.state else None
            if state is not None:
                query_text(state)  # Validate before accessing optional typed fields.
            if args.command == "context" and state is not None and not state.get("target_expr"):
                typed = elaborate_state(state, args.project_root)
                if typed.get("status") != "elaborated":
                    raise ValueError("Lean could not elaborate the new goal: " + str(typed.get("reason", typed)))
                state = {**state, **typed}
            hits = _query(args, store, state)
            if args.command == "context":
                packet = context_packet(store, hits, state=state, limit=args.limit)
                return _compact(packet) if args.compact else packet
            return hits
        _current(store, args)
        if args.command == "show":
            if args.fragment:
                from .structure import step_effect
                fragment = store.get_fragment(args.fragment)
                if fragment is None:
                    raise ValueError("fragment not found")
                return {"fragment": fragment, "effect": step_effect(fragment)}
            return {"declaration": store.get_decl(args.name), "triad": store.get_triad(args.name),
                    "proof_source": store.get_proof_text(args.name)}
        if args.command == "graph":
            return store.dag(args.name, direction=args.direction, depth=args.depth,
                             edge_kind=args.edge_kind, limit=args.limit)
        if args.command == "duplicates":
            if not (args.structural or args.proofs):
                return {"candidates": store.duplicate_candidates(limit=args.limit, namespace=args.namespace),
                        "meaning": "identical complete contracts; inspect proof syntax before consolidation"}
            records = (json.loads(row[0]) for row in store.conn.execute("SELECT payload_json FROM triads"))
            result = exact_clusters(records, field="proof_skeleton.expr" if args.proofs else "type_expr",
                                    binders_field="ordered_telescope" if args.proofs else "__closed_type__")
            result["clusters"] = result["clusters"][:args.limit]
            return result
        if args.command == "compare":
            left, right = store.get_triad(args.left), store.get_triad(args.right)
            if left is None or right is None:
                raise ValueError("both declarations need triads; run detail first")
            params = {"left_binders": left["ordered_telescope"],
                      "right_binders": right["ordered_telescope"]}
            function = anti_unify if args.generalize else compare_structure
            return function(left["target_expr"], right["target_expr"], **params)
        if args.command == "match":
            return transfer(store, _read(args.state), pattern_id=args.pattern, declaration=args.name,
                            check=args.check, root=args.project_root, timeout=args.timeout)
        if args.command == "serve":
            from .web import serve
            return serve(args, store)
        raise ValueError("unknown command")


def parser():
    p = argparse.ArgumentParser(description="Local Lean proof triads, dependency graph and checked retrieval")
    subs = p.add_subparsers(dest="command", required=True)

    def command(name, help):
        cmd = subs.add_parser(name, help=help)
        cmd.add_argument("--project-root", type=Path, default=ROOT)
        cmd.add_argument("--data-dir", type=Path,
                         default=Path(os.getenv("PROOF_ATLAS_DATA", str(ROOT.parent / "otselector-index"))))
        return cmd

    def embedding(cmd, none=False):
        cmd.add_argument("--embedding", choices=["qwen", "tei"] + (["none"] if none else []), default="qwen")
        cmd.add_argument("--model-dir")
        cmd.add_argument("--embedding-url")
        cmd.add_argument("--device", default="auto")
        cmd.add_argument("--worker-python", default=os.getenv("PROOF_ATLAS_WORKER_PYTHON"),
                         help="Qwen worker Python with torch/transformers installed")

    b = command("build", "Export compiled declarations, import graph/triads and embed locally")
    b.add_argument("--module", default="OTSelector")
    b.add_argument("--triads", choices=["public", "all", "none"], default="public")
    b.add_argument("--refresh", action="store_true")
    b.add_argument("--jobs", type=int, default=4, help="native extraction workers; reduce for limited memory")
    for cmd in (b, command("embed", "Resume or rebuild the source/model-bound semantic index")):
        embedding(cmd, none=True)
        cmd.add_argument("--views", nargs="+")
        cmd.add_argument("--batch-size", type=int, default=16)
        cmd.add_argument("--chunk-tokens", type=int, default=1024)
        cmd.add_argument("--include-internal", action="store_true")
    for name in ("search", "context"):
        cmd = command(name, "Retrieve proof views" if name == "search" else "Produce a structured RAG packet")
        cmd.add_argument("query", nargs="?", default="")
        cmd.add_argument("--state", type=Path, help="JSON with context/goal (and optional typed AST)")
        cmd.add_argument("--limit", type=int, default=10)
        cmd.add_argument("--view", choices=["statement", "conditions", "objects", "proof_detail", "full_proof", "proof_state"])
        cmd.add_argument("--module")
        cmd.add_argument("--namespace")
        cmd.add_argument("--semantic", action="store_true")
        if name == "context":
            cmd.add_argument("--compact", action="store_true", help="omit raw ASTs from the RAG packet")
        embedding(cmd)
    command("status", "Show graph, trace, source and vector coverage")
    s = command("show", "Read a complete proof triad or a traced fragment")
    s.add_argument("name", nargs="?", default="")
    s.add_argument("--fragment", type=int)
    t = command("trace", "Replay a source file and index real intermediate proof states")
    t.add_argument("file", type=Path)
    t.add_argument("--name")
    d = command("detail", "Extract a triad for any imported declaration")
    d.add_argument("name")
    d.add_argument("--module", default="OTSelector")
    d.add_argument("--proof-budget", type=int, default=2000,
                   help="raw proof DAG node budget; 0 extracts the complete expression")
    g = command("graph", "Query a bounded dependency DAG with recursive components condensed")
    g.add_argument("name")
    g.add_argument("--direction", choices=["upstream", "downstream"], default="upstream")
    g.add_argument("--edge-kind", choices=["type_ref", "proof_ref"])
    g.add_argument("--depth", type=int, default=1)
    g.add_argument("--limit", type=int, default=100)
    du = command("duplicates", "Find equal contracts or alpha-equivalent proof syntax")
    du.add_argument("--limit", type=int, default=20)
    du.add_argument("--namespace")
    du.add_argument("--structural", action="store_true")
    du.add_argument("--proofs", action="store_true")
    co = command("compare", "Compare typed expression structure or propose a limited common pattern")
    co.add_argument("left")
    co.add_argument("right")
    co.add_argument("--generalize", action="store_true")
    pa = command("patterns", "Read the curated conditions/objects/proof_detail pattern library")
    pa.add_argument("id", nargs="?")
    m = command("match", "Map a pattern or apply a theorem to a new goal, optionally checked by Lean")
    m.add_argument("state", type=Path)
    choice = m.add_mutually_exclusive_group(required=True)
    choice.add_argument("--pattern")
    choice.add_argument("--name")
    m.add_argument("--check", action="store_true")
    m.add_argument("--timeout", type=float, default=60)
    v = command("verify", "Run an explicit proof trial; report complete/partial/rejected")
    v.add_argument("request", type=Path)
    v.add_argument("--timeout", type=float, default=60)
    st = command("state", "Elaborate a new goal into a typed telescope and expression DAG")
    st.add_argument("request", type=Path)
    st.add_argument("--timeout", type=float, default=60)
    server = command("serve", "Serve the read-only local explorer on loopback")
    server.add_argument("--port", type=int, default=8765)
    server.add_argument("--semantic", action="store_true")
    embedding(server)
    return p


def main(argv=None):
    args = parser().parse_args(argv)
    try:
        _emit(dispatch(args))
        return 0
    except (ValueError, OSError, RuntimeError, subprocess.SubprocessError, StopIteration) as exc:
        print(f"proof-atlas: {exc}", file=sys.stderr)
        return 2
