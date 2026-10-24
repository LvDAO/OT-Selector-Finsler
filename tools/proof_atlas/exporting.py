"""Native, sharded Lean extraction with resumable parts and atomic publication."""

from concurrent.futures import ThreadPoolExecutor, as_completed
import fcntl
import hashlib
import json
import os
from pathlib import Path
import subprocess
import uuid

from .manifest import save_json, source_manifest


def _hash(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def native_extractor(project_root, data_dir):
    """Compile once for the exact extractor source and Lean toolchain."""
    project_root, data_dir = Path(project_root).resolve(), Path(data_dir).resolve()
    script = Path(__file__).with_name("lean") / "ProofAtlas.lean"
    source_hash, toolchain_hash = _hash(script), _hash(project_root / "lean-toolchain")
    binary = data_dir / "bin" / f"proof-atlas-{source_hash[:16]}-{toolchain_hash[:12]}"
    binary.parent.mkdir(parents=True, exist_ok=True)
    with binary.with_suffix(".lock").open("a") as lock:
        fcntl.flock(lock, fcntl.LOCK_EX)
        if binary.is_file():
            return binary
        c_source = binary.with_suffix(".c")
        pending = binary.with_suffix(f".{os.getpid()}.pending")
        try:
            subprocess.run(["lake", "env", "lean", "-c", str(c_source), str(script)],
                           cwd=project_root, check=True)
            subprocess.run(["lake", "env", "leanc", "-O3", "-rdynamic", "-o", str(pending), str(c_source)],
                           cwd=project_root, check=True)
            if _hash(script) != source_hash or _hash(project_root / "lean-toolchain") != toolchain_hash:
                raise ValueError("extractor source or Lean toolchain changed during native compilation")
            pending.replace(binary)
        finally:
            pending.unlink(missing_ok=True)
    return binary


def run_extract(project_root, data_dir, command, output, extra):
    binary = native_extractor(project_root, data_dir)
    output = Path(output)
    output.parent.mkdir(parents=True, exist_ok=True)
    return subprocess.run(["lake", "env", str(binary), command, "--output", str(output), *extra],
                          cwd=project_root, check=True)


def _read(path):
    return json.loads(Path(path).read_text(encoding="utf-8"))


def _summary(path):
    with Path(path).open("rb") as stream:
        stream.seek(max(0, Path(path).stat().st_size - 32768))
        lines = stream.read().splitlines()
    try:
        summary = json.loads(lines[-1])
    except (ValueError, IndexError) as exc:
        raise ValueError(f"{path}: missing complete EOF summary") from exc
    if not isinstance(summary, dict) or summary.get("record_type") != "summary" or summary.get("complete") is not True:
        raise ValueError(f"{path}: missing complete EOF summary")
    return summary


def _validate_part(path, count, index):
    summary = _summary(path)
    with Path(path).open(encoding="utf-8") as stream:
        manifest = json.loads(stream.readline())
    if manifest.get("record_type") != "manifest":
        raise ValueError(f"{path}: first record must be a manifest")
    for record in (manifest, summary):
        if record.get("shard_count") != count or record.get("shard_index") != index:
            raise ValueError(f"{path}: shard identity does not match {index}/{count}")
    if summary.get("failures", 0) != 0 or summary.get("scope_complete", True) is not True:
        raise ValueError(f"{path}: shard scope is incomplete")
    return manifest, summary


def _merge(parts, output, manifest, module, triads, jobs):
    """Stream parts in shard order; keep only names and external stubs in memory."""
    output = Path(output)
    temporary = output.with_name(output.name + ".merging-" + uuid.uuid4().hex)
    own, triad_names, external = set(), set(), {}
    summaries, first_manifest = [], None
    counts = {"declarations": 0, "triads": 0, "fragments": 0, "diagnostics": 0}
    try:
        with temporary.open("w", encoding="utf-8") as target:
            for index, part in enumerate(parts):
                part_manifest, summary = _validate_part(part, jobs, index)
                summaries.append(summary)
                if first_manifest is None:
                    first_manifest = part_manifest
                    combined = {**part_manifest, "shard_index": None, "shard_count": jobs,
                                "export_scope": "full_project" if module == "OTSelector" else "module_selection",
                                "scope": "full_project" if module == "OTSelector" else "module_selection",
                                "source_manifest": manifest, "merged_shards": jobs,
                                "selection": {"module": module, "triads": triads}}
                    target.write(json.dumps(combined, ensure_ascii=False, separators=(",", ":")) + "\n")
                else:
                    for key in ("schema_version", "ast_encoding", "lean_version", "imports", "proof_budget", "partition_rule"):
                        if part_manifest.get(key) != first_manifest.get(key):
                            raise ValueError(f"{part}: incompatible shard manifest field {key}")
                local_owned = local_triads = 0
                with Path(part).open(encoding="utf-8") as source:
                    for line_number, line in enumerate(source, 1):
                        if not line.strip():
                            continue
                        record = json.loads(line)
                        kind = record.get("record_type")
                        if kind in ("manifest", "summary"):
                            continue
                        if kind == "declaration":
                            name = record.get("name")
                            if not isinstance(name, str) or not name:
                                raise ValueError(f"{part}:{line_number}: missing declaration name")
                            if record.get("external"):
                                previous = external.setdefault(name, record)
                                if previous != record:
                                    raise ValueError(f"{part}:{line_number}: conflicting external stub {name}")
                                continue
                            if name in own:
                                raise ValueError(f"duplicate owned declaration across shards: {name}")
                            own.add(name)
                            counts["declarations"] += 1
                            local_owned += 1
                        elif kind == "triad":
                            name = record.get("declaration")
                            if name in triad_names:
                                raise ValueError(f"duplicate owned proof triad: {name}")
                            triad_names.add(name)
                            counts["triads"] += 1
                            local_triads += 1
                        elif kind == "proof_fragment":
                            counts["fragments"] += 1
                        elif kind == "diagnostic":
                            counts["diagnostics"] += 1
                            if record.get("severity") == "error":
                                raise ValueError(f"{part}:{line_number}: export contains an error diagnostic")
                        else:
                            raise ValueError(f"{part}:{line_number}: unknown record_type {kind!r}")
                        target.write(line if line.endswith("\n") else line + "\n")
                if summary.get("declarations") != local_owned or summary.get("triads") != local_triads:
                    raise ValueError(f"{part}: summary does not match emitted declaration/triad records")
                if "owned_count" in summary and summary["owned_count"] != local_owned:
                    raise ValueError(f"{part}: partition owned_count does not match emitted declarations")
            if not triad_names <= own:
                raise ValueError("merged triads include declarations outside the owned partition")
            totals = {summary["project_owned_count"] for summary in summaries if "project_owned_count" in summary}
            if totals and (len(totals) != 1 or next(iter(totals)) != len(own)):
                raise ValueError("merged declarations do not cover the producer's complete project count")
            for name in sorted(external.keys() - own):
                target.write(json.dumps(external[name], ensure_ascii=False, separators=(",", ":")) + "\n")
            summary = {"record_type": "summary", **counts, "external_references": len(external.keys() - own),
                       "owned_count": len(own), "project_owned_count": len(own), "failures": 0,
                       "complete": True, "scope_complete": True, "full_corpus": module == "OTSelector",
                       "export_scope": "full_project" if module == "OTSelector" else "module_selection",
                       "shard_count": jobs, "merged_shards": jobs, "source_summaries": summaries}
            target.write(json.dumps(summary, ensure_ascii=False, separators=(",", ":")) + "\n")
            target.flush()
            os.fsync(target.fileno())
        temporary.replace(output)
        return summary
    finally:
        temporary.unlink(missing_ok=True)


def export_corpus(args, output: Path, module: str, triads: str, jobs: int = 4):
    """Run one writer per hash partition, validate all parts, then publish one corpus.

    The top-level ``export-status.json`` points to per-shard running/complete/error
    receipts. Growing ``*.pending.jsonl`` files are promoted only after the writer
    exits successfully with the matching complete shard summary. No database is
    opened here; an independent importer may tail complete JSONL lines.
    """
    if jobs < 1 or triads not in ("public", "all", "none"):
        raise ValueError("jobs must be positive and triads must be public, all or none")
    project_root, data_dir = Path(args.project_root).resolve(), Path(args.data_dir).resolve()
    output = Path(output)
    output.parent.mkdir(parents=True, exist_ok=True)
    manifest = source_manifest(project_root)
    binary = native_extractor(project_root, data_dir)
    binding = {"content_hash": manifest["content_hash"], "binary": binary.name,
               "module": module, "triads": triads, "jobs": jobs}
    identity = hashlib.sha256(json.dumps(binding, sort_keys=True).encode()).hexdigest()[:24]
    part_directory = data_dir / "export-parts" / identity
    part_directory.mkdir(parents=True, exist_ok=True)
    top_status = data_dir / "export-status.json"
    status = {"state": "exporting", "part_directory": str(part_directory), "jobs": jobs,
              "output": str(output), "binding": binding}
    save_json(top_status, status)

    def writer(index):
        part = part_directory / f"part-{index:05d}.jsonl"
        pending = part.with_suffix(".pending.jsonl")
        receipt = part.with_suffix(".status.json")
        base = {"shard_index": index, "shard_count": jobs, "binding": binding,
                "pending": str(pending), "output": str(part)}
        try:
            if part.is_file() and receipt.is_file() and _read(receipt).get("binding") == binding:
                _, summary = _validate_part(part, jobs, index)
                save_json(receipt, {**base, "state": "complete", "returncode": 0, "reused": True,
                                    "summary": summary})
                return part
            save_json(receipt, {**base, "state": "running"})
            subprocess.run(["lake", "env", str(binary), "export", "--output", str(pending),
                            "--module", module, "--triads", triads,
                            "--shard-count", str(jobs), "--shard-index", str(index)],
                           cwd=project_root, check=True)
            _, summary = _validate_part(pending, jobs, index)
            pending.replace(part)
            save_json(receipt, {**base, "state": "complete", "returncode": 0, "reused": False,
                                "summary": summary})
            return part
        except BaseException as exc:
            save_json(receipt, {**base, "state": "error", "error": str(exc),
                                "returncode": getattr(exc, "returncode", None)})
            raise

    try:
        parts = [None] * jobs
        with ThreadPoolExecutor(max_workers=jobs) as pool:
            futures = {pool.submit(writer, index): index for index in range(jobs)}
            for future in as_completed(futures):
                parts[futures[future]] = future.result()
        if source_manifest(project_root)["content_hash"] != manifest["content_hash"]:
            raise ValueError("mathematical sources changed while exporting shards")
        save_json(top_status, {**status, "state": "merging"})
        summary = _merge(parts, output, manifest, module, triads, jobs)
        save_json(top_status, {**status, "state": "complete", "summary": summary})
        return {"path": str(output), "part_directory": str(part_directory), "summary": summary,
                "source_manifest_hash": manifest["content_hash"]}
    except BaseException as exc:
        save_json(top_status, {**status, "state": "error", "error": str(exc)})
        raise
