"""Hash the mathematical inputs, including the dirty tree, rather than Git HEAD."""

from __future__ import annotations

import hashlib
import json
from pathlib import Path


def source_manifest(root: Path) -> dict:
    root = root.resolve()
    paths = [p for folder in ("OTSelector", "vendor")
             for p in (root / folder).rglob("*.lean") if p.is_file()]
    paths.extend(root.glob("*.lean"))
    paths.extend(root / name for name in
                 ("lean-toolchain", "lakefile.toml", "lake-manifest.json"))
    sources = {str(p.relative_to(root)): hashlib.sha256(p.read_bytes()).hexdigest()
               for p in sorted(set(paths)) if p.is_file()}
    lake = json.loads((root / "lake-manifest.json").read_text())
    revision = next((p.get("rev") for p in lake.get("packages", [])
                     if p.get("name") == "mathlib"), None)
    manifest = {"sources": sources, "toolchain": (root / "lean-toolchain").read_text().strip(),
                "mathlib_revision": revision}
    encoded = json.dumps(manifest, ensure_ascii=False, sort_keys=True, separators=(",", ":"))
    manifest["content_hash"] = hashlib.sha256(encoded.encode()).hexdigest()
    # Location is metadata, not part of the mathematical content identity.
    manifest["project_root"] = str(root)
    return manifest


def save_json(path: Path, value: object) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    temporary = path.with_suffix(path.suffix + ".tmp")
    temporary.write_text(json.dumps(value, ensure_ascii=False, indent=2) + "\n")
    temporary.replace(path)
