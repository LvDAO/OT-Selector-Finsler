"""Persistent declaration, proof-triad, reference-graph and lexical indexes.

The SQLite file is a generated artifact; callers choose its location outside the
source repository. JSONL ingestion is transactional and streams edges in batches.
The dependency graph retains recursive edges. ``dag`` condenses only its bounded
display into strongly connected components.
"""

from __future__ import annotations

from collections import defaultdict
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import re
import sqlite3
from typing import Any, Iterator


EDGE_KINDS = {"type_ref": 0, "proof_ref": 1}
VIEW_NAMES = ("conditions", "objects", "proof_detail", "full_proof", "proof_state")


def _json(value: Any) -> str:
    return json.dumps(value, ensure_ascii=False, sort_keys=True, separators=(",", ":"))


def _sha(text: str) -> str:
    return hashlib.sha256(text.encode("utf-8")).hexdigest()


def _manifest_hash(manifest: dict[str, Any]) -> str:
    if manifest.get("content_hash"):
        return str(manifest["content_hash"])
    # Timestamps and Git HEAD are not substitutes for the dirty tree's content.
    content = {key: manifest[key] for key in
               ("sources", "toolchain", "mathlib_revision") if key in manifest}
    return _sha(_json(content))


class Store:
    """A single SQLite index; returned records are JSON-serializable dictionaries."""

    def __init__(self, path: str | Path):
        self.path = Path(path) if str(path) != ":memory:" else None
        if self.path is not None:
            self.path.parent.mkdir(parents=True, exist_ok=True)
        self.conn = sqlite3.connect(str(path), timeout=60)
        self.conn.row_factory = sqlite3.Row
        self.conn.execute("PRAGMA foreign_keys = ON")
        self.conn.execute("PRAGMA journal_mode = WAL")
        self.conn.execute("PRAGMA busy_timeout = 60000")
        self._create_schema()
        self._node_ids: dict[str, int] = {}
        self._source_texts: dict[tuple[str, str], str] = {}

    def close(self) -> None:
        self.conn.close()

    def __enter__(self) -> "Store":
        return self

    def __exit__(self, *exc: Any) -> None:
        self.close()

    def _create_schema(self) -> None:
        version = self.conn.execute("PRAGMA user_version").fetchone()[0]
        if version not in (0, 1):
            raise ValueError(f"unsupported proof-atlas schema version {version}")
        self.conn.executescript("""
            CREATE TABLE IF NOT EXISTS meta (key TEXT PRIMARY KEY, value TEXT NOT NULL);
            CREATE TABLE IF NOT EXISTS snapshots (
                id INTEGER PRIMARY KEY, content_hash TEXT NOT NULL UNIQUE,
                manifest_json TEXT NOT NULL, imported_at TEXT NOT NULL);
            CREATE TABLE IF NOT EXISTS nodes (
                id INTEGER PRIMARY KEY, name TEXT NOT NULL UNIQUE);
            CREATE TABLE IF NOT EXISTS declarations (
                node_id INTEGER PRIMARY KEY REFERENCES nodes(id) ON DELETE CASCADE,
                module TEXT NOT NULL DEFAULT '', namespace TEXT NOT NULL DEFAULT '',
                kind TEXT NOT NULL DEFAULT '', private INTEGER NOT NULL DEFAULT 0,
                internal_detail INTEGER NOT NULL DEFAULT 0, has_range INTEGER NOT NULL DEFAULT 0,
                external INTEGER NOT NULL DEFAULT 0,
                source_path TEXT, source_hash TEXT, signature TEXT NOT NULL,
                type_text TEXT, type_fingerprint TEXT, fingerprint_basis TEXT,
                metadata_json TEXT NOT NULL, snapshot_id INTEGER REFERENCES snapshots(id));
            CREATE INDEX IF NOT EXISTS declarations_module ON declarations(module);
            CREATE INDEX IF NOT EXISTS declarations_namespace ON declarations(namespace);
            CREATE INDEX IF NOT EXISTS declarations_type ON declarations(type_fingerprint);
            CREATE TABLE IF NOT EXISTS edges (
                source_id INTEGER NOT NULL REFERENCES nodes(id) ON DELETE CASCADE,
                target_id INTEGER NOT NULL REFERENCES nodes(id) ON DELETE CASCADE,
                kind INTEGER NOT NULL CHECK(kind IN (0, 1)),
                PRIMARY KEY(source_id, target_id, kind)) WITHOUT ROWID;
            CREATE INDEX IF NOT EXISTS edges_target ON edges(target_id, kind, source_id);
            CREATE TABLE IF NOT EXISTS triads (
                node_id INTEGER PRIMARY KEY REFERENCES nodes(id) ON DELETE CASCADE,
                payload_json TEXT NOT NULL, source_hash TEXT,
                snapshot_id INTEGER REFERENCES snapshots(id));
            CREATE TABLE IF NOT EXISTS fragments (
                id INTEGER PRIMARY KEY,
                node_id INTEGER NOT NULL REFERENCES nodes(id) ON DELETE CASCADE,
                fragment_key TEXT NOT NULL, payload_json TEXT NOT NULL, source_hash TEXT,
                snapshot_id INTEGER REFERENCES snapshots(id), UNIQUE(node_id, fragment_key));
            CREATE TABLE IF NOT EXISTS documents (
                id INTEGER PRIMARY KEY,
                node_id INTEGER NOT NULL REFERENCES nodes(id) ON DELETE CASCADE,
                view TEXT NOT NULL, record_key TEXT NOT NULL DEFAULT '', text TEXT NOT NULL,
                content_hash TEXT NOT NULL, metadata_json TEXT NOT NULL DEFAULT '{}',
                UNIQUE(node_id, view, record_key));
            CREATE VIRTUAL TABLE IF NOT EXISTS documents_fts USING fts5(
                text, content='documents', content_rowid='id', tokenize='unicode61');
            CREATE TRIGGER IF NOT EXISTS documents_ai AFTER INSERT ON documents BEGIN
                INSERT INTO documents_fts(rowid, text) VALUES (new.id, new.text);
            END;
            CREATE TRIGGER IF NOT EXISTS documents_ad AFTER DELETE ON documents BEGIN
                INSERT INTO documents_fts(documents_fts, rowid, text)
                    VALUES ('delete', old.id, old.text);
            END;
            CREATE TRIGGER IF NOT EXISTS documents_au AFTER UPDATE ON documents BEGIN
                INSERT INTO documents_fts(documents_fts, rowid, text)
                    VALUES ('delete', old.id, old.text);
                INSERT INTO documents_fts(rowid, text) VALUES (new.id, new.text);
            END;
            CREATE TABLE IF NOT EXISTS diagnostics (
                id INTEGER PRIMARY KEY, snapshot_id INTEGER REFERENCES snapshots(id),
                payload_json TEXT NOT NULL);
            PRAGMA user_version = 1;
        """)
        if "external" not in {row[1] for row in self.conn.execute("PRAGMA table_info(declarations)")}:
            self.conn.execute("ALTER TABLE declarations ADD COLUMN external INTEGER NOT NULL DEFAULT 0")
            self.conn.commit()

    def _node(self, name: str) -> int:
        if not isinstance(name, str) or not name:
            raise ValueError("declaration names must be nonempty strings")
        if name not in self._node_ids:
            self.conn.execute("INSERT OR IGNORE INTO nodes(name) VALUES (?)", (name,))
            self._node_ids[name] = self.conn.execute(
                "SELECT id FROM nodes WHERE name = ?", (name,)).fetchone()[0]
        return self._node_ids[name]

    def _nodes(self, names: list[str]) -> None:
        missing = list(dict.fromkeys(name for name in names if name not in self._node_ids))
        if any(not isinstance(name, str) or not name for name in missing):
            raise ValueError("dependency names must be nonempty strings")
        self.conn.executemany("INSERT OR IGNORE INTO nodes(name) VALUES (?)",
                              ((name,) for name in missing))
        for start in range(0, len(missing), 500):
            batch = missing[start:start + 500]
            marks = ",".join("?" for _ in batch)
            for row in self.conn.execute(f"SELECT name, id FROM nodes WHERE name IN ({marks})", batch):
                self._node_ids[row["name"]] = row["id"]

    def _snapshot(self, manifest: dict[str, Any]) -> int:
        digest = _manifest_hash(manifest)
        self.conn.execute("""INSERT INTO snapshots(content_hash, manifest_json, imported_at)
            VALUES (?, ?, ?) ON CONFLICT(content_hash) DO UPDATE SET manifest_json=excluded.manifest_json""",
                          (digest, _json(manifest), datetime.now(timezone.utc).isoformat()))
        return self.conn.execute("SELECT id FROM snapshots WHERE content_hash=?", (digest,)).fetchone()[0]

    @staticmethod
    def _source_binding(record: dict[str, Any], manifest: dict[str, Any]) -> tuple[Any, Any]:
        source = record.get("source")
        source = source if isinstance(source, dict) else {}
        module = str(record.get("module") or "")
        path = record.get("source_path") or source.get("file") or source.get("path")
        path = path or (module.replace(".", "/") + ".lean" if module else None)
        digest = record.get("source_hash") or record.get("source_sha256") or source.get("sha256")
        sources = manifest.get("sources", {})
        if isinstance(sources, dict) and path and path not in sources:
            # Vendored packages retain LeanPool/LeanLevy module names.
            matches = [candidate for candidate in sources if candidate.endswith("/" + path)]
            if len(matches) == 1:
                path = matches[0]
        if digest is None and isinstance(sources, dict) and path in sources:
            value = sources[path]
            digest = value.get("sha256", value.get("hash")) if isinstance(value, dict) else value
        return path, digest

    def _document(self, node: int, view: str, text: str, record_key: str = "",
                  metadata: dict[str, Any] | None = None) -> None:
        self.conn.execute("""INSERT INTO documents(node_id,view,record_key,text,content_hash,metadata_json)
            VALUES (?,?,?,?,?,?) ON CONFLICT(node_id,view,record_key) DO UPDATE SET
            text=excluded.text,content_hash=excluded.content_hash,metadata_json=excluded.metadata_json
            WHERE documents.content_hash != excluded.content_hash
               OR documents.metadata_json != excluded.metadata_json""",
                          (node, view, record_key, text, _sha(text), _json(metadata or {})))

    def _declaration(self, record: dict[str, Any], manifest: dict[str, Any], snapshot: int) -> None:
        name = record.get("name", record.get("declaration"))
        node = self._node(name)
        module = record.get("module") or ""
        namespace = record.get("namespace", name.rpartition(".")[0])
        path, source_hash = self._source_binding(record, manifest)
        metadata = {k: v for k, v in record.items() if k not in
                    ("type_dependencies", "proof_dependencies", "type_refs", "proof_refs")}
        signature = _sha(_json({"metadata": metadata, "source_hash": source_hash}))
        old = self.conn.execute("SELECT signature,external FROM declarations WHERE node_id=?", (node,)).fetchone()
        # A scoped detail export labels its unselected dependencies as stubs.
        # Such a stub must not erase previously imported complete metadata.
        if record.get("external") and old is not None and not old["external"]:
            return
        if old is not None and old[0] != signature:
            self.conn.execute("DELETE FROM triads WHERE node_id=?", (node,))
            self.conn.execute("DELETE FROM fragments WHERE node_id=?", (node,))
            self.conn.execute("DELETE FROM documents WHERE node_id=?", (node,))
            self.conn.execute("""UPDATE declarations SET type_text=NULL,type_fingerprint=NULL,
                fingerprint_basis=NULL WHERE node_id=?""", (node,))
        type_text = record.get("type_text", record.get("type"))
        fingerprint = record.get("type_fingerprint")
        basis = "exported_type_fingerprint" if fingerprint else None
        if not fingerprint and type_text:
            fingerprint, basis = _sha(" ".join(type_text.split())), "full_type_text"
        self.conn.execute("""INSERT INTO declarations
            (node_id,module,namespace,kind,private,internal_detail,has_range,source_path,source_hash,
             signature,type_text,type_fingerprint,fingerprint_basis,metadata_json,snapshot_id,external)
            VALUES (?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?) ON CONFLICT(node_id) DO UPDATE SET
            module=excluded.module,namespace=excluded.namespace,kind=excluded.kind,private=excluded.private,
            internal_detail=excluded.internal_detail,has_range=excluded.has_range,
            source_path=excluded.source_path,source_hash=excluded.source_hash,signature=excluded.signature,
            type_text=COALESCE(excluded.type_text,declarations.type_text),
            type_fingerprint=CASE WHEN declarations.fingerprint_basis IN
                ('full_type_expr','ordered_telescope_and_target') THEN declarations.type_fingerprint
                ELSE COALESCE(excluded.type_fingerprint,declarations.type_fingerprint) END,
            fingerprint_basis=CASE WHEN declarations.fingerprint_basis IN
                ('full_type_expr','ordered_telescope_and_target') THEN declarations.fingerprint_basis
                ELSE COALESCE(excluded.fingerprint_basis,declarations.fingerprint_basis) END,
            metadata_json=excluded.metadata_json,snapshot_id=excluded.snapshot_id,external=excluded.external""",
                          (node, module, namespace, record.get("kind") or "", bool(record.get("private")),
                           bool(record.get("internal_detail")), bool(record.get("range")), path,
                           source_hash, signature, type_text, fingerprint, basis, _json(metadata), snapshot,
                           bool(record.get("external"))))
        self.conn.execute("DELETE FROM edges WHERE source_id=?", (node,))
        for edge_kind, keys in ((0, ("type_dependencies", "type_refs")),
                                (1, ("proof_dependencies", "proof_refs"))):
            names = record.get(keys[0], record.get(keys[1], []))
            if not isinstance(names, list):
                raise ValueError(f"{keys[0]} must be a list for {name}")
            self._nodes(names)
            self.conn.executemany("INSERT OR IGNORE INTO edges(source_id,target_id,kind) VALUES (?,?,?)",
                                  ((node, self._node_ids[ref], edge_kind) for ref in names))
        if type_text:
            self._document(node, "statement", "\n".join(
                part for part in (name, record.get("docstring"), type_text) if part))
        self._original_source(node, record, manifest, path, source_hash)
        if isinstance(record.get("triad"), dict):
            self._triad({"record_type": "triad", "declaration": name, **record["triad"]}, snapshot)
        for fragment in record.get("proof_fragments", []):
            self._fragment({"declaration": name, **fragment}, snapshot)

    def _original_source(self, node, record, manifest, path, digest):
        bounds = record.get("range")
        if not manifest.get("project_root") or not path or not digest or not isinstance(bounds, dict):
            return
        if not all(isinstance(bounds.get(key), dict) and "line" in bounds[key]
                   and "column" in bounds[key] for key in ("start", "end")):
            return
        root = Path(manifest["project_root"]).resolve()
        source = (root / path).resolve()
        try:
            source.relative_to(root)
        except ValueError as exc:
            raise ValueError(f"declaration source path escapes project root: {path}") from exc
        key = (str(source), digest)
        if key not in self._source_texts:
            raw = source.read_bytes()
            if hashlib.sha256(raw).hexdigest() != digest:
                raise ValueError(f"source content does not match manifest SHA-256: {path}")
            self._source_texts[key] = raw.decode("utf-8")
        text = self._source_texts[key]
        lines = text.split("\n")
        offsets, offset = [], 0
        for line in lines:
            offsets.append(offset)
            offset += len(line) + 1

        def position(point):
            line, column = point["line"], point["column"]
            if (not isinstance(line, int) or not isinstance(column, int) or
                    line < 1 or line > len(lines) or column < 0 or column > len(lines[line - 1])):
                raise ValueError(f"invalid Lean source range for {record.get('name')}: {point}")
            return offsets[line - 1] + column

        start, end = position(bounds["start"]), position(bounds["end"])
        if end < start:
            raise ValueError(f"reversed Lean source range for {record.get('name')}")
        self._document(node, "full_proof", text[start:end], metadata={
            "representation": "original Lean declaration source", "complete": True,
            "range": bounds, "source_path": path, "source_hash": digest})

    @staticmethod
    def _binder_text(binder: dict[str, Any]) -> str:
        label = binder.get("name", binder.get("id", "?"))
        prefix = f"{binder.get('id', '?')} #{binder.get('index', '?')} [{binder.get('binder_mode', 'explicit')}]"
        text = f"{prefix} {label} : {binder.get('type_text', '')}"
        if binder.get("value_text") is not None:
            text += " := " + binder["value_text"]
        if binder.get("depends_on"):
            text += " (depends on " + ", ".join(binder["depends_on"]) + ")"
        return text

    def _triad(self, record: dict[str, Any], snapshot: int) -> None:
        name = record.get("declaration", record.get("name"))
        node = self._node(name)
        row = self.conn.execute("SELECT source_hash FROM declarations WHERE node_id=?", (node,)).fetchone()
        source_hash = row[0] if row else None
        self.conn.execute("""INSERT INTO triads(node_id,payload_json,source_hash,snapshot_id) VALUES (?,?,?,?)
            ON CONFLICT(node_id) DO UPDATE SET payload_json=excluded.payload_json,
            source_hash=excluded.source_hash,snapshot_id=excluded.snapshot_id""",
                          (node, _json(record), source_hash, snapshot))
        binders = record.get("ordered_telescope", record.get("binders", []))
        if not isinstance(binders, list):
            raise ValueError(f"ordered_telescope must be a list for {name}")
        for role, view in (("condition", "conditions"), ("object", "objects")):
            selected = [binder for binder in binders if binder.get("role") == role]
            text = f"{name}\n" + "\n".join(self._binder_text(binder) for binder in selected)
            self._document(node, view, text, metadata={"binder_indices": [b.get("index") for b in selected]})
        skeleton = record.get("proof_skeleton", record.get("proof_detail", {}))
        target = record.get("target_text", record.get("goal", ""))
        detail = [name, "Ordered context:", *(self._binder_text(binder) for binder in binders),
                  f"Goal: {target}"]
        if isinstance(skeleton, dict):
            detail.append(f"Proof head: {skeleton.get('head', '')}")
            for arg in skeleton.get("arguments", []):
                role = "proof" if arg.get("is_proof") else "object"
                detail.append(f"Argument {arg.get('index', '?')} [{role}]: "
                              f"{arg.get('expression_text', '')} : {arg.get('type_text', '')}"
                              + (" (depends on " + ", ".join(arg["depends_on"]) + ")"
                                 if arg.get("depends_on") else ""))
        self._document(node, "proof_detail", "\n".join(detail))
        full_proof = skeleton.get("expression_text") if isinstance(skeleton, dict) else None
        existing = self.conn.execute("""SELECT metadata_json FROM documents
            WHERE node_id=? AND view='full_proof' AND record_key=''""", (node,)).fetchone()
        original = existing is not None and json.loads(existing[0]).get("representation") == "original Lean declaration source"
        if full_proof and not original:
            expr = skeleton.get("expr", {})
            nodes = expr.get("nodes", []) if isinstance(expr, dict) else []
            ast_truncated = any(isinstance(item, dict) and item.get("kind") == "truncated" for item in nodes)
            self._document(node, "full_proof", full_proof, metadata={
                "representation": "Lean pretty-printed proof term",
                "complete": skeleton.get("expression_text_complete") is True,
                "ast_budget": skeleton.get("expr_budget"), "ast_truncated": ast_truncated})
        elif not full_proof and not original:
            self.conn.execute("DELETE FROM documents WHERE node_id=? AND view='full_proof'", (node,))
        # A fingerprint covers the entire contract, never merely the conclusion
        # or equality of proof terms (Lean has proof irrelevance).
        full_type = record.get("type_expr")
        contract = full_type if full_type is not None else {
            "ordered_telescope": binders, "target_expr": record.get("target_expr"),
            "target_text": target, "universe_params": record.get("universe_params", [])}
        self.conn.execute("""UPDATE declarations SET type_fingerprint=?, fingerprint_basis=?
            WHERE node_id=?""",
                          (_sha(_json(contract)), "full_type_expr" if full_type is not None
                           else "ordered_telescope_and_target", node))

    def _fragment(self, record: dict[str, Any], snapshot: int) -> None:
        name = record.get("declaration", record.get("name"))
        node = self._node(name)
        payload = _json(record)
        key = str(record.get("id", _sha(payload)))
        row = self.conn.execute("SELECT source_hash FROM declarations WHERE node_id=?", (node,)).fetchone()
        self.conn.execute("""INSERT INTO fragments(node_id,fragment_key,payload_json,source_hash,snapshot_id)
            VALUES (?,?,?,?,?) ON CONFLICT(node_id,fragment_key) DO UPDATE SET
            payload_json=excluded.payload_json,source_hash=excluded.source_hash,snapshot_id=excluded.snapshot_id""",
                          (node, key, payload, row[0] if row else None, snapshot))
        fragment_id = self.conn.execute("SELECT id FROM fragments WHERE node_id=? AND fragment_key=?",
                                        (node, key)).fetchone()[0]
        text = [name, f"Tactic ({record.get('syntax_kind', '')}):", str(record.get("source", ""))]
        for field, label in (("goals_before", "Before"), ("goals_after", "After")):
            for goal in record.get(field, []):
                text.append(f"{label} goal {goal.get('id', '?')}:")
                text.extend(self._binder_text(binder) for binder in goal.get("hypotheses", []))
                text.append(f"⊢ {goal.get('target_text', '')}")
        self._document(node, "proof_state", "\n".join(text), key, {"fragment_id": fragment_id})

    def import_jsonl(self, path: str | Path, source_manifest: dict[str, Any] | None = None,
                     replace: bool = False) -> dict[str, Any]:
        """Atomically stream an exporter file; malformed input rolls back the batch.

        Full exports replace each emitted declaration's outgoing references.
        Partial triad/trace exports preserve declarations and other dependencies.
        A caller-supplied source manifest takes priority over an exporter manifest.
        """
        counts = defaultdict(int)
        manifest = dict(source_manifest or {})
        try:
            with self.conn:
                if replace:
                    self.conn.execute("DELETE FROM nodes")
                    self.conn.execute("DELETE FROM diagnostics")
                    self._node_ids.clear()
                snapshot = self._snapshot(manifest)
                with Path(path).open(encoding="utf-8") as stream:
                    for line_number, line in enumerate(stream, 1):
                        if not line.strip():
                            continue
                        try:
                            record = json.loads(line)
                            if not isinstance(record, dict):
                                raise ValueError("expected a JSON object")
                            kind = record.get("record_type", record.get("record_kind"))
                            if kind is None and "name" in record:
                                kind = "declaration"
                            if kind == "manifest":
                                exporter = record.get("source_manifest", record)
                                if source_manifest is None:
                                    manifest = dict(exporter)
                                    snapshot = self._snapshot(manifest)
                                self.conn.execute("INSERT OR REPLACE INTO meta(key,value) VALUES (?,?)",
                                                  ("exporter_manifest", _json(record)))
                            elif kind == "declaration":
                                self._declaration(record, manifest, snapshot)
                            elif kind == "triad":
                                self._triad(record, snapshot)
                            elif kind == "proof_fragment":
                                self._fragment(record, snapshot)
                            elif kind == "diagnostic":
                                self.conn.execute("INSERT INTO diagnostics(snapshot_id,payload_json) VALUES (?,?)",
                                                  (snapshot, _json(record)))
                            elif kind == "summary":
                                self.conn.execute("INSERT OR REPLACE INTO meta(key,value) VALUES (?,?)",
                                                  ("exporter_summary", _json(record)))
                            else:
                                raise ValueError(f"unknown record_type {kind!r}")
                            counts[kind] += 1
                        except (ValueError, TypeError, KeyError) as exc:
                            raise ValueError(f"{path}:{line_number}: {exc}") from exc
                self.conn.execute("INSERT OR REPLACE INTO meta(key,value) VALUES ('active_snapshot',?)",
                                  (str(snapshot),))
        except BaseException:
            # Cached row IDs may have belonged to inserts rolled back above.
            self._node_ids.clear()
            raise
        return {"records": dict(counts), "snapshot_id": snapshot,
                "content_hash": _manifest_hash(manifest), "source_bound": bool(manifest.get("sources"))}

    def snapshot_status(self, current_manifest: dict[str, Any] | None = None) -> dict[str, Any]:
        row = self.conn.execute("""SELECT s.* FROM snapshots s JOIN meta m
            ON m.key='active_snapshot' AND s.id=CAST(m.value AS INTEGER)""").fetchone()
        if row is None:
            return {"status": "empty", "stale": None, "source_bound": False}
        manifest = json.loads(row["manifest_json"])
        bound = bool(manifest.get("sources"))
        current_hash = _manifest_hash(current_manifest) if current_manifest is not None else None
        # A partial trace import must not make older declaration metadata appear
        # current merely by installing the latest full manifest.
        stale_declarations = 0
        if bound:
            sources = manifest["sources"]
            for declaration in self.conn.execute(
                    "SELECT source_path,source_hash FROM declarations WHERE external=0"):
                path, digest = declaration
                current = sources.get(path)
                if isinstance(current, dict):
                    current = current.get("sha256", current.get("hash"))
                if current != digest or current is None:
                    stale_declarations += 1
        compared = current_hash != row["content_hash"] if current_hash is not None and bound else None
        stale = True if stale_declarations else compared
        return {"status": "stale" if stale else ("current" if stale is False else "unchecked"),
                "stale": stale, "source_bound": bound, "content_hash": row["content_hash"],
                "current_content_hash": current_hash, "manifest": manifest,
                "stale_declarations": stale_declarations,
                "snapshot_id": row["id"], "imported_at": row["imported_at"]}

    def get_decl(self, name: str) -> dict[str, Any] | None:
        row = self.conn.execute("""SELECT n.id,n.name,d.* FROM nodes n
            LEFT JOIN declarations d ON d.node_id=n.id WHERE n.name=?""", (name,)).fetchone()
        if row is None:
            return None
        record = json.loads(row["metadata_json"]) if row["metadata_json"] else {"name": name}
        record.update({"id": row["id"], "name": name,
                       "external": row["node_id"] is None or bool(row["external"]),
                       "module": row["module"], "namespace": row["namespace"],
                       "source_path": row["source_path"], "source_hash": row["source_hash"],
                       "type_text": row["type_text"], "type_fingerprint": row["type_fingerprint"],
                       "fingerprint_basis": row["fingerprint_basis"], "snapshot_id": row["snapshot_id"]})
        refs = {0: [], 1: []}
        for edge in self.conn.execute("""SELECT e.kind,n.name FROM edges e JOIN nodes n
            ON n.id=e.target_id WHERE e.source_id=? ORDER BY n.name""", (row["id"],)):
            refs[edge["kind"]].append(edge["name"])
        record.update(type_dependencies=refs[0], proof_dependencies=refs[1])
        return record

    def get_triad(self, name: str) -> dict[str, Any] | None:
        row = self.conn.execute("""SELECT t.payload_json FROM triads t JOIN nodes n
            ON n.id=t.node_id WHERE n.name=?""", (name,)).fetchone()
        return json.loads(row[0]) if row else None

    def get_proof_text(self, name: str) -> dict[str, Any] | None:
        row = self.conn.execute("""SELECT v.*,n.name,d.module,d.namespace,d.kind,d.private,
            d.internal_detail,d.has_range,d.source_path,d.source_hash FROM documents v
            JOIN nodes n ON n.id=v.node_id JOIN declarations d ON d.node_id=n.id
            WHERE n.name=? AND v.view='full_proof' AND v.record_key=''""", (name,)).fetchone()
        return self._view_row(row) if row else None

    def get_fragment(self, fragment_id: int) -> dict[str, Any] | None:
        row = self.conn.execute("SELECT payload_json FROM fragments WHERE id=?", (fragment_id,)).fetchone()
        return {**json.loads(row[0]), "id": fragment_id} if row else None

    @staticmethod
    def _filters(view: str | None = None, module: str | None = None,
                 namespace: str | None = None, kind: str | None = None,
                 include_internal: bool = True, human_only: bool = False) -> tuple[list[str], list[Any]]:
        clauses, args = [], []
        for column, value in (("v.view", view), ("d.module", module), ("d.kind", kind)):
            if value is not None:
                clauses.append(column + "=?")
                args.append(value)
        if namespace is not None:
            clauses.append("(d.namespace=? OR substr(d.namespace,1,?)=?)")
            args.extend((namespace, len(namespace) + 1, namespace + "."))
        if not include_internal:
            clauses.extend(("d.internal_detail=0", "d.private=0"))
        if human_only:
            clauses.extend(("d.internal_detail=0", "d.private=0", "d.has_range=1"))
        return clauses, args

    @staticmethod
    def _view_row(row: sqlite3.Row) -> dict[str, Any]:
        result = dict(row)
        result["declaration"] = result["name"]
        result["record_id"] = result["name"]
        result["metadata"] = json.loads(result.pop("metadata_json"))
        return result

    def iter_views(self, view: str | None = None, module: str | None = None,
                   namespace: str | None = None, kind: str | None = None,
                   include_internal: bool = False, human_only: bool = False,
                   limit: int | None = None, offset: int = 0, *,
                   include_text: bool = True) -> Iterator[dict[str, Any]]:
        """Iterate source-ordered views, optionally omitting proof text at SQL level."""
        clauses, args = self._filters(view, module, namespace, kind, include_internal, human_only)
        columns = ("v.*" if include_text else
                   "v.id,v.node_id,v.view,v.record_key,v.content_hash,v.metadata_json")
        sql = f"""SELECT {columns},n.name,d.module,d.namespace,d.kind,d.private,d.internal_detail,
            d.has_range,d.source_path,d.source_hash FROM documents v JOIN nodes n ON n.id=v.node_id
            JOIN declarations d ON d.node_id=n.id"""
        if clauses:
            sql += " WHERE " + " AND ".join(clauses)
        sql += " ORDER BY v.id LIMIT ? OFFSET ?"
        args.extend((-1 if limit is None else max(0, limit), max(0, offset)))
        for row in self.conn.execute(sql, args):
            yield self._view_row(row)

    def search_lexical(self, query: str, limit: int = 20, offset: int = 0,
                       view: str | None = None, module: str | None = None,
                       namespace: str | None = None, kind: str | None = None,
                       include_internal: bool = True) -> list[dict[str, Any]]:
        # Treat user input as literal terms, not an accidental FTS query program.
        terms = re.findall(r"[^\W_]+(?:_[^\W_]+)*", query, flags=re.UNICODE)
        if not terms:
            return []
        match = " AND ".join('"' + term.replace('"', '""') + '"' for term in terms)
        clauses, args = self._filters(view, module, namespace, kind, include_internal)
        clauses.insert(0, "documents_fts MATCH ?")
        args.insert(0, match)
        sql = """SELECT v.*,n.name,d.module,d.namespace,d.kind,d.private,d.internal_detail,
            d.has_range,d.source_path,d.source_hash,
            snippet(documents_fts,0,'[',']',' … ',32) AS snippet
            FROM documents_fts JOIN documents v ON v.id=documents_fts.rowid
            JOIN nodes n ON n.id=v.node_id JOIN declarations d ON d.node_id=n.id WHERE """
        sql += " AND ".join(clauses) + " ORDER BY documents_fts.rank,v.id LIMIT ? OFFSET ?"
        args.extend((max(0, limit), max(0, offset)))
        return [self._view_row(row) for row in self.conn.execute(sql, args)]

    def neighbors(self, name: str, direction: str = "upstream", edge_kind: str | None = None,
                  depth: int = 1, limit: int = 100, offset: int = 0,
                  include_external: bool = True) -> dict[str, Any]:
        if direction not in ("upstream", "downstream"):
            raise ValueError("direction must be upstream (dependencies) or downstream (dependents)")
        if edge_kind not in (None, *EDGE_KINDS):
            raise ValueError("edge_kind must be type_ref or proof_ref")
        if depth < 1 or limit < 1 or offset < 0:
            raise ValueError("depth and limit must be positive and offset nonnegative")
        root = self.conn.execute("SELECT id FROM nodes WHERE name=?", (name,)).fetchone()
        result = {"name": name, "direction": direction, "edge_kind": edge_kind, "depth": depth,
                  "limit": limit, "offset": offset, "items": [], "has_more": False, "next_offset": None}
        if root is None:
            return result
        origin, dest = ("source_id", "target_id") if direction == "upstream" else ("target_id", "source_id")
        kind_clause = " AND e.kind=:kind" if edge_kind else ""
        sql = f"""WITH RECURSIVE reach(id,distance) AS (
            SELECT e.{dest},1 FROM edges e WHERE e.{origin}=:root {kind_clause}
            UNION
            SELECT e.{dest},r.distance+1 FROM reach r JOIN edges e ON e.{origin}=r.id
                WHERE r.distance<:depth {kind_clause})
            SELECT n.id,n.name,d.module,d.namespace,d.kind,d.source_path,
                d.private,d.internal_detail,d.has_range,
                (d.node_id IS NULL OR d.external=1) AS external,
                MIN(r.distance) AS distance FROM reach r JOIN nodes n ON n.id=r.id
                LEFT JOIN declarations d ON d.node_id=n.id WHERE n.id != :root
                {'AND d.node_id IS NOT NULL AND d.external=0' if not include_external else ''}
                GROUP BY n.id ORDER BY distance,n.name LIMIT :limit OFFSET :offset"""
        rows = self.conn.execute(sql, {"root": root[0], "depth": depth, "limit": limit + 1,
                                      "offset": offset, "kind": EDGE_KINDS.get(edge_kind)}).fetchall()
        result["items"] = [dict(row) for row in rows[:limit]]
        result["has_more"] = len(rows) > limit
        result["next_offset"] = offset + limit if result["has_more"] else None
        return result

    def duplicate_candidates(self, limit: int = 20, offset: int = 0,
                             namespace: str | None = None,
                             include_internal: bool = False,
                             kind: str | None = "theorem") -> list[dict[str, Any]]:
        clauses = ["d.type_fingerprint IS NOT NULL"]
        args: list[Any] = []
        filters, values = self._filters(namespace=namespace, kind=kind,
                                        include_internal=include_internal)
        clauses.extend(filters)
        args.extend(values)
        rows = self.conn.execute("""SELECT d.type_fingerprint,MIN(d.fingerprint_basis) AS basis,
            COUNT(*) AS count FROM declarations d WHERE """ + " AND ".join(clauses) +
                                 " GROUP BY d.type_fingerprint HAVING COUNT(*)>1"
                                 " ORDER BY count DESC,d.type_fingerprint LIMIT ? OFFSET ?",
                                 [*args, max(0, limit), max(0, offset)])
        result = []
        for row in rows:
            names = [r[0] for r in self.conn.execute("""SELECT n.name FROM nodes n
                JOIN declarations d ON d.node_id=n.id WHERE d.type_fingerprint=? AND """ +
                                                    " AND ".join(clauses) + " ORDER BY n.name",
                                                    [row["type_fingerprint"], *args])]
            result.append({"type_fingerprint": row["type_fingerprint"], "basis": row["basis"],
                           "count": row["count"], "names": names,
                           "status": "candidate_requires_contract_and_caller_check"})
        return result

    def stats(self) -> dict[str, Any]:
        result = {table: self.conn.execute(f"SELECT COUNT(*) FROM {table}").fetchone()[0]
                  for table in ("nodes", "declarations", "triads", "fragments", "documents", "snapshots")}
        result["declaration_metadata"] = result["declarations"]
        result["declarations"] = self.conn.execute(
            "SELECT COUNT(*) FROM declarations WHERE external=0").fetchone()[0]
        result["external_nodes"] = result["nodes"] - result["declarations"]
        result["edges"] = {kind: self.conn.execute("SELECT COUNT(*) FROM edges WHERE kind=?", (code,)).fetchone()[0]
                           for kind, code in EDGE_KINDS.items()}
        result["views"] = {row[0]: row[1] for row in self.conn.execute(
            "SELECT view,COUNT(*) FROM documents GROUP BY view")}
        result["snapshot"] = self.snapshot_status()
        return result

    def dag(self, name: str, direction: str = "upstream", depth: int = 2,
            limit: int = 250, edge_kind: str | None = None) -> dict[str, Any]:
        """Return a bounded local graph and its SCC condensation, retaining cycles."""
        page = self.neighbors(name, direction, edge_kind, depth, limit)
        root = self.conn.execute("SELECT id FROM nodes WHERE name=?", (name,)).fetchone()
        if root is None:
            return {"root": name, "components": [], "edges": [], "raw_edges": [], "truncated": False}
        names = {row["id"]: row["name"] for row in page["items"]}
        names[root[0]] = name
        ids = sorted(names)
        marks = ",".join("?" for _ in ids)
        args: list[Any] = [*ids, *ids]
        sql = f"SELECT source_id,target_id,kind FROM edges WHERE source_id IN ({marks}) AND target_id IN ({marks})"
        if edge_kind:
            sql += " AND kind=?"
            args.append(EDGE_KINDS[edge_kind])
        raw = [tuple(row) for row in self.conn.execute(sql, args)]
        forward: dict[int, list[int]] = defaultdict(list)
        reverse: dict[int, list[int]] = defaultdict(list)
        for source, target, _ in raw:
            forward[source].append(target)
            reverse[target].append(source)
        # Iterative Kosaraju avoids recursion-depth failures on long local chains.
        seen, order = set(), []
        for start in ids:
            if start in seen:
                continue
            stack = [(start, False)]
            while stack:
                node, finished = stack.pop()
                if finished:
                    order.append(node)
                elif node not in seen:
                    seen.add(node)
                    stack.append((node, True))
                    stack.extend((target, False) for target in forward[node] if target not in seen)
        owner, components = {}, []
        self_loops = {source for source, target, _ in raw if source == target}
        for start in reversed(order):
            if start in owner:
                continue
            component_id = len(components)
            stack, members = [start], []
            owner[start] = component_id
            while stack:
                node = stack.pop()
                members.append(node)
                for target in reverse[node]:
                    if target not in owner:
                        owner[target] = component_id
                        stack.append(target)
            components.append({"id": component_id, "members": sorted(names[node] for node in members),
                               "recursive": len(members) > 1 or any(node in self_loops for node in members)})
        labels = {code: kind for kind, code in EDGE_KINDS.items()}
        condensed = sorted({(owner[a], owner[b], kind) for a, b, kind in raw if owner[a] != owner[b]})
        return {"root": name, "direction": direction, "depth": depth, "truncated": page["has_more"],
                "next_offset": page["next_offset"], "components": components,
                "edges": [{"source": a, "target": b, "kind": labels[kind]} for a, b, kind in condensed],
                "raw_edges": [{"source": names[a], "target": names[b], "kind": labels[kind]}
                              for a, b, kind in raw]}
