"""Contract tests for persisted proof records and their independent graph edges."""

import hashlib
import itertools
import json
from pathlib import Path
import sqlite3
import tempfile
import unittest

from tools.proof_atlas.store import Store


def declaration(name, module="Demo.Core", **extra):
    return {"record_type": "declaration", "name": name, "module": module,
            "kind": "theorem", "private": False, "internal_detail": False,
            "range": {"start": {"line": 1}, "end": {"line": 4}},
            "type_dependencies": [], "proof_dependencies": [], **extra}


def triad(name, target="FiniteMeasure μ", condition="IsFiniteMeasure μ"):
    return {"record_type": "triad", "declaration": name,
            "ordered_telescope": [
                {"id": "b0", "index": 0, "name": "μ", "binder_mode": "implicit",
                 "role": "object", "type_text": "Measure M", "type_expr": "Measure M",
                 "depends_on": []},
                {"id": "b1", "index": 1, "name": "h", "binder_mode": "instance",
                 "role": "condition", "type_text": condition, "type_expr": condition,
                 "depends_on": ["b0"]}],
            "target_text": target, "target_expr": target, "universe_params": [],
            "proof_skeleton": {"head": "finite_measure", "expression_text": "fullUniqueProof μ h",
                               "arguments": [{"index": 0, "expression_text": "μ", "type_text": "Measure M"}]}}


class StoreTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name)
        self.path = self.root / "index.sqlite3"
        self.store = Store(self.path)
        self.addCleanup(self.store.close)
        self.manifest = {"sources": {"Demo/Core.lean": "source-v1"},
                         "toolchain": "lean-test", "mathlib_revision": "mathlib-test"}

    def ingest(self, records, manifest=None, replace=False):
        path = self.root / "batch.jsonl"
        path.write_text("".join(json.dumps(record) + "\n" for record in records), encoding="utf-8")
        return self.store.import_jsonl(path, self.manifest if manifest is None else manifest,
                                       replace=replace)

    def test_persistence_and_full_triad_context(self):
        self.ingest([declaration("Demo.keep"), triad("Demo.keep")])
        with Store(self.path) as reopened:
            saved = reopened.get_triad("Demo.keep")
            self.assertEqual([b["id"] for b in saved["ordered_telescope"]], ["b0", "b1"])
            self.assertEqual(saved["ordered_telescope"][1]["depends_on"], ["b0"])
            views = {row["view"]: row for row in reopened.iter_views()}
            self.assertIn("b1 #1 [instance] h : IsFiniteMeasure μ", views["conditions"]["text"])
            self.assertNotIn('"type_expr"', views["conditions"]["text"])
            self.assertIn("Measure M", views["objects"]["text"])
            self.assertEqual(views["full_proof"]["text"], "fullUniqueProof μ h")
            self.assertEqual(reopened.search_lexical("fullUniqueProof")[0]["name"], "Demo.keep")

    def test_atomic_rollback_after_partial_parse_and_cached_node_ids(self):
        self.ingest([declaration("Demo.keep", type_dependencies=["External.Known"])])
        path = self.root / "broken.jsonl"
        path.write_text(json.dumps(declaration("Demo.lost", proof_dependencies=["External.New"]))
                        + "\nnot valid JSON\n", encoding="utf-8")
        with self.assertRaisesRegex(ValueError, ":2:"):
            self.store.import_jsonl(path, self.manifest)
        self.assertIsNone(self.store.get_decl("Demo.lost"))
        self.assertIsNone(self.store.get_decl("External.New"))
        self.assertEqual(self.store.stats()["declarations"], 1)
        self.ingest([declaration("Demo.reused", proof_dependencies=["External.New"])])
        self.assertEqual(self.store.get_decl("Demo.reused")["proof_dependencies"], ["External.New"])

    def test_incremental_edges_replaced_and_edge_kinds_remain_separate(self):
        self.ingest([declaration("Demo.A", type_dependencies=["Demo.B"],
                                 proof_dependencies=["Demo.B", "External.proof"]),
                     declaration("Demo.B")])
        self.assertEqual(self.store.stats()["edges"], {"type_ref": 1, "proof_ref": 2})
        incoming = self.store.neighbors("Demo.B", "downstream", "type_ref")
        self.assertEqual([item["name"] for item in incoming["items"]], ["Demo.A"])
        self.ingest([declaration("Demo.A", proof_dependencies=["External.other"])])
        self.assertEqual(self.store.neighbors("Demo.B", "downstream")["items"], [])
        self.assertEqual(self.store.get_decl("Demo.A")["proof_dependencies"], ["External.other"])

    def test_namespace_filter_is_segment_based_and_internal_views_opt_in(self):
        records = []
        for name in ("A.one", "A.B.two", "AB.three", "A.hidden"):
            records.extend((declaration(name, private=name == "A.hidden"), triad(name)))
        self.ingest(records)
        views = list(self.store.iter_views(view="objects", namespace="A"))
        self.assertEqual({view["name"] for view in views}, {"A.one", "A.B.two"})
        views = list(self.store.iter_views(view="objects", namespace="A", include_internal=True))
        self.assertEqual({view["name"] for view in views}, {"A.one", "A.B.two", "A.hidden"})

    def test_metadata_projection_does_not_read_proof_text(self):
        long_proof = triad("Demo.keep")
        long_proof["proof_skeleton"]["expression_text"] = "large proof body " * 10000
        self.ingest([declaration("Demo.keep"), long_proof])
        full = list(self.store.iter_views())

        def deny_proof_text(action, table, column, database, trigger):
            if action == sqlite3.SQLITE_READ and table == "documents" and column == "text":
                return sqlite3.SQLITE_DENY
            return sqlite3.SQLITE_OK

        self.store.conn.set_authorizer(deny_proof_text)
        try:
            metadata = list(self.store.iter_views(include_text=False))
            with self.assertRaises(sqlite3.DatabaseError):
                list(self.store.iter_views())
        finally:
            self.store.conn.set_authorizer(None)
        self.assertEqual(metadata, [{key: value for key, value in item.items() if key != "text"}
                                    for item in full])

    def test_metadata_projection_preserves_composed_filters_and_pagination(self):
        records = []
        for name, extra in (
                ("A.z", {}), ("A.B.middle", {"module": "Other"}), ("AB.outside", {}),
                ("A.hidden", {"private": True}), ("A.internal", {"internal_detail": True}),
                ("A.definition", {"kind": "definition"}), ("A.noRange", {"range": None})):
            records.extend((declaration(name, **extra), triad(name)))
        self.ingest(records)
        for view, module, namespace, kind, include_internal, human_only in itertools.product(
                (None, "objects"), (None, "Other"), (None, "A"),
                (None, "theorem"), (False, True), (False, True)):
            filters = dict(view=view, module=module, namespace=namespace, kind=kind,
                           include_internal=include_internal, human_only=human_only)
            with self.subTest(**filters):
                full = list(self.store.iter_views(**filters))
                expected = [{key: value for key, value in item.items() if key != "text"}
                            for item in full]
                metadata = list(self.store.iter_views(**filters, include_text=False))
                self.assertEqual(metadata, expected)
                pages = []
                for offset in range(0, len(full), 3):
                    pages.extend(self.store.iter_views(**filters, include_text=False,
                                                      limit=3, offset=offset))
                self.assertEqual(pages, expected)
                self.assertEqual([item["id"] for item in metadata],
                                 sorted(item["id"] for item in metadata))

    def test_fragments_persist_goals_and_are_lexically_searchable(self):
        fragment = {"record_type": "proof_fragment", "declaration": "Demo.A",
                    "syntax_kind": "apply", "source": "Demo/Core.lean", "start": {"line": 3},
                    "end": {"line": 3}, "goals_before": [{"id": "g0", "target_text": "RareTarget"}],
                    "goals_after": [], "goal_ids_before": ["g0"], "goal_ids_after": []}
        self.ingest([declaration("Demo.A"), fragment])
        self.ingest([fragment])
        self.assertEqual(self.store.stats()["fragments"], 1)
        found = self.store.search_lexical("RareTarget", view="proof_state")
        self.assertEqual(len(found), 1)
        saved = self.store.get_fragment(found[0]["metadata"]["fragment_id"])
        self.assertEqual(saved["goals_before"][0]["id"], "g0")

    def test_source_manifest_binds_dirty_contents_and_invalidates_changed_triad(self):
        self.ingest([declaration("Demo.A"), triad("Demo.A")])
        same_contents = {**self.manifest, "git_head": "unrelated", "captured_at": "later"}
        self.assertFalse(self.store.snapshot_status(same_contents)["stale"])
        changed = {**self.manifest, "sources": {"Demo/Core.lean": "dirty-v2"}}
        self.assertTrue(self.store.snapshot_status(changed)["stale"])
        self.ingest([declaration("Demo.A")], changed)
        self.assertIsNone(self.store.get_triad("Demo.A"))
        self.assertEqual(self.store.search_lexical("fullUniqueProof"), [])
        self.assertFalse(self.store.snapshot_status(changed)["stale"])

    def test_partial_trace_cannot_hide_stale_declaration_metadata(self):
        self.ingest([declaration("Demo.A"), triad("Demo.A")])
        changed = {**self.manifest, "sources": {"Demo/Core.lean": "dirty-v2"}}
        self.ingest([triad("Demo.A")], changed)
        status = self.store.snapshot_status(changed)
        self.assertTrue(status["stale"])
        self.assertEqual(status["stale_declarations"], 1)

    def test_external_detail_stubs_preserve_full_metadata_and_do_not_stale_snapshot(self):
        self.ingest([declaration("Demo.A", proof_dependencies=["Demo.B"]), triad("Demo.A"),
                     declaration("Demo.B")])
        self.ingest([{"record_type": "declaration", "name": "Demo.A", "external": True,
                      "module": "Demo.Core", "kind": "theorem"},
                     {"record_type": "declaration", "name": "Mathlib.stub", "external": True,
                      "module": "Mathlib.External", "kind": "theorem"}])
        self.assertEqual(self.store.get_decl("Demo.A")["proof_dependencies"], ["Demo.B"])
        self.assertIsNotNone(self.store.get_triad("Demo.A"))
        self.assertTrue(self.store.get_decl("Mathlib.stub")["external"])
        self.assertFalse(self.store.snapshot_status(self.manifest)["stale"])
        self.assertEqual(self.store.stats()["declarations"], 2)
        self.assertEqual(self.store.stats()["external_nodes"], 1)

    def test_bounded_graph_pagination_and_recursive_condensation(self):
        self.ingest([declaration("Demo.A", proof_dependencies=["Demo.B", "Demo.C", "Demo.A"]),
                     declaration("Demo.B", proof_dependencies=["Demo.A"]),
                     declaration("Demo.C", type_dependencies=["External.Known"])])
        page = self.store.neighbors("Demo.A", depth=3, limit=1)
        self.assertEqual(len(page["items"]), 1)
        self.assertTrue(page["has_more"])
        following = self.store.neighbors("Demo.A", depth=3, limit=1, offset=page["next_offset"])
        self.assertNotEqual(following["items"][0]["name"], page["items"][0]["name"])
        dag = self.store.dag("Demo.A", depth=3)
        recursive = [component for component in dag["components"] if component["recursive"]]
        self.assertEqual(recursive[0]["members"], ["Demo.A", "Demo.B"])
        self.assertTrue(any(edge["source"] == edge["target"] for edge in dag["raw_edges"]))
        self.assertTrue(all(edge["source"] != edge["target"] for edge in dag["edges"]))

    def test_duplicate_candidates_use_entire_contract_and_never_proof_equivalence(self):
        self.ingest([declaration("Demo.A"), triad("Demo.A"),
                     declaration("Demo.B"), triad("Demo.B"),
                     declaration("Demo.C"), triad("Demo.C", condition="DifferentCondition μ")])
        groups = self.store.duplicate_candidates()
        self.assertEqual(len(groups), 1)
        self.assertEqual(groups[0]["names"], ["Demo.A", "Demo.B"])
        self.assertEqual(groups[0]["basis"], "ordered_telescope_and_target")
        self.assertIn("candidate", groups[0]["status"])

    def test_duplicate_proof_candidates_exclude_same_type_data_projections_and_instances(self):
        self.ingest([
            declaration("PopData.Berr", kind="definition", type_text="ℝ"),
            declaration("PopData.Bnd", kind="definition", type_text="ℝ"),
            declaration("PopData.Cb", kind="definition", type_text="ℝ"),
            declaration("Demo.topologyA", kind="definition", type_text="TopologicalSpace M"),
            declaration("Demo.topologyB", kind="definition", type_text="TopologicalSpace M"),
            declaration("Demo.proofA", type_text="∀ n : ℕ, n = n"),
            declaration("Demo.proofB", type_text="∀ n : ℕ, n = n")])
        groups = self.store.duplicate_candidates()
        self.assertEqual(len(groups), 1)
        self.assertEqual(groups[0]["names"], ["Demo.proofA", "Demo.proofB"])
        definitions = self.store.duplicate_candidates(kind="definition")
        self.assertEqual(definitions[0]["names"], ["PopData.Berr", "PopData.Bnd", "PopData.Cb"])
        self.assertEqual(len(definitions), 2)
        self.assertEqual(len(self.store.duplicate_candidates(kind=None)), 3)

    def test_unchanged_metadata_refresh_retains_typed_fingerprint_and_triad(self):
        metadata = declaration("Demo.A", type_text="(μ : Measure M) → FiniteMeasure μ")
        self.ingest([metadata, triad("Demo.A")])
        before = self.store.get_decl("Demo.A")["type_fingerprint"]
        self.ingest([metadata])
        self.assertEqual(self.store.get_decl("Demo.A")["type_fingerprint"], before)
        self.assertEqual(self.store.get_decl("Demo.A")["fingerprint_basis"],
                         "ordered_telescope_and_target")
        self.assertIsNotNone(self.store.get_triad("Demo.A"))

    def test_original_unicode_declaration_source_is_complete_and_survives_triad_render(self):
        source = self.root / "Demo/Core.lean"
        source.parent.mkdir()
        text = "-- α😀 prefix\n  theorem exactSource : True := by\n    trivial\n-- after\n"
        source.write_text(text, encoding="utf-8")
        digest = hashlib.sha256(source.read_bytes()).hexdigest()
        manifest = {"project_root": str(self.root), "sources": {"Demo/Core.lean": digest}}
        bounds = {"start": {"line": 1, "column": 4}, "end": {"line": 3, "column": 11}}
        self.ingest([declaration("Demo.A", range=bounds), triad("Demo.A")], manifest)
        view = next(self.store.iter_views(view="full_proof"))
        self.assertEqual(view["text"], "😀 prefix\n  theorem exactSource : True := by\n    trivial")
        self.assertTrue(view["metadata"]["complete"])
        self.assertEqual(view["metadata"]["representation"], "original Lean declaration source")
        self.assertEqual(self.store.get_proof_text("Demo.A")["text"], view["text"])

    def test_source_hash_mismatch_and_path_escape_do_not_certify_original_proof(self):
        source = self.root / "Demo/Core.lean"
        source.parent.mkdir()
        source.write_text("theorem A : True := by trivial\n", encoding="utf-8")
        bounds = {"start": {"line": 1, "column": 0}, "end": {"line": 1, "column": 10}}
        manifest = {"project_root": str(self.root), "sources": {"Demo/Core.lean": "wrong-sha"}}
        with self.assertRaisesRegex(ValueError, "manifest SHA-256"):
            self.ingest([declaration("Demo.A", range=bounds)], manifest)
        self.assertIsNone(self.store.get_decl("Demo.A"))
        with self.assertRaisesRegex(ValueError, "escapes project root"):
            self.ingest([declaration("Demo.A", range=bounds, source_path="../outside.lean",
                                     source_hash="unused")], manifest)

    def test_pretty_proof_completeness_is_explicit_without_original_source(self):
        self.ingest([declaration("Demo.A"), triad("Demo.A")])
        view = next(self.store.iter_views(view="full_proof"))
        self.assertFalse(view["metadata"]["complete"])
        self.assertEqual(view["metadata"]["representation"], "Lean pretty-printed proof term")

    def test_failed_replace_keeps_previous_persisted_index(self):
        self.ingest([declaration("Demo.A"), triad("Demo.A")])
        path = self.root / "broken.jsonl"
        path.write_text('{"record_type":"unknown"}\n', encoding="utf-8")
        with self.assertRaises(ValueError):
            self.store.import_jsonl(path, self.manifest, replace=True)
        self.assertIsNotNone(self.store.get_triad("Demo.A"))
        self.assertEqual(len(self.store.search_lexical("fullUniqueProof", view="full_proof")), 1)


if __name__ == "__main__":
    unittest.main()
