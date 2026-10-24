"""Retrieval integration using a small source-bound, typed exporter fixture."""

from contextlib import redirect_stderr, redirect_stdout
from copy import deepcopy
import io
import json
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

from tools.proof_atlas.cli import main
from tools.proof_atlas.manifest import source_manifest
from tools.proof_atlas.retrieval import (
    context_packet, instantiate_pattern, query_text, search, transfer,
)
from tools.proof_atlas.store import Store


def const(name):
    return {"kind": "const", "name": name, "levels": []}


def var(identity):
    return {"kind": "fvar", "id": identity}


def app(name, arg):
    return {"kind": "app", "fn": const(name), "arg": arg}


def telescope(names=("b0", "b1", "b2"), predicate="P"):
    return [
        {"id": names[0], "index": 0, "name": "x", "binder_mode": "default",
         "role": "object", "type_text": "Nat", "type_expr": const("Nat"), "depends_on": []},
        {"id": names[1], "index": 1, "name": "h", "binder_mode": "default",
         "role": "condition", "type_text": f"{predicate} x",
         "type_expr": app(predicate, var(names[0])), "depends_on": [names[0]]},
        {"id": names[2], "index": 2, "name": "y", "binder_mode": "default",
         "role": "object", "type_text": "Nat", "type_expr": const("Nat"), "depends_on": []},
    ]


def declaration(name):
    return {"record_type": "declaration", "name": name, "module": "OTSelector.Demo",
            "kind": "theorem", "private": False, "internal_detail": False,
            "type_text": "(x : Nat) → P x → (y : Nat) → Needle f x",
            "range": {"start": {"line": 1}, "end": {"line": 5}},
            "type_dependencies": [], "proof_dependencies": []}


def triad(name):
    return {"record_type": "triad", "declaration": name, "ordered_telescope": telescope(),
            "target_text": "Needle f x", "target_expr": app("f", var("b0")),
            "universe_params": [],
            "proof_skeleton": {"head": "Demo.core", "expression_text": "Demo.core x h",
                               "expr": app("Demo.core", var("b0")), "arguments": []}}


def fragment(name, identity, needle):
    return {"record_type": "proof_fragment", "declaration": name, "id": identity,
            "syntax_kind": "constructor", "source": "constructor", "source_kind": "original",
            "source_original": "constructor", "start": {"line": 3}, "end": {"line": 3},
            "goals_before": [{"id": "g0", "scope": "rawG", "target_text": needle,
                              "target_expr": const("PAndQ"), "hypotheses": []}],
            "goals_after": [{"id": "g1", "scope": "rawG1", "target_text": "P",
                             "target_expr": const("P"), "hypotheses": []},
                            {"id": "g2", "scope": "rawG2", "target_text": "Q",
                             "target_expr": const("Q"), "hypotheses": []}],
            "goal_assignments_after": [{"goal_id": "rawG", "assigned": True,
                                        "referenced_goal_ids": ["rawG1", "rawG2"]}]}


class RetrievalTests(unittest.TestCase):
    def setUp(self):
        tmp = tempfile.TemporaryDirectory()
        self.addCleanup(tmp.cleanup)
        self.base = Path(tmp.name)
        self.project = self.base / "project"
        (self.project / "OTSelector").mkdir(parents=True)
        (self.project / "OTSelector" / "Demo.lean").write_text("-- immutable fixture source\n")
        (self.project / "lean-toolchain").write_text("lean-test\n")
        (self.project / "lakefile.toml").write_text('name = "Demo"\n')
        (self.project / "lake-manifest.json").write_text('{"packages": []}\n')
        self.data = self.base / "index"
        self.store = Store(self.data / "atlas.sqlite3")
        self.addCleanup(self.store.close)
        self.manifest = source_manifest(self.project)
        records = [declaration("Demo.first"), triad("Demo.first"),
                   declaration("Demo.second"), triad("Demo.second"),
                   fragment("Demo.first", "one", "NeedleOne"),
                   fragment("Demo.first", "two", "NeedleTwo")]
        export = self.base / "export.jsonl"
        export.write_text("".join(json.dumps(record) + "\n" for record in records))
        self.store.import_jsonl(export, self.manifest)

    def hit(self, name):
        return next(hit for hit in self.store.search_lexical("Needle", view="statement")
                    if hit["name"] == name)

    def fragment_hit(self, query):
        return self.store.search_lexical(query, view="proof_state")[0]

    def state(self):
        return {"imports": ["OTSelector.Demo"], "context": "variable (u v : Nat)",
                "goal": "f v", "ordered_telescope": telescope(("u", "k", "v"), "Q"),
                "target_expr": app("f", var("v"))}

    def test_context_keeps_authoritative_telescope_and_explicit_role_projections(self):
        original = self.store.get_triad("Demo.first")
        packet = context_packet(self.store, {"query": "Needle", "lexical": [self.hit("Demo.first")]})
        entry = packet["references"][0]
        self.assertEqual(entry["ordered_telescope"], original["ordered_telescope"])
        self.assertEqual([b["id"] for b in entry["objects"]], ["b0", "b2"])
        self.assertEqual([b["id"] for b in entry["conditions"]], ["b1"])
        self.assertEqual(entry["conditions"][0]["depends_on"], ["b0"])
        self.assertEqual(entry["proof_detail"], original["proof_skeleton"])
        self.assertEqual(entry["source"]["source_hash"],
                         self.manifest["sources"]["OTSelector/Demo.lean"])

    def test_state_alignment_retains_condition_obligations_and_original_goal(self):
        state = self.state()
        before = deepcopy(state)
        packet = context_packet(self.store, {"query": "f v", "lexical": [self.hit("Demo.first")]},
                                state=state)
        match = packet["references"][0]["structural_match"]
        self.assertEqual(match["status"], "unverified")
        self.assertTrue(any(item["kind"] == "condition" for item in match["obligations"]))
        self.assertEqual(match["substitutions"][0]["source_id"], "b0")
        self.assertEqual(state, before)
        self.assertEqual(packet["task"], before)

    def test_semantic_and_lexical_lanes_are_retained_without_fusion_score(self):
        semantic = [{"name": "Demo.second", "similarity": 0.7},
                    {"name": "Demo.first", "similarity": 0.6}]

        class VectorFixture:
            def search(inner, query, client, store, **kwargs):
                self.assertEqual(kwargs["view"], "statement")
                return deepcopy(semantic)

        # Pattern retrieval has its own independently tested lane; isolate this
        # theorem-lane contract from any live embedding client.
        with patch("tools.proof_atlas.retrieval.search_patterns", return_value={"lexical": [], "semantic": []}):
            result = search(self.store, "Needle", view="statement",
                            vector_index=VectorFixture(), client=object())
        self.assertEqual(result["semantic"], semantic)
        self.assertEqual(len(result["lexical"]), 2)
        self.assertNotIn("fusion_score", json.dumps(result))
        packet = context_packet(self.store, result, limit=2)
        self.assertEqual([e["declaration"] for e in packet["references"]], ["Demo.second", "Demo.first"])
        self.assertTrue(all(e["retrieved_by"] == "semantic" for e in packet["references"]))
        self.assertTrue(all(e["retrieval_lanes"] == ["semantic", "lexical"]
                            for e in packet["references"]))

    def test_fragment_is_not_lost_after_same_declaration_semantic_hit(self):
        first = self.fragment_hit("NeedleOne")
        second = self.fragment_hit("NeedleTwo")
        retrieved = {"query": "Needle", "semantic": [self.hit("Demo.first")],
                     "lexical": [first, self.hit("Demo.second"), second, first]}
        entry = context_packet(self.store, retrieved, limit=1)["references"][0]
        self.assertEqual(len(entry["fragments"]), 2)
        self.assertEqual(entry["fragment"]["id"], first["metadata"]["fragment_id"])
        effect = entry["step_effect"]
        self.assertEqual(effect["solved_goals"], [])
        self.assertEqual(effect["new_goals"], ["rawG1", "rawG2"])
        self.assertEqual(effect["goal_dependencies"][0]["referenced_goal_ids"], ["rawG1", "rawG2"])

    def test_stale_vectors_preserve_lexical_results_and_context(self):
        from tools.proof_atlas.vectors import StaleVectorIndex

        class StaleVectors:
            def search(inner, *args, **kwargs):
                raise StaleVectorIndex("proof views changed")

        with patch("tools.proof_atlas.retrieval.search_patterns", return_value={}):
            result = search(self.store, "Needle", view="statement",
                            vector_index=StaleVectors(), client=object())
        self.assertEqual(len(result["lexical"]), 2)
        self.assertEqual(result["semantic"], [])
        self.assertEqual(result["semantic_status"],
                         {"status": "stale", "reason": "proof views changed"})
        packet = context_packet(self.store, result)
        self.assertEqual(len(packet["references"]), 2)
        self.assertTrue(all(item["retrieved_by"] == "lexical" for item in packet["references"]))

    def test_other_vector_failures_are_not_hidden(self):
        class BrokenVectors:
            def search(inner, *args, **kwargs):
                raise RuntimeError("unreadable vector matrix")

        with self.assertRaisesRegex(RuntimeError, "unreadable vector matrix"):
            search(self.store, "Needle", vector_index=BrokenVectors(), client=object())

    def test_pattern_replaces_only_explicit_template_placeholders(self):
        pattern = {"application_template": "exact use {{measure}} {{measure}} {{function}}",
                   "proof_detail": {"remaining_obligations": ["provide a bound"]}}
        state = {"context": "variable (measure function : Nat)", "goal": "measure = function",
                 "object_mapping": {"measure": "μ", "function": "f x"}}
        before = deepcopy(state)
        request = instantiate_pattern(pattern, state)
        self.assertEqual(request["candidate"], "exact use (μ) (μ) (f x)")
        self.assertEqual(request["context"], before["context"])
        self.assertEqual(request["goal"], before["goal"])
        self.assertEqual(request["remaining_obligations"], ["provide a bound"])
        self.assertEqual(state, before)
        explicit = instantiate_pattern(pattern, {**state, "candidate": "exact function"})
        self.assertEqual(explicit["candidate"], "exact function")

    def test_missing_or_malformed_mapping_has_useful_errors(self):
        pattern = {"application_template": "exact {{measure}} {{bound}}", "proof_detail": {}}
        with self.assertRaisesRegex(ValueError, "missing explicit object_mapping roles: bound"):
            instantiate_pattern(pattern, {"goal": "True", "object_mapping": {"measure": "μ"}})
        for mapping in ([], "x", {"measure": 3}):
            with self.subTest(mapping=mapping), self.assertRaisesRegex(ValueError, "object_mapping"):
                instantiate_pattern(pattern, {"goal": "True", "object_mapping": mapping})

    def test_declaration_transfer_remains_unverified_until_trial(self):
        state = self.state()
        result = transfer(self.store, state, declaration="Demo.first")
        self.assertEqual(result["status"], "unverified")
        self.assertEqual(result["structural_match"]["status"], "unverified")
        self.assertEqual(result["request"]["goal"], state["goal"])
        self.assertIn("apply Demo.first", result["request"]["candidate"])
        with patch("tools.proof_atlas.retrieval.verify_candidate",
                   return_value={"status": "partial", "remaining_goals": ["P v"]}) as trial:
            checked = transfer(self.store, state, declaration="Demo.first", check=True)
        self.assertEqual(checked["status"], "partial")
        self.assertEqual(trial.call_args.args[0]["goal"], state["goal"])

    def test_goal_only_query_does_not_require_existing_proof(self):
        self.assertEqual(query_text({"goal": "Integrable f μ"}).strip(), "Integrable f μ")

    def cli(self, command, state_text=None, *extra):
        args = [command, "--project-root", str(self.project), "--data-dir", str(self.data)]
        if state_text is not None:
            state_file = self.base / "request.json"
            state_file.write_text(state_text)
            if command == "match":
                args.extend([str(state_file), "--name", "Demo.first"])
            else:
                args.extend(["--state", str(state_file)])
        args.extend(extra)
        out, err = io.StringIO(), io.StringIO()
        with redirect_stdout(out), redirect_stderr(err):
            code = main(args)
        return code, out.getvalue(), err.getvalue()

    def test_cli_reports_invalid_json_and_state_shapes_without_traceback(self):
        for value in ("{invalid", "[]", '{"goal":3}', '{"object_mapping": []}'):
            with self.subTest(value=value):
                code, out, err = self.cli("context", value)
                self.assertEqual(code, 2)
                self.assertEqual(out, "")
                self.assertIn("proof-atlas:", err)
                self.assertNotIn("Traceback", err)

    def test_cli_match_rejects_nonstring_mapped_expressions(self):
        code, _, err = self.cli("match", '{"goal":"True", "object_mapping":{"x":1}}')
        self.assertEqual(code, 2)
        self.assertIn("object_mapping", err)

    def test_cli_match_requires_a_single_selection(self):
        with redirect_stderr(io.StringIO()), self.assertRaises(SystemExit) as error:
            main(["match", "request.json", "--pattern", "p", "--name", "Demo.first"])
        self.assertEqual(error.exception.code, 2)


if __name__ == "__main__":
    unittest.main()
