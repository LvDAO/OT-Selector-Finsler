"""Contract tests for conservative Lean-expression structural operations."""

import json
import unittest

from tools.proof_atlas.structure import (
    UnsupportedExpression,
    align_objects,
    alpha_fingerprint,
    anti_unify,
    compare_structure,
    exact_clusters,
    exact_structure_clusters,
    step_effect,
)


def const(name):
    return {"kind": "const", "name": name, "levels": []}


def var(name):
    return {"kind": "fvar", "id": name}


def app(name, *arguments):
    result = const(name) if isinstance(name, str) else name
    for argument in arguments:
        result = {"kind": "app", "fn": result, "arg": argument}
    return result


def nat(value):
    return {"kind": "lit", "literal_kind": "nat", "value": value}


def binder(identity, type_expr=None, *, index=0, role="object", name=None, **extra):
    return {"id": identity, "index": index, "name": name or identity,
            "binder_mode": "default", "role": role, "type_expr": type_expr or const("Nat"),
            "depends_on": [], **extra}


def context(*names):
    return [binder(name, index=index) for index, name in enumerate(names)]


def goal(identity, target, hypotheses=(), **extra):
    return {"id": identity, "target_expr": target, "hypotheses": list(hypotheses), **extra}


def small_tree(expr):
    """Expand only the deliberately tiny DAG fixtures used in shape assertions."""
    if expr.get("kind") != "dag":
        return expr
    def visit(node):
        if isinstance(node, dict):
            if node.get("kind") == "ref":
                return visit(expr["nodes"][node["id"]])
            return {key: visit(value) for key, value in node.items()}
        if isinstance(node, list):
            return [visit(value) for value in node]
        return node
    return visit(expr["nodes"][expr["root"]])


def shared_binary_dag(depth, leaf=None):
    nodes = [leaf or nat(0), const("pair")]
    previous = 0
    for _ in range(depth):
        nodes.append({"kind": "app", "fn": {"kind": "ref", "id": 1},
                      "arg": {"kind": "ref", "id": previous}})
        nodes.append({"kind": "app", "fn": {"kind": "ref", "id": len(nodes) - 1},
                      "arg": {"kind": "ref", "id": previous}})
        previous = len(nodes) - 1
    return {"kind": "dag", "root": previous, "nodes": nodes}


class FingerprintTests(unittest.TestCase):
    def test_names_and_metadata_are_alpha_invariant(self):
        left = app("Nat.succ", var("x"))
        right = {"kind": "mdata", "expr": app("Nat.succ", var("different"))}
        self.assertEqual(alpha_fingerprint(left, context("x")),
                         alpha_fingerprint(right, context("different")))

    def test_binder_order_type_and_mode_remain(self):
        a = [binder("x", const("Real")), binder("y", const("ENNReal"), index=1)]
        b = [binder("y", const("ENNReal")), binder("x", const("Real"), index=1)]
        self.assertNotEqual(alpha_fingerprint(const("True"), a),
                            alpha_fingerprint(const("True"), b))
        implicit = [{**a[0], "binder_mode": "implicit"}, a[1]]
        self.assertNotEqual(alpha_fingerprint(const("True"), a),
                            alpha_fingerprint(const("True"), implicit))

    def test_forall_and_exists_are_different(self):
        universal = {"kind": "forallE", "binder_name": "x", "binder_info": "default",
                     "type": const("Nat"), "body": const("True")}
        existential = app("Exists", {"kind": "lam", "binder_name": "x",
                                     "binder_info": "default", "type": const("Nat"),
                                     "body": const("True")})
        self.assertNotEqual(alpha_fingerprint(universal), alpha_fingerprint(existential))

    def test_proof_syntax_is_not_definitional_equality(self):
        proof = app("Eq.refl", nat(0))
        wrapped = app("id", proof)
        self.assertNotEqual(alpha_fingerprint(proof), alpha_fingerprint(wrapped))

    def test_universe_alpha_names_and_sharing(self):
        def universe(name):
            return {"kind": "const", "name": "List", "levels": [{"kind": "param", "name": name}]}
        self.assertEqual(alpha_fingerprint(universe("u"), universe_params=["u"]),
                         alpha_fingerprint(universe("v"), universe_params=["v"]))
        self.assertNotEqual(alpha_fingerprint(universe("u"), universe_params=["u"]),
                            alpha_fingerprint(universe("u"), universe_params=["u", "unused"]))
        self.assertNotEqual(alpha_fingerprint(const("Real")), alpha_fingerprint(const("ENNReal")))

    def test_let_values_are_retained(self):
        value = {"kind": "letE", "binder_name": "x", "type": const("Nat"), "value": nat(1),
                 "body": {"kind": "bvar", "index": 0}, "nondep": False}
        self.assertNotEqual(alpha_fingerprint(value), alpha_fingerprint({**value, "value": nat(2)}))

    def test_incomplete_and_unbound_expressions_are_explicit(self):
        for expr in [{"kind": "truncated", "fingerprint": "abc"},
                     {"kind": "mvar", "id": "?m.1"}, var("missing")]:
            self.assertEqual(compare_structure(expr, expr)["status"], "unsupported")
        with self.assertRaises(UnsupportedExpression):
            alpha_fingerprint(app("f", nat(0)), max_nodes=1)


class MatchingTests(unittest.TestCase):
    def test_object_alignment_reports_explicit_substitution(self):
        ctx = context("x", "y")
        result = align_objects(app("f", var("x")), app("f", var("y")),
                               pattern_binders=ctx, target_binders=ctx)
        self.assertEqual(result["status"], "compatible")
        self.assertEqual(result["substitutions"][0]["source_id"], "x")
        self.assertEqual(result["substitutions"][0]["target_expr"], var("b1"))
        self.assertEqual(result["obligations"], [])

    def test_repeated_object_requires_same_substitution(self):
        ctx = context("x", "y", "z")
        result = align_objects(app("f", var("x"), var("x")),
                               app("f", var("y"), var("z")),
                               pattern_binders=ctx, target_binders=ctx)
        self.assertEqual(result["status"], "incompatible")

    def test_rigid_types_and_constants_do_not_align(self):
        result = align_objects(var("x"), var("y"),
                               pattern_binders=[binder("x", const("Real"))],
                               target_binders=[binder("y", const("ENNReal"))])
        self.assertEqual(result["status"], "incompatible")
        self.assertEqual(anti_unify(const("Real"), const("ENNReal"))["status"], "incompatible")

    def test_conditions_are_obligations_not_discarded(self):
        a = [binder("x"), binder("h", app("P", var("x")), index=1, role="condition")]
        b = [binder("y"), binder("k", app("Q", var("y")), index=1, role="condition")]
        result = align_objects(app("f", var("x")), app("f", var("y")),
                               pattern_binders=a, target_binders=b)
        self.assertEqual(result["status"], "unverified")
        self.assertTrue(any(item["kind"] == "condition" for item in result["obligations"]))

    def test_missing_subterm_type_remains_unverified(self):
        ctx = context("x", "y")
        result = align_objects(app("f", var("x")), app("f", app("g", var("y"))),
                               pattern_binders=ctx, target_binders=ctx)
        self.assertEqual(result["status"], "unverified")
        self.assertTrue(any(item["kind"] == "type" for item in result["obligations"]))

    def test_higher_order_matching_is_unsupported(self):
        ctx = context("x", "y")
        result = align_objects(app("f", var("x")), app(var("x"), var("y")),
                               pattern_binders=ctx, target_binders=ctx)
        self.assertEqual(result["status"], "unsupported")
        quantified = {"kind": "forallE", "binder_name": "x", "binder_info": "default",
                      "type": const("Real"), "body": const("True")}
        self.assertEqual(anti_unify(quantified, {**quantified, "body": const("False")})["status"],
                         "unsupported")

    def test_anti_unification_reuses_typed_disagreement_holes(self):
        result = anti_unify(app("f", var("x"), var("x")), app("f", nat(1), nat(1)),
                            left_binders=context("x"))
        self.assertEqual(len(result["substitutions"]), 1)
        self.assertEqual(result["substitutions"][0]["type_expr"], const("Nat"))
        pattern = small_tree(result["pattern"])
        self.assertEqual(pattern["arg"]["id"], "H0")
        self.assertEqual(pattern["fn"]["arg"]["id"], "H0")

    def test_anti_unification_checks_context_types_even_for_same_variable_index(self):
        result = anti_unify(var("x"), var("y"),
                            left_binders=[binder("x", const("Real"))],
                            right_binders=[binder("y", const("ENNReal"))])
        self.assertEqual(result["status"], "incompatible")


class DagTests(unittest.TestCase):
    def test_tree_and_dag_have_identical_syntax_fingerprint(self):
        dag = shared_binary_dag(3)
        self.assertEqual(alpha_fingerprint(dag), alpha_fingerprint(small_tree(dag)))

    def test_non_postorder_references_are_supported(self):
        dag = {"kind": "dag", "root": 0, "nodes": [
            {"kind": "app", "fn": {"kind": "ref", "id": 2},
             "arg": {"kind": "ref", "id": 1}}, nat(1), const("f")]}
        self.assertEqual(alpha_fingerprint(dag), alpha_fingerprint(app("f", nat(1))))

    def test_invalid_cyclic_and_out_of_scope_references_are_rejected(self):
        fixtures = [
            {"kind": "dag", "root": 2, "nodes": [nat(1)]},
            {"kind": "dag", "root": 0, "nodes": [{"kind": "ref", "id": 0}]},
            {"kind": "dag", "root": 0, "nodes": [nat(1), {"kind": "ref", "id": 9}]},
            {"kind": "ref", "id": 0},
        ]
        for expr in fixtures:
            with self.subTest(expr=expr):
                self.assertEqual(compare_structure(expr, expr)["status"], "unsupported")

    def test_exponential_tree_sharing_stays_compact_in_hashing_and_matching(self):
        # The expanded tree has billions of leaves; only 72 nodes are exported.
        left, right = shared_binary_dag(35, var("x")), shared_binary_dag(35, nat(1))
        self.assertEqual(compare_structure(left, left, left_binders=context("x"),
                                           right_binders=context("x"))["status"], "exact")
        result = anti_unify(left, right, left_binders=context("x"), max_nodes=512)
        self.assertEqual(len(result["substitutions"]), 1)
        self.assertEqual(result["pattern"]["kind"], "dag")
        self.assertLess(len(json.dumps(result)), 50000)

    def test_dag_budget_and_truncated_nodes_are_explicit(self):
        dag = shared_binary_dag(5)
        self.assertEqual(compare_structure(dag, dag, max_nodes=3)["status"], "unsupported")
        truncated = {"kind": "dag", "root": 0,
                     "nodes": [{"kind": "truncated", "fingerprint": "omitted"}]}
        self.assertEqual(anti_unify(truncated, truncated)["status"], "unsupported")


class InventoryTests(unittest.TestCase):
    def test_type_clusters_skip_missing_and_truncated(self):
        records = [{"name": "a", "type_expr": app("f", var("x")), "ordered_telescope": context("x")},
                   {"name": "b", "type_expr": app("f", var("y")), "ordered_telescope": context("y")},
                   {"name": "c", "type_expr": {"kind": "truncated", "fingerprint": "x"}},
                   {"name": "no_ast", "type_text": "f x"}]
        result = exact_clusters(records)
        self.assertEqual([m["name"] for m in result["clusters"][0]["members"]], ["a", "b"])
        self.assertEqual(len(result["skipped"]), 2)

    def test_structure_field_names_are_ignored_but_types_are_preserved(self):
        result = exact_structure_clusters([
            {"name": "A", "fields": [binder("x", name="first")]},
            {"name": "B", "fields": [binder("different", name="other")]},
            {"name": "C", "fields": [binder("x", const("Real"))]},
        ])
        self.assertEqual(len(result["clusters"]), 1)
        self.assertEqual([m["name"] for m in result["clusters"][0]["members"]], ["A", "B"])


class StepEffectTests(unittest.TestCase):
    def test_local_alias_shift_is_addition_not_target_change(self):
        old = [binder("h0", fvar_id="rawX")]
        new = [binder("h0", const("True"), role="condition", fvar_id="rawH"),
               binder("h1", index=1, fvar_id="rawX")]
        result = step_effect([goal("g", var("h0"), old)], [goal("g", var("h1"), new)])
        effect = result["persisting_goals"][0]
        self.assertEqual(len(effect["hypotheses_added"]), 1)
        self.assertEqual(effect["hypotheses_removed"], [])
        self.assertEqual(effect["hypotheses_changed"], [])
        self.assertEqual(effect["target"]["status"], "exact")

    def test_hypothesis_removal_and_type_change(self):
        old = context("x", "h")
        new = [binder("x", const("Real"))]
        result = step_effect([goal("g", const("True"), old)], [goal("g", const("False"), new)])
        effect = result["persisting_goals"][0]
        self.assertEqual(effect["hypotheses_removed"][0]["id"], "h")
        self.assertEqual(effect["hypotheses_changed"][0]["id"], "x")
        self.assertEqual(effect["target"]["status"], "unverified")

    def test_subgoals_are_not_reported_as_independently_solved(self):
        result = step_effect({"goals_before": [goal("g", const("P"))],
                              "goals_after": [goal("g1", const("Q")), goal("g2", const("R"))],
                              "goal_assignments_after": [{"goal_id": "g", "assigned": True,
                                                           "referenced_goal_ids": ["g1", "g2"]}]})
        self.assertEqual(result["solved_goals"], [])
        self.assertEqual(result["removed_goals"], ["g"])
        self.assertEqual(result["new_goals"], ["g1", "g2"])
        self.assertEqual(result["goal_dependencies"][0]["referenced_goal_ids"], ["g1", "g2"])
        self.assertEqual(result["subgoal_count_change"], 1)

    def test_no_remaining_goal_records_completion(self):
        result = step_effect([goal("g", const("True"))], [])
        self.assertEqual(result["solved_goals"], ["g"])

    def test_let_value_changes_are_separate_from_hypothesis_types(self):
        old = [binder("x", is_let=True, value_expr=nat(1))]
        new = [binder("x", is_let=True, value_expr=nat(2))]
        effect = step_effect([goal("g", const("True"), old)],
                             [goal("g", const("True"), new)])["persisting_goals"][0]
        self.assertEqual(effect["hypotheses_changed"][0]["comparison"]["status"], "exact")
        self.assertEqual(effect["hypotheses_changed"][0]["fields_changed"], ["value_expr"])


if __name__ == "__main__":
    unittest.main()
