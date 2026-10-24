"""Contract checks against Lean itself, including incomplete and invalid transfers."""

from pathlib import Path
import unittest

from tools.proof_atlas.verify import elaborate_state, load_patterns, verify_candidate
from tools.proof_atlas.structure import align_objects, alpha_fingerprint, alpha_normalize


PROJECT = Path(__file__).resolve().parents[1]


class ProofAtlasVerifyTests(unittest.TestCase):
    def check_trial(self, request, status):
        result = verify_candidate(request, project_root=PROJECT)
        self.assertEqual(result["status"], status, result)
        self.assertEqual(result["kernel_checked"], status == "complete", result)
        return result

    def test_curated_patterns_are_real_lean_proofs(self):
        for pattern in load_patterns():
            with self.subTest(pattern=pattern["id"]):
                example = pattern["proof_detail"]["example"]
                result = self.check_trial(example, example["expected_status"])
                self.assertEqual(result["remaining_goals"], [])

    @staticmethod
    def application(pattern, request):
        candidate = pattern["application_template"]
        for role, expression in request["object_mapping"].items():
            candidate = candidate.replace("{{" + role + "}}", expression)
        return dict(request, candidate=candidate)

    def test_application_templates_solve_when_conditions_are_present(self):
        for pattern in load_patterns():
            if pattern.get("kind") == "counterexample":
                continue
            with self.subTest(pattern=pattern["id"]):
                example = pattern["proof_detail"]["example"]
                self.check_trial(self.application(pattern, example), "complete")

    def test_application_templates_leave_missing_conditions_as_actual_goals(self):
        contexts = {
            "finite-measure-bounded-integrability": (
                "open MeasureTheory\nvariable {Ω : Type*} [MeasurableSpace Ω] "
                "(μ : Measure Ω) (f : Ω → ℝ) (C : ℝ)",
                ["IsFiniteMeasure μ", "AEStronglyMeasurable f μ"]),
            "eventual-upper-bound-passes-to-limit": (
                "open Filter\nopen scoped Topology\nvariable (a : ℕ → ℝ) (L B : ℝ) "
                "(hlimit : Tendsto a atTop (𝓝 L))",
                ["a n ≤ B"]),
            "nonnegative-real-strict-contraction-zero": (
                "variable (D κ : ℝ) (hD : 0 ≤ D)", ["κ < 1", "D ≤ κ * D"]),
        }
        for pattern in load_patterns():
            if pattern["id"] not in contexts:
                continue
            with self.subTest(pattern=pattern["id"]):
                context, obligations = contexts[pattern["id"]]
                request = dict(pattern["proof_detail"]["example"], context=context)
                result = self.check_trial(self.application(pattern, request), "partial")
                actual = "\n".join(result["remaining_goal_types"])
                for obligation in obligations:
                    self.assertIn(obligation, actual)

    def test_mapped_objects_have_actual_inferred_lean_types(self):
        result = self.check_trial({
            "imports": ["Mathlib"], "context": "variable (D : ℝ)",
            "goal": "D = D", "candidate": "rfl", "object_mapping": {"defect": "D"},
        }, "complete")
        self.assertEqual(result["typed_object_mapping"]["defect"]["inferred_type"], "ℝ")

    def test_bounded_integrability_keeps_only_missing_finite_measure_instance(self):
        pattern = next(p for p in load_patterns()
                       if p["id"] == "finite-measure-bounded-integrability")
        context = (
            "open MeasureTheory\nvariable {Ω : Type*} [MeasurableSpace Ω] "
            "(μ : Measure Ω) (f : Ω → ℝ) (C : ℝ) "
            "(hf : AEStronglyMeasurable f μ) (hbound : ∀ᵐ x ∂μ, ‖f x‖ ≤ C)"
        )
        request = dict(pattern["proof_detail"]["example"], context=context)
        result = self.check_trial(self.application(pattern, request), "partial")
        self.assertEqual(result["remaining_goal_types"], ["IsFiniteMeasure μ"])

    def test_bounded_integrability_subtype_keeps_missing_finite_measure_instance(self):
        pattern = next(p for p in load_patterns()
                       if p["id"] == "finite-measure-bounded-integrability")
        context = (
            "open MeasureTheory\nvariable {Ω : Type*} [MeasurableSpace Ω] (s : Set Ω) "
            "(μ : Measure s) (f : s → ℝ) (C : ℝ) "
            "(hf : AEStronglyMeasurable f μ) (hbound : ∀ᵐ x ∂μ, ‖f x‖ ≤ C)"
        )
        request = dict(pattern["proof_detail"]["example"], context=context)
        result = self.check_trial(self.application(pattern, request), "partial")
        self.assertEqual(result["remaining_goal_types"], ["IsFiniteMeasure μ"])

    def test_invalid_mapped_expression_rejects_even_an_independent_proof(self):
        self.check_trial({
            "imports": ["Mathlib"], "goal": "True", "candidate": "trivial",
            "object_mapping": {"defect": "unknownObject"},
        }, "rejected")

    def test_ennreal_infinite_defect_rejects_real_contraction_transfer(self):
        negative = next(p for p in load_patterns() if p.get("kind") == "counterexample")
        request = negative["proof_detail"]["invalid_transfer"]
        self.check_trial(request, "rejected")

    def test_partial_candidate_reports_actual_metavariable_goals(self):
        result = self.check_trial({
            "imports": ["Mathlib"],
            "context": "variable (P Q : Prop)",
            "goal": "P ∧ Q",
            "candidate": "constructor",
            "remaining_obligations": ["caller description is not Lean proof evidence"],
        }, "partial")
        self.assertEqual(result["remaining_goal_types"], ["P", "Q"])
        self.assertTrue(all("⊢" in goal for goal in result["remaining_goals"]))
        self.assertNotEqual(result["remaining_goals"], result["declared_remaining_obligations"])

    def test_dropping_tactic_goal_list_cannot_certify_a_proof(self):
        result = self.check_trial({
            "imports": ["Mathlib"],
            "goal": "False",
            "candidate": "run_tac Lean.Elab.Tactic.setGoals []",
        }, "partial")
        self.assertEqual(result["remaining_goal_types"], ["False"])

    def test_term_candidate_is_kernel_checked(self):
        self.check_trial({
            "imports": ["Mathlib"],
            "goal": "(2 : ℕ) + 2 = 4",
            "candidate": "rfl",
            "candidate_kind": "term",
        }, "complete")

    def test_unsolved_term_placeholder_is_partial(self):
        result = self.check_trial({
            "imports": ["Mathlib"],
            "goal": "True",
            "candidate": "refine ?_",
        }, "partial")
        self.assertEqual(result["remaining_goal_types"], ["True"])

    def test_placeholders_and_new_axiom_declarations_are_rejected_before_lean(self):
        for field, text in (("candidate", "sorry"), ("candidate", "admit"),
                            ("context", "axiom falseClaim : False")):
            with self.subTest(field=field, text=text):
                request = {"goal": "True", "candidate": "trivial", field: text}
                result = self.check_trial(request, "rejected")
                self.assertIsNone(result["validation"]["returncode"])
                self.assertIn("forbidden", result["reason"])

    def test_lean_error_cannot_be_mistaken_for_complete(self):
        result = self.check_trial({
            "imports": ["Mathlib"],
            "context": "def invalidContext : Nat := True",
            "goal": "True",
            "candidate": "trivial",
        }, "rejected")
        self.assertNotEqual(result["validation"]["returncode"], 0)


class ProofAtlasStateTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.state = elaborate_state({
            "imports": ["Mathlib"],
            "context": "variable (D κ : ℝ) (hD : 0 ≤ D)",
            "goal": "D = 0",
        }, PROJECT)
        if cls.state["status"] != "elaborated":
            raise AssertionError(cls.state)

    def test_state_exports_actual_ordered_binders_without_claiming_a_proof(self):
        state = self.state
        self.assertFalse(state["kernel_checked"])
        self.assertTrue(state["type_kernel_checked"])
        self.assertNotIn("candidate", state)
        binders = state["ordered_telescope"]
        self.assertEqual([b["id"] for b in binders], ["b0", "b1", "b2"])
        self.assertEqual([b["role"] for b in binders], ["object", "object", "condition"])
        self.assertEqual(binders[2]["depends_on"], ["b0"])
        self.assertEqual(binders[2]["type_text"], "0 ≤ D")
        self.assertEqual(state["target_expr"]["kind"], "dag")
        comparison = align_objects(state["target_expr"], state["target_expr"],
                                   pattern_binders=binders, target_binders=binders)
        self.assertEqual(comparison["status"], "exact", comparison)

    def test_renamed_context_has_the_same_alpha_structure(self):
        renamed = elaborate_state({
            "imports": ["Mathlib"],
            "context": "variable (defect factor : ℝ) (hnonnegative : 0 ≤ defect)",
            "goal": "defect = 0",
        }, PROJECT)
        self.assertEqual(renamed["status"], "elaborated", renamed)
        left = alpha_fingerprint(self.state["target_expr"], self.state["ordered_telescope"])
        right = alpha_fingerprint(renamed["target_expr"], renamed["ordered_telescope"])
        self.assertEqual(left, right)

    def test_generic_universes_are_parameters_not_unresolved_metavariables(self):
        state = elaborate_state({
            "imports": ["Mathlib"],
            "context": "variable {α : Type*} (x : α) (h : x = x)",
            "goal": "x = x",
        }, PROJECT)
        self.assertEqual(state["status"], "elaborated", state)
        self.assertTrue(state["universe_params"])
        alpha_normalize(state["target_expr"], state["ordered_telescope"],
                        state["universe_params"])

    def test_expression_budget_is_explicit_and_prevents_false_structural_matching(self):
        state = elaborate_state({
            "imports": ["Mathlib"], "context": "variable (D : ℝ)",
            "goal": "D = 0", "expr_budget": 1,
        }, PROJECT)
        self.assertEqual(state["status"], "elaborated", state)
        self.assertTrue(state["ast_truncated"])
        comparison = align_objects(state["target_expr"], state["target_expr"],
                                   pattern_binders=state["ordered_telescope"],
                                   target_binders=state["ordered_telescope"])
        self.assertEqual(comparison["status"], "unsupported", comparison)

    def test_untyped_goal_is_rejected(self):
        state = elaborate_state({"imports": ["Mathlib"], "goal": "unknownGoal"}, PROJECT)
        self.assertEqual(state["status"], "rejected", state)
        self.assertFalse(state["state_elaborated"])
        self.assertFalse(state["kernel_checked"])


if __name__ == "__main__":
    unittest.main()
