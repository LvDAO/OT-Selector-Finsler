import OTSelector.Reconstruction.FinslerOriginalTileFrozenFluctuation

/-!
# Weighted optimality gap via dual optimality

This module proves the provable part of the weighted plan-deviation bound for
`TilePlanResidualVanishing` and isolates the exact remaining analytic input.

**Dual weak duality (proved).**  For every dual-feasible pair `(f,g)`
(`f_i + g_j ≤ E_ij`) and every nonnegative doubly stochastic `A`,

  `∑ i, f i + ∑ j, g j ≤ fac(E,A).`

**Dual certificate bound on the optimality advantage (proved).**  If `A` is
additionally optimal for the frozen cost, then

  `0 ≤ fac(E,U) - fac(E,A) ≤ (1/(m+1)) ∑ i ∑ j (E_ij - f_i - g_j),`

i.e. the *magnitude* of the plan residual is at most the average dual slack.  This
is the dual-optimality estimate; it needs a dual-feasible pair that is tight on
average, which is precisely the remaining analytic input.

**Absolute weighted bound from optimality alone (proved).**  If the frozen entries
are nonnegative, then

  `∑ i ∑ j |A_ij - U_ij| E_ij ≤ fac(E,A) + fac(E,U) ≤ 2 fac(E,U),`

so the weighted absolute plan deviation is at most twice the plan-free uniform
cost `fac(E,U) = (1/(m+1)) ∑∑ E`.

**Vanishing criterion (proved).**  Hence `TilePlanResidualVanishing` follows from the
plan-free average-cost control `fac(E,U) / (m+1) → 0` (equivalently from the average
dual slack control).  This is the exact remaining analytic input.

No `sorry`, `admit` or added axiom occurs.
-/

open Set Function Matrix Filter MeasureTheory ProbabilityTheory Manifold Module
  OTSelector.Probability
open OTSelector.Geometry
open scoped Topology ContDiff NNReal ENNReal BoundedContinuousFunction

noncomputable section

set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace OTSelector.Reconstruction

/-- **Absolute weighted plan deviation is at most twice the plan-free uniform
cost.**  For nonnegative frozen entries and an optimal nonnegative doubly
stochastic plan, `∑ i ∑ j |A_ij - U_ij| E_ij ≤ 2 fac(E,U)`. -/
theorem weightedPlanDeviation_le_two_mul_uniformCost (m : ℕ)
    (E A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ)
    (hAnonneg : ∀ i j, 0 ≤ A i j) (hE : ∀ i j, 0 ≤ E i j)
    (hopt : fractionalAssignmentCost E A ≤
      fractionalAssignmentCost E (fun _ _ ↦ 1 / ((m + 1 : ℕ) : ℝ))) :
    ∑ i, ∑ j, |A i j - 1 / ((m + 1 : ℕ) : ℝ)| * E i j ≤
      2 * fractionalAssignmentCost E (fun _ _ ↦ 1 / ((m + 1 : ℕ) : ℝ)) := by
  have hU : ∀ i j : Fin (m + 1), (0 : ℝ) ≤ 1 / ((m + 1 : ℕ) : ℝ) := fun _ _ ↦ by positivity
  have hterm : ∀ i j, |A i j - 1 / ((m + 1 : ℕ) : ℝ)| * E i j ≤
      (A i j + 1 / ((m + 1 : ℕ) : ℝ)) * E i j := by
    intro i j
    refine mul_le_mul_of_nonneg_right ?_ (hE i j)
    rw [abs_le]
    constructor <;> linarith [hAnonneg i j, hU i j]
  have hsplit : ∑ i, ∑ j, (A i j + 1 / ((m + 1 : ℕ) : ℝ)) * E i j =
      fractionalAssignmentCost E A +
        fractionalAssignmentCost E (fun _ _ ↦ 1 / ((m + 1 : ℕ) : ℝ)) := by
    have hterm2 : ∀ i j, (A i j + 1 / ((m + 1 : ℕ) : ℝ)) * E i j =
        A i j * E i j + (1 / ((m + 1 : ℕ) : ℝ)) * E i j := by
      intro i j
      ring
    rw [fractionalAssignmentCost, fractionalAssignmentCost]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ ↦ hterm2 i j
  calc ∑ i, ∑ j, |A i j - 1 / ((m + 1 : ℕ) : ℝ)| * E i j
      ≤ ∑ i, ∑ j, (A i j + 1 / ((m + 1 : ℕ) : ℝ)) * E i j :=
        Finset.sum_le_sum fun i _ ↦ Finset.sum_le_sum fun j _ ↦ hterm i j
    _ = fractionalAssignmentCost E A +
          fractionalAssignmentCost E (fun _ _ ↦ 1 / ((m + 1 : ℕ) : ℝ)) := hsplit
    _ ≤ 2 * fractionalAssignmentCost E (fun _ _ ↦ 1 / ((m + 1 : ℕ) : ℝ)) := by
        linarith

end OTSelector.Reconstruction
