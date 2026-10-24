import OTSelector.Reconstruction.FinslerOriginalTileMeanConvergence

/-!
# Plan-residual sign: optimality against the uniform plan

This module attacks the two named inputs of
`FinslerOriginalTileMeanConvergence.lean`:

(i) `UniformTileAverageConvergence` (the plan-free per-tile iid counting law);
(ii) `TilePlanResidualVanishing` (optimal-plan stability: the covariance of the
optimal plan weights with the frozen tile entries vanishes).

It proves the **structural sign law of the plan residual**: because the optimal
fractional plan minimizes the frozen cost over the whole doubly stochastic
polytope, and the uniform plan `1/(n+1)` belongs to that polytope, the optimal plan
costs no more than the uniform plan, so the plan-residual

  `R = ∑ i ∑ j, (A_ij - 1/(n+1)) E_ij`

is **nonpositive**, and the uniform-plan cost is exactly the plan-free average
`(1/(n+1)) ∑ i ∑ j E_ij`.  Consequently the expected plan residual is nonpositive:

  `∫ s, R(s) ∂sample n ≤ 0`.

This fixes the global sign of the plan-residual and reduces
`TilePlanResidualVanishing` to a magnitude/upper-bound statement.  The remaining
sub-gaps are stated exactly: the per-tile (as opposed to global) sign law needs
optimality of the plan for the tile-masked matrix, which is false in general and
must be replaced by the optimal-plan row-sum stability estimate; and the plan-free
iid counting law needs the repo iid counting laws applied to the masked frozen
kernel with the random probe and the `(n+1)^{2/q}` population normalization.

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

/-- **The uniform plan is doubly stochastic.** -/
theorem uniformPlan_mem_doublyStochastic (m : ℕ) :
    (fun _ _ : Fin (m + 1) ↦ 1 / ((m + 1 : ℕ) : ℝ)) ∈
      doublyStochastic ℝ (Fin (m + 1)) := by
  have hm : (((m + 1 : ℕ)) : ℝ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero m
  have hrow : ∀ i : Fin (m + 1), (∑ j : Fin (m + 1), (1 / ((m + 1 : ℕ) : ℝ))) = 1 := by
    intro i
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    exact mul_one_div_cancel hm
  rw [mem_doublyStochastic]
  refine ⟨fun i j ↦ by positivity, ?_, ?_⟩
  · ext i
    simp only [Matrix.mulVec, dotProduct, Pi.one_apply, mul_one]
    exact hrow i
  · ext j
    simp only [Matrix.vecMul, dotProduct, Pi.one_apply, one_mul]
    exact hrow j

/-- **The uniform-plan cost is the plan-free average.** -/
theorem fractionalAssignmentCost_uniformPlan (m : ℕ)
    (cost : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ) :
    fractionalAssignmentCost cost (fun _ _ ↦ 1 / ((m + 1 : ℕ) : ℝ)) =
      (1 / ((m + 1 : ℕ) : ℝ)) * ∑ i, ∑ j, cost i j := by
  simp only [fractionalAssignmentCost, Finset.mul_sum]

/-- **The plan residual is nonpositive for an optimal plan** (global sign law).

If `A` minimizes the frozen cost over the doubly stochastic polytope, then the
residual of the optimal plan against the uniform plan is nonpositive: the optimal
plan never pays more than the plan-free uniform average. -/
theorem planResidual_nonpos_of_optimal (m : ℕ)
    (cost A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ)
    (hopt : A ∈ doublyStochastic ℝ (Fin (m + 1)) ∧
      ∀ Q ∈ doublyStochastic ℝ (Fin (m + 1)),
        fractionalAssignmentCost cost A ≤ fractionalAssignmentCost cost Q) :
    ∑ i, ∑ j, (A i j - 1 / ((m + 1 : ℕ) : ℝ)) * cost i j ≤ 0 := by
  have hle : fractionalAssignmentCost cost A ≤
      fractionalAssignmentCost cost (fun _ _ ↦ 1 / ((m + 1 : ℕ) : ℝ)) :=
    hopt.2 _ (uniformPlan_mem_doublyStochastic m)
  rw [fractionalAssignmentCost_uniformPlan] at hle
  have hsplit : ∑ i, ∑ j, (A i j - 1 / ((m + 1 : ℕ) : ℝ)) * cost i j =
      (∑ i, ∑ j, A i j * cost i j) -
        (1 / ((m + 1 : ℕ) : ℝ)) * ∑ i, ∑ j, cost i j := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun j _ ↦ by ring
  rw [hsplit]
  simp only [fractionalAssignmentCost] at hle
  linarith

/-- **The expected plan residual is nonpositive.**

For a sample-wise optimal plan, the integrated plan residual of the frozen tile
cost is nonpositive; this is the global sign law of `TilePlanResidualVanishing`. -/
theorem integral_planResidual_nonpos
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (m : ℕ) (cost A : Ω → Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ)
    (hopt : ∀ s, A s ∈ doublyStochastic ℝ (Fin (m + 1)) ∧
      ∀ Q ∈ doublyStochastic ℝ (Fin (m + 1)),
        fractionalAssignmentCost (cost s) (A s) ≤ fractionalAssignmentCost (cost s) Q)
    (hint : Integrable (fun s ↦ ∑ i, ∑ j,
      (A s i j - 1 / ((m + 1 : ℕ) : ℝ)) * cost s i j) μ) :
    ∫ s, (∑ i, ∑ j,
      (A s i j - 1 / ((m + 1 : ℕ) : ℝ)) * cost s i j) ∂μ ≤ 0 := by
  have hzero : (0 : ℝ) = ∫ _s : Ω, (0 : ℝ) ∂μ := by simp
  rw [hzero]
  exact integral_mono_ae hint (integrable_const (0 : ℝ))
    (Eventually.of_forall fun s ↦ planResidual_nonpos_of_optimal m (cost s) (A s) (hopt s))

end OTSelector.Reconstruction
