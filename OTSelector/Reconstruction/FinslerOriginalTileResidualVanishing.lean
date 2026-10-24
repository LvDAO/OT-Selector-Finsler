import OTSelector.Finite.PlanResidual
import OTSelector.Analysis.NormalizedResidual
import OTSelector.Reconstruction.FinslerOriginalTilePlanResidual

/-!
# Plan residual magnitude: row-sum stability and the vanishing criterion

This module attacks the remaining inputs of `FinslerOriginalTilePlanResidual.lean`:
the *magnitude* and *vanishing* of the plan residual (only its global sign was
proved there), and it isolates the exact quantitative criterion for
`TilePlanResidualVanishing`.

**Row-sum stability (proved).**  Because a doubly stochastic plan `A` has row and
column sums one, adding a row constant `c_i` and a column constant `d_j` to the
frozen cost does not change the plan residual:

  `∑ i ∑ j, (A_ij - u) E_ij = ∑ i ∑ j, (A_ij - u) (E_ij + c_i + d_j),  u = 1/(n+1).`

Hence only the *centered* frozen fluctuations matter for the residual.

**Magnitude bound (proved).**  If the centered frozen entries are bounded by
`η` and the L1 distance of the plan weights to the uniform plan is at most `F`,
then the residual is bounded by `η · F`.

**Vanishing criterion (proved).**  Consequently the normalized residual
`(1/(n+1)) · R_n` vanishes as soon as `η_n · F_n / (n+1) -> 0`.  This is the exact
quantitative criterion for `TilePlanResidualVanishing`: `η_n` is the centered
frozen fluctuation bound (from the `(1-2ε)k`-scale Taylor expansion of the frozen
physical cost plus the probe term) and `F_n` is the L1 fluctuation of the optimal
plan weights around the uniform plan.

The remaining sub-gaps are stated exactly: the quantitative centered fluctuation
bound for the frozen kernel, the plan L1 fluctuation bound, and (for the plan-free
tile average) the per-tile iid counting law applied to the masked frozen kernel.

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

/-! ## Row-sum stability of the plan residual -/

/-- **The plan residual is invariant under adding row and column constants to the
frozen cost.**  Only the centered frozen fluctuations contribute to the residual;
this is the row-sum/column-sum stability identity reducing the magnitude estimate
to centered quantities. -/
theorem planResidual_add_rowColConstants (m : ℕ)
    (cost A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ)
    (hrow : ∀ i, ∑ j, A i j = 1) (hcol : ∀ j, ∑ i, A i j = 1)
    (c d : Fin (m + 1) → ℝ) :
    ∑ i, ∑ j, (A i j - 1 / ((m + 1 : ℕ) : ℝ)) * (cost i j + (c i + d j)) =
      ∑ i, ∑ j, (A i j - 1 / ((m + 1 : ℕ) : ℝ)) * cost i j := by
  apply Finite.sum_mul_add_rowColumn
  · intro i
    rw [Finset.sum_sub_distrib, hrow i]
    simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      Nat.cast_add, Nat.cast_one, ne_of_gt (by positivity : (0 : ℝ) < m + 1)]
  · intro j
    rw [Finset.sum_sub_distrib, hcol j]
    simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      Nat.cast_add, Nat.cast_one, ne_of_gt (by positivity : (0 : ℝ) < m + 1)]

/-- **Magnitude bound for the plan residual.**  If the centered frozen entries are
bounded by `η` and the L1 distance of the plan weights from the uniform plan is at
most `F`, then the plan residual is bounded by `η · F`. -/
theorem abs_planResidual_le_centered (m : ℕ)
    (cost A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ)
    (hrow : ∀ i, ∑ j, A i j = 1) (hcol : ∀ j, ∑ i, A i j = 1)
    (c d : Fin (m + 1) → ℝ) {η F : ℝ} (hη0 : 0 ≤ η)
    (hη : ∀ i j, |cost i j + (c i + d j)| ≤ η)
    (hF : ∑ i, ∑ j, |A i j - 1 / ((m + 1 : ℕ) : ℝ)| ≤ F) :
    |∑ i, ∑ j, (A i j - 1 / ((m + 1 : ℕ) : ℝ)) * cost i j| ≤ η * F := by
  have hzero (v : Fin (m + 1) → ℝ) (hv : ∑ j, v j = 1) :
      ∑ j, (v j - 1 / ((m + 1 : ℕ) : ℝ)) = 0 := by
    rw [Finset.sum_sub_distrib, hv]
    simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      Nat.cast_add, Nat.cast_one, ne_of_gt (by positivity : (0 : ℝ) < m + 1)]
  exact Finite.abs_sum_mul_le_of_centered
    (fun i j ↦ A i j - 1 / ((m + 1 : ℕ) : ℝ)) cost
    (fun i ↦ hzero _ (hrow i)) (fun j ↦ hzero _ (hcol j)) c d hη0 hη hF

/-- **Vanishing criterion for the normalized plan residual.**  If the residual is
bounded by `η_n · F_n` and `η_n · F_n / (n+1) -> 0`, then the normalized residual
vanishes: this is the exact quantitative criterion for
`TilePlanResidualVanishing`. -/
theorem tendsto_normalized_residual_zero_of_bound
    (R : ℕ → ℝ) (η F : ℕ → ℝ)
    (hbound : ∀ n, |R n| ≤ η n * F n)
    (hlim : Tendsto (fun n ↦ η n * F n / ((n + 1 : ℕ) : ℝ)) atTop (𝓝 0)) :
    Tendsto (fun n ↦ R n / ((n + 1 : ℕ) : ℝ)) atTop (𝓝 0) := by
  exact Analysis.tendsto_div_zero_of_abs_le R (fun n ↦ η n * F n)
    (fun n ↦ ((n + 1 : ℕ) : ℝ))
    (Eventually.of_forall fun _ ↦ by positivity) (Eventually.of_forall hbound) hlim

end OTSelector.Reconstruction
