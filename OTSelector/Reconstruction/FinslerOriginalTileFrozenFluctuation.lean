import OTSelector.Finite.PlanResidual
import OTSelector.Analysis.NormalizedResidual
import OTSelector.Reconstruction.FinslerOriginalTileFluctuationBounds

/-!
# Frozen fluctuation: why the centered bound cannot vanish, and the weighted form

This module continues `FinslerOriginalTileFluctuationBounds.lean` and records a
**correction of the quantitative strategy**: the centered frozen fluctuation
`η_n` of task 120 does **not** tend to zero and cannot be proved to, because the
frozen entries are *not* small: they approximate the scaled actual slack costs

  `frozenCoreMatrix entry ≈ max((1-2ε) k · frozenPhysicalCost + t · probe, 0)`,

and the frozen physical cost is by construction within relative error `2ε` of the
actual slack cost `lengthEDist - u y + u x`
(`OriginalPopulationCoefficientCore.TaylorRootCover.physical_relative`).  The scale
`k` and the slack cost are comparable, so the entries are `O(1)` on the retained
edges; only the *weighted* sum against the plan deviation can be small.

The correct quantitative target is therefore the **weighted optimality-gap form**

  `|plan residual| ≤ ∑ i ∑ j, |A_ij - 1/(n+1)| · |E_ij| ≤ ρ_n,  ρ_n / (n+1) → 0,`

which this module isolates and proves sufficient (`tendsto_normalized_residual_zero_of_weighted`).
It also provides `maskedFrozenCost_abs_le`: the masked frozen entry is bounded by
the entry bound of the unmasked frozen matrix (the mask only zeroes entries).

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

/-- **The masked frozen cost is bounded by the entry bound of the frozen matrix.**
Masking only zeroes entries, so a uniform entry bound for the frozen cost matrix is
a uniform entry bound for every masked frozen cost. -/
theorem maskedFrozenCost_abs_le {n : ℕ} (Q : Set (Fin n × Fin n))
    (d : Matrix (Fin n) (Fin n) ℝ) {η : ℝ} (hη0 : 0 ≤ η)
    (hd : ∀ i j, |d i j| ≤ η) :
    ∀ i j, |maskedFrozenCost Q d i j| ≤ η := by
  intro i j
  by_cases h : (i, j) ∈ Q
  · rw [show maskedFrozenCost Q d i j = d i j from by
      rw [maskedFrozenCost]
      exact Set.indicator_of_mem (f := fun p : Fin n × Fin n => d p.1 p.2) h]
    exact hd i j
  · rw [show maskedFrozenCost Q d i j = 0 from by
      rw [maskedFrozenCost]
      exact Set.indicator_of_notMem (f := fun p : Fin n × Fin n => d p.1 p.2) h]
    rw [abs_zero]
    exact hη0

/-- **Weighted optimality-gap bound for the plan residual.**  The absolute plan
residual is at most the plan deviation weighted by the absolute frozen entries. -/
theorem abs_planResidual_le_weighted (m : ℕ)
    (A E : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ) :
    |∑ i, ∑ j, (A i j - 1 / ((m + 1 : ℕ) : ℝ)) * E i j| ≤
      ∑ i, ∑ j, |A i j - 1 / ((m + 1 : ℕ) : ℝ)| * |E i j| := by
  exact Finite.abs_sum_mul_le_weighted
    (fun i j ↦ A i j - 1 / ((m + 1 : ℕ) : ℝ)) E

/-- **Vanishing of the normalized plan residual from the weighted optimality-gap
bound.**  If the weighted plan deviation is bounded by `ρ_n` with
`ρ_n / (n+1) → 0`, then the normalized plan residual vanishes.  This is the
correct quantitative target for `TilePlanResidualVanishing` (replacing the
nonvanishing centered-fluctuation criterion). -/
theorem tendsto_normalized_residual_zero_of_weighted
    (R ρ : ℕ → ℝ) (hbound : ∀ n, |R n| ≤ ρ n)
    (hlim : Tendsto (fun n ↦ ρ n / ((n + 1 : ℕ) : ℝ)) atTop (𝓝 0)) :
    Tendsto (fun n ↦ R n / ((n + 1 : ℕ) : ℝ)) atTop (𝓝 0) := by
  exact Analysis.tendsto_div_zero_of_abs_le R ρ (fun n ↦ ((n + 1 : ℕ) : ℝ))
    (Eventually.of_forall fun _ ↦ by positivity) (Eventually.of_forall hbound) hlim

end OTSelector.Reconstruction
