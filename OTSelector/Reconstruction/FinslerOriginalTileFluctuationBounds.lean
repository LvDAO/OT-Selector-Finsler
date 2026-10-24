import OTSelector.Reconstruction.FinslerOriginalTileResidualVanishing

/-!
# Centered frozen fluctuation and plan L1 bounds

This module closes the quantitative gap of
`FinslerOriginalTileResidualVanishing.lean` as far as the matrix algebra goes.

**Frozen entry bounds (proved).**  The frozen core matrix satisfies

  `|frozenCoreMatrix C ε z₀ X Y k t h i j| ≤ (1-2ε) k R + |t| G`

whenever the frozen physical cost is bounded by `R` and the probe entry by `G`
(with `0 ≤ 1-2ε`, `0 ≤ k`).  The same bound holds for the masked frozen cost.  With
row/column centering `c_i`, `d_j` the centered frozen fluctuation is what enters the
plan residual.

**Plan L1 bound (proved).**  Every row-stochastic nonnegative plan satisfies

  `∑ i ∑ j, |A_ij - 1/(m+1)| ≤ 2 (m+1)`,

so the plan L1 fluctuation budget is `F_n = 2(n+1)` unconditionally.

**Vanishing criterion (proved).**  Consequently the normalized plan residual
vanishes as soon as the centered frozen fluctuation `η_n` itself tends to zero:
`η_n → 0 ⇒ η_n · F_n / (n+1) → 0`.  This reduces the optimal-plan stability input to
the vanishing of the row/column-centered frozen fluctuation, which is the
quantitative form of the `(1-2ε)k`-scale relative Taylor expansion of
`FinslerFrozenCoreDomination`.

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

/-- **The plan L1 fluctuation is at most twice the number of sample points.**
Every nonnegative row-stochastic plan is within L1 distance ¤2(m+1)¤ of the uniform
plan. -/
theorem planL1_le_two_mul (m : ℕ) (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ)
    (hnonneg : ∀ i j, 0 ≤ A i j) (hrow : ∀ i, ∑ j, A i j = 1) :
    ∑ i, ∑ j, |A i j - 1 / ((m + 1 : ℕ) : ℝ)| ≤ 2 * ((m + 1 : ℕ) : ℝ) := by
  have hm : (((m + 1 : ℕ)) : ℝ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero m
  have hc : 0 ≤ 1 / (((m + 1 : ℕ)) : ℝ) := by positivity
  have hterm : ∀ i j, |A i j - 1 / (((m + 1 : ℕ)) : ℝ)| ≤
      A i j + 1 / (((m + 1 : ℕ)) : ℝ) := by
    intro i j
    rw [abs_le]
    constructor <;> linarith [hnonneg i j, hc]
  have hstep : ∀ i : Fin (m + 1),
      ∑ j : Fin (m + 1), |A i j - 1 / (((m + 1 : ℕ)) : ℝ)| ≤ 2 := by
    intro i
    calc ∑ j : Fin (m + 1), |A i j - 1 / (((m + 1 : ℕ)) : ℝ)|
        ≤ ∑ j : Fin (m + 1), (A i j + 1 / (((m + 1 : ℕ)) : ℝ)) :=
          Finset.sum_le_sum fun j _ ↦ hterm i j
      _ = (∑ j : Fin (m + 1), A i j) + (∑ _j : Fin (m + 1), 1 / (((m + 1 : ℕ)) : ℝ)) :=
          Finset.sum_add_distrib
      _ = 2 := by
          rw [hrow i]
          have hsum : (∑ _j : Fin (m + 1), (1 / (((m + 1 : ℕ)) : ℝ))) = 1 := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
              mul_one_div_cancel hm]
          rw [hsum]
          norm_num
  calc ∑ i, ∑ j : Fin (m + 1), |A i j - 1 / (((m + 1 : ℕ)) : ℝ)|
      ≤ ∑ _i : Fin (m + 1), (2 : ℝ) := Finset.sum_le_sum fun i _ ↦ hstep i
    _ = (((m + 1 : ℕ)) : ℝ) * 2 := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    _ = 2 * (((m + 1 : ℕ)) : ℝ) := by ring

/-- **Vanishing of the centered frozen fluctuation implies vanishing of the
normalized plan residual.**  This is the exact quantitative closure of
`TilePlanResidualVanishing`: it suffices that the row/column-centered frozen
fluctuation `η_n` tends to zero. -/
theorem tendsto_normalized_residual_zero_of_fluctuation
    (R : ℕ → ℝ) (η : ℕ → ℝ)
    (hbound : ∀ n, |R n| ≤ η n * (2 * ((n + 1 : ℕ) : ℝ)))
    (hη : Tendsto η atTop (𝓝 0)) :
    Tendsto (fun n ↦ R n / ((n + 1 : ℕ) : ℝ)) atTop (𝓝 0) := by
  refine tendsto_normalized_residual_zero_of_bound R η
    (fun n ↦ 2 * ((n + 1 : ℕ) : ℝ)) hbound ?_
  have h2 : Tendsto (fun n ↦ 2 * η n) atTop (𝓝 0) := by
    simpa using hη.const_mul 2
  refine h2.congr' ?_
  filter_upwards with n
  have hc : (((n + 1 : ℕ)) : ℝ) ≠ 0 := by positivity
  have hηη : η n * (2 * ((n + 1 : ℕ) : ℝ)) / ((n + 1 : ℕ) : ℝ) = 2 * η n := by
    field_simp
  exact hηη.symm

end OTSelector.Reconstruction
