import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic

/-!
# Vanishing original physical cost of a square-root legal deficit

For the original scaling `N^(2/q)`, an expected `C sqrt(N)` missing-vertex
count costs at most `C (N^(2/q) D + T) sqrt(N) / N`. This tends to zero exactly
in the dimension regime used here, `q > 4`. No moment of the selected orphan
positions is assumed.
-/

open Filter
open scoped Topology

noncomputable section
namespace OTSelector.Reconstruction

/-- The exact original sample-size repair error. -/
def physicalLegalRepairError (q C D T : ℝ) (n : ℕ) : ℝ :=
  C * (((n + 1 : ℕ) : ℝ) ^ (2 / q) * D + T) *
    Real.sqrt ((n + 1 : ℕ) : ℝ) / ((n + 1 : ℕ) : ℝ)

/-- The error is nonnegative whenever its physical constants are. -/
theorem physicalLegalRepairError_nonneg {q C D T : ℝ}
    (hC : 0 ≤ C) (hD : 0 ≤ D) (hT : 0 ≤ T) (n : ℕ) :
    0 ≤ physicalLegalRepairError q C D T n := by
  unfold physicalLegalRepairError
  positivity

/-- The true physical orphan cost vanishes for every `q > 4`. -/
theorem tendsto_physicalLegalRepairError_zero {q : ℝ} (hq : 4 < q) (C D T : ℝ) :
    Tendsto (physicalLegalRepairError q C D T) atTop (𝓝 0) := by
  have hqpos : 0 < q := by linarith
  have hexp : 2 / q - 1 / 2 < 0 := by
    have h : 2 / q < (1 : ℝ) / 2 := (div_lt_iff₀ hqpos).mpr (by linarith)
    linarith
  have hN : Tendsto (fun n : ℕ ↦ ((n + 1 : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
  have hkin : Tendsto (fun n : ℕ ↦ ((n + 1 : ℕ) : ℝ) ^ (2 / q - 1 / 2))
      atTop (𝓝 0) := by
    have h := (tendsto_rpow_neg_atTop (y := -(2 / q - 1 / 2))
      (by linarith : 0 < -(2 / q - 1 / 2))).comp hN
    simpa only [neg_neg, Function.comp_def] using h
  have hprobe : Tendsto (fun n : ℕ ↦ ((n + 1 : ℕ) : ℝ) ^ (-(1 / 2 : ℝ)))
      atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 2)).comp hN
  have hlim := (hkin.const_mul (C * D)).add (hprobe.const_mul (C * T))
  simp only [mul_zero, add_zero] at hlim
  apply hlim.congr'
  apply Filter.Eventually.of_forall
  intro n
  let N : ℝ := ((n + 1 : ℕ) : ℝ)
  have hNpos : 0 < N := by dsimp [N]; positivity
  have hdiv (a : ℝ) : N ^ a / N = N ^ (a - 1) := by
    calc
      N ^ a / N = N ^ a / N ^ (1 : ℝ) := by rw [Real.rpow_one]
      _ = N ^ (a - 1) := (Real.rpow_sub hNpos a 1).symm
  have hk : N ^ (2 / q) * Real.sqrt N / N = N ^ (2 / q - 1 / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add hNpos, hdiv]
    congr 1
    ring
  have hp : Real.sqrt N / N = N ^ (-(1 / 2 : ℝ)) := by
    rw [Real.sqrt_eq_rpow, hdiv]
    congr 1
    norm_num
  change C * D * N ^ (2 / q - 1 / 2) + C * T * N ^ (-(1 / 2 : ℝ)) =
    C * (N ^ (2 / q) * D + T) * Real.sqrt N / N
  rw [← hk, ← hp]
  ring

end OTSelector.Reconstruction
