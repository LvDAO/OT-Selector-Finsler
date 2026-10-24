import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic

/-! Normalize the actual hole's Poisson energy and square-root count correction. -/

open Filter
open scoped Topology NNReal
noncomputable section
namespace OTSelector.Reconstruction

/-- The universal hole energy leaves only its fractional-mass term in the pressure limit. -/
theorem tendsto_originalOrientedShape_hole_upper_div
    {q : ℕ} (hq : 4 < q) (A B L h : ℝ) (hh : 0 ≤ h) :
    Tendsto (fun r : ℝ ↦
      (A * r ^ (2 / (q : ℝ)) * (r * h) ^ (1 - 2 / (q : ℝ)) +
        B * r ^ (2 / (q : ℝ)) * Real.sqrt (2 * r * h) + L * r * h) / r)
      atTop (𝓝 (A * h ^ (1 - 2 / (q : ℝ)) + L * h)) := by
  let a : ℝ := 2 / (q : ℝ)
  let γ : ℝ := 1 - a
  have hqR : (4 : ℝ) < q := by exact_mod_cast hq
  have hneg : a - (1 / 2 : ℝ) < 0 := by
    have hdiv : 2 / (q : ℝ) < (1 / 2 : ℝ) :=
      (div_lt_iff₀ (by linarith : (0 : ℝ) < q)).mpr (by linarith)
    dsimp only [a]
    linarith
  have hpower : Tendsto (fun r : ℝ ↦ r ^ (a - (1 / 2 : ℝ))) atTop (𝓝 0) := by
    simpa only [neg_neg] using
      tendsto_rpow_neg_atTop (y := -(a - (1 / 2 : ℝ))) (neg_pos.mpr hneg)
  have hmodel :=
    ((tendsto_const_nhds (x := A * h ^ γ)).add
      (hpower.const_mul (B * Real.sqrt (2 * h)))).add
        (tendsto_const_nhds (x := L * h))
  simp only [mul_zero, add_zero] at hmodel
  apply hmodel.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
  have hmain : r ^ a * (r * h) ^ γ = r * h ^ γ := by
    rw [Real.mul_rpow hr.le hh, ← mul_assoc, ← Real.rpow_add hr,
      show a + γ = 1 by dsimp only [γ]; ring, Real.rpow_one]
  have hA : A * r ^ a * (r * h) ^ γ = A * r * h ^ γ := by
    calc
      _ = A * (r ^ a * (r * h) ^ γ) := by ring
      _ = _ := by rw [hmain]; ring
  have hfactor : Real.sqrt (2 * r * h) = Real.sqrt (2 * h) * Real.sqrt r := by
    rw [show 2 * r * h = (2 * h) * r by ring, Real.sqrt_mul (by positivity)]
  have hsqrt : Real.sqrt r ≠ 0 := (Real.sqrt_pos.mpr hr).ne'
  change A * h ^ γ + B * Real.sqrt (2 * h) * r ^ (a - (1 / 2 : ℝ)) + L * h =
    (A * r ^ a * (r * h) ^ γ + B * r ^ a * Real.sqrt (2 * r * h) + L * r * h) / r
  rw [hA, Real.rpow_sub hr, ← Real.sqrt_eq_rpow, hfactor]
  field_simp [hr.ne', hsqrt]
  ring_nf
  rw [Real.sq_sqrt hr.le]
  ring

/-- The same exact normalization along the original nonnegative Poisson intensities. -/
theorem tendsto_originalOrientedShape_hole_upper_div_nnreal
    {q : ℕ} (hq : 4 < q) (A B L h : ℝ) (hh : 0 ≤ h) :
    Tendsto (fun r : ℝ≥0 ↦
      (A * (r : ℝ) ^ (2 / (q : ℝ)) * ((r : ℝ) * h) ^ (1 - 2 / (q : ℝ)) +
        B * (r : ℝ) ^ (2 / (q : ℝ)) * Real.sqrt (2 * (r : ℝ) * h) +
          L * (r : ℝ) * h) / (r : ℝ))
      atTop (𝓝 (A * h ^ (1 - 2 / (q : ℝ)) + L * h)) :=
  (tendsto_originalOrientedShape_hole_upper_div hq A B L h hh).comp
    (NNReal.tendsto_coe_atTop.mpr tendsto_id)

end OTSelector.Reconstruction
