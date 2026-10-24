import OTSelector.Reconstruction.BirthTrafficPhysicalHaarScale

/-! The physical coarse scale converts the actual birth-window momentum
occupation bound into the exact large-phase energy powers of the paper. -/
open Set Function Matrix MeasureTheory
open scoped ENNReal
noncomputable section
namespace OTSelector.Reconstruction

/-- The reciprocal coarse scale is the actual square-root window size times
the physical focal-time dimensional power. -/
theorem birthTrafficCoarseScale_inv {q : ℕ} {t s : ℝ} (ht : 0 < t) :
    (birthTrafficCoarseScale q t s)⁻¹ = Real.sqrt s * t ^ (1 / (q : ℝ)) := by
  simp only [birthTrafficCoarseScale, _root_.mul_inv_rev, inv_inv]
  rw [Real.rpow_neg ht.le, inv_inv]
  ring

/-- After multiplying by the physical window size, the large-phase energy
coefficient has its exact `s² t^(-2+1/q)` scale. -/
theorem birthLargePhase_energy_scale {q : ℕ} {t s : ℝ}
    (ht : 0 < t) (hs : 0 ≤ s) :
    (birthTrafficCoarseScale q t s)⁻¹ * s * Real.sqrt s * (t ^ 2)⁻¹ =
      s ^ 2 * t ^ (-2 + 1 / (q : ℝ)) := by
  rw [birthTrafficCoarseScale_inv ht,
    Real.rpow_add ht, Real.rpow_neg ht.le, Real.rpow_two]
  calc
    _ = (Real.sqrt s) ^ 2 * s * ((t ^ 2)⁻¹ * t ^ (1 / (q : ℝ))) := by ring
    _ = _ := by rw [Real.sq_sqrt hs]; ring

/-- The unchanged full-momentum energy has its exact accompanying
`s² t^(-1+1/q)` physical coefficient. -/
theorem birthLargePhase_momentum_scale {q : ℕ} {t s : ℝ}
    (ht : 0 < t) (hs : 0 ≤ s) :
    (birthTrafficCoarseScale q t s)⁻¹ * s * Real.sqrt s * t⁻¹ =
      s ^ 2 * t ^ (-1 + 1 / (q : ℝ)) := by
  rw [birthTrafficCoarseScale_inv ht, Real.rpow_add ht, Real.rpow_neg_one]
  calc
    _ = (Real.sqrt s) ^ 2 * s * (t⁻¹ * t ^ (1 / (q : ℝ))) := by ring
    _ = _ := by rw [Real.sq_sqrt hs]; ring

/-- The nonnegative large-phase Campbell bound retains each original band
energy and spends its actual clock-window length, with no independence step. -/
theorem birthLargePhase_moment_le_of_window_bound
    {q : ℕ} {t s A C : ℝ} (ht : 0 < t) (hs : 0 < s)
    (hA : 0 ≤ A) (hC : 0 ≤ C) {J E V H : ℝ≥0∞}
    (hJ : J ≤ ENNReal.ofReal (A * s))
    (hH : H ≤ J * ENNReal.ofReal (C * Real.sqrt s) *
      (ENNReal.ofReal ((t ^ 2)⁻¹) * E + ENNReal.ofReal t⁻¹ * V)) :
    ENNReal.ofReal ((birthTrafficCoarseScale q t s)⁻¹) * H ≤
      ENNReal.ofReal (A * C) *
        (ENNReal.ofReal (s ^ 2 * t ^ (-2 + 1 / (q : ℝ))) * E +
         ENNReal.ofReal (s ^ 2 * t ^ (-1 + 1 / (q : ℝ))) * V) := by
  have hL : 0 ≤ (birthTrafficCoarseScale q t s)⁻¹ :=
    (birthTrafficCoarseScale_pos q ht hs).le |> inv_nonneg.mpr
  have he := birthLargePhase_energy_scale (q := q) ht hs.le
  have hv := birthLargePhase_momentum_scale (q := q) ht hs.le
  have he' : ((birthTrafficCoarseScale q t s)⁻¹ * (A * s) * (C * Real.sqrt s)) * (t ^ 2)⁻¹ =
      (A * C) * (s ^ 2 * t ^ (-2 + 1 / (q : ℝ))) := by
    calc
      _ = (A * C) * ((birthTrafficCoarseScale q t s)⁻¹ * s * Real.sqrt s * (t ^ 2)⁻¹) := by ring
      _ = _ := by rw [he]
  have hv' : ((birthTrafficCoarseScale q t s)⁻¹ * (A * s) * (C * Real.sqrt s)) * t⁻¹ =
      (A * C) * (s ^ 2 * t ^ (-1 + 1 / (q : ℝ))) := by
    calc
      _ = (A * C) * ((birthTrafficCoarseScale q t s)⁻¹ * s * Real.sqrt s * t⁻¹) := by ring
      _ = _ := by rw [hv]
  calc
    _ ≤ ENNReal.ofReal ((birthTrafficCoarseScale q t s)⁻¹) *
        (ENNReal.ofReal (A * s) * ENNReal.ofReal (C * Real.sqrt s) *
          (ENNReal.ofReal ((t ^ 2)⁻¹) * E + ENNReal.ofReal t⁻¹ * V)) := by
      exact mul_le_mul_right (hH.trans (by gcongr)) _
    _ = _ := by
      simp only [mul_add, ← mul_assoc]
      rw [← ENNReal.ofReal_mul hL,
        ← ENNReal.ofReal_mul (mul_nonneg hL (mul_nonneg hA hs.le)),
        ← ENNReal.ofReal_mul (by positivity),
        ← ENNReal.ofReal_mul (show 0 ≤ (birthTrafficCoarseScale q t s)⁻¹ * (A * s) * (C * Real.sqrt s) by positivity),
        he', hv']
      rw [ENNReal.ofReal_mul (mul_nonneg hA hC), ENNReal.ofReal_mul (mul_nonneg hA hC)]

end OTSelector.Reconstruction
