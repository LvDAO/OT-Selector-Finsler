import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Real.Sqrt

/-! The physical birth source volume, actual one-edge coefficient and same-band
canonical quadratic moment give the exact second small-phase dyadic powers. -/
noncomputable section
namespace OTSelector.Probability

/-- The genuine raw confined-traffic square has the required two energy powers;
all rank dependence comes from the actual Haar source-window factor. -/
theorem birthConfined_quadratic_power_bound
    {q k : ℕ} {t s C Cv K w z e v : ℝ}
    (ht : 0 < t) (hs : 0 < s) (hCv : 0 ≤ Cv) (hK : 0 ≤ K)
    (_hw0 : 0 ≤ w) (hz0 : 0 ≤ z) (he : 0 ≤ e) (hv : 0 ≤ v)
    (hw : w ≤ Cv * (t ^ (k + 1))⁻¹)
    (hz : z ≤ (s * (q : ℝ)) * v + (2 * s / t) * e) :
    K * (C * Real.sqrt s / t) ^ 2 * w * z ≤
      (K * C ^ 2 * Cv * ((q : ℝ) + 2)) * s ^ 2 *
        (t ^ (-(k : ℝ) - 4) * e + t ^ (-(k : ℝ) - 3) * v) := by
  have hp (n : ℕ) : t ^ (-(n : ℝ)) = (t ^ n)⁻¹ := by
    rw [Real.rpow_neg ht.le, Real.rpow_natCast]
  have hp3 : t ^ (-(k : ℝ) - 3) = (t ^ (k + 3))⁻¹ := by
    convert hp (k + 3) using 2; push_cast; ring
  have hp4 : t ^ (-(k : ℝ) - 4) = (t ^ (k + 4))⁻¹ := by
    convert hp (k + 4) using 2; push_cast; ring
  have h0 : 0 ≤ K * C ^ 2 * Cv * s ^ 2 := by positivity
  have hq : 0 ≤ (q : ℝ) := Nat.cast_nonneg q
  calc
    _ ≤ K * (C * Real.sqrt s / t) ^ 2 * (Cv * (t ^ (k + 1))⁻¹) * z := by
      gcongr
    _ ≤ K * (C * Real.sqrt s / t) ^ 2 * (Cv * (t ^ (k + 1))⁻¹) *
        ((s * (q : ℝ)) * v + (2 * s / t) * e) := by gcongr
    _ = (K * C ^ 2 * Cv * s ^ 2) *
        (2 * (t ^ (k + 4))⁻¹ * e + (q : ℝ) * (t ^ (k + 3))⁻¹ * v) := by
      rw [div_pow, mul_pow, Real.sq_sqrt hs.le]
      simp only [pow_add]
      field_simp
      ring
    _ ≤ (K * C ^ 2 * Cv * s ^ 2) * (((q : ℝ) + 2) *
        ((t ^ (k + 4))⁻¹ * e + (t ^ (k + 3))⁻¹ * v)) := by
      apply mul_le_mul_of_nonneg_left _ h0
      have hE : 0 ≤ (t ^ (k + 4))⁻¹ * e := by positivity
      have hV : 0 ≤ (t ^ (k + 3))⁻¹ * v := by positivity
      nlinarith
    _ = _ := by rw [hp3, hp4]; ring

end OTSelector.Probability
