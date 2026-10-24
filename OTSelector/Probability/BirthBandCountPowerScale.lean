import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! Exact physical coefficients after summing the literal `N s = 8 t` original
birth bands. No constant depending on either dyadic index is introduced. -/
noncomputable section
namespace OTSelector.Probability

/-- Square roots preserve the exact original real power at positive time. -/
theorem sqrt_positive_time_rpow {t : ℝ} (ht : 0 < t) (r : ℝ) :
    Real.sqrt (t ^ r) = t ^ (r / 2) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_mul ht.le]
  congr 1
  ring

/-- The actual number of birth bands converts the square-root count into its
physical endpoint/elapsed ratio. -/
theorem birthBand_sqrt_count_mul_width {N : ℕ} {t s : ℝ}
    (ht : 0 < t) (hs : 0 < s) (hNs : (N : ℝ) * s = 8 * t) :
    Real.sqrt (N : ℝ) * s = Real.sqrt 8 * t * Real.sqrt (s / t) := by
  calc
    _ = Real.sqrt ((N : ℝ) * s) * Real.sqrt s := by
      rw [Real.sqrt_mul (Nat.cast_nonneg _), mul_assoc, Real.mul_self_sqrt hs.le]
    _ = Real.sqrt (8 * t) * Real.sqrt s := by rw [hNs]
    _ = Real.sqrt 8 * Real.sqrt t * Real.sqrt s := by rw [Real.sqrt_mul (by norm_num)]
    _ = Real.sqrt 8 * (Real.sqrt t) ^ 2 * (Real.sqrt s / Real.sqrt t) := by
      field_simp
    _ = _ := by rw [Real.sq_sqrt ht.le, Real.sqrt_div hs.le]

/-- Each actual quadratic per-band mean-square coefficient yields the exact
square-root-count birth-level power. -/
theorem birthBand_sqrt_quadratic_coefficient {N : ℕ} {t s C : ℝ}
    (ht : 0 < t) (hs : 0 < s) (hC : 0 ≤ C) (hNs : (N : ℝ) * s = 8 * t)
    (r : ℝ) :
    Real.sqrt (N : ℝ) * Real.sqrt (C * s ^ 2 * t ^ r) =
      Real.sqrt 8 * Real.sqrt C * t ^ (r / 2 + 1) * Real.sqrt (s / t) := by
  have hroot : Real.sqrt (C * s ^ 2 * t ^ r) = Real.sqrt C * s * t ^ (r / 2) := by
    rw [Real.sqrt_mul (mul_nonneg hC (sq_nonneg s)), Real.sqrt_mul hC,
      Real.sqrt_sq_eq_abs, abs_of_pos hs, sqrt_positive_time_rpow ht]
  have htime : t * t ^ (r / 2) = t ^ (r / 2 + 1) := by
    calc
      _ = t ^ (1 : ℝ) * t ^ (r / 2) := by rw [Real.rpow_one]
      _ = t ^ (1 + r / 2) := (Real.rpow_add ht _ _).symm
      _ = _ := by congr 1; ring
  calc
    _ = Real.sqrt C * (Real.sqrt (N : ℝ) * s) * t ^ (r / 2) := by rw [hroot]; ring
    _ = Real.sqrt C * (Real.sqrt 8 * t * Real.sqrt (s / t)) * t ^ (r / 2) := by
      rw [birthBand_sqrt_count_mul_width ht hs hNs]
    _ = Real.sqrt 8 * Real.sqrt C * (t * t ^ (r / 2)) * Real.sqrt (s / t) := by ring
    _ = _ := by rw [htime]

/-- Each square-root energy per-band estimate retains the exact positive
endpoint decay after the actual `N^(3/4)` finite-band Holder factor. -/
theorem birthBand_fourthRoot_coefficient {N : ℕ} {t s C : ℝ}
    (ht : 0 < t) (hs : 0 < s) (hC : 0 ≤ C) (hNs : (N : ℝ) * s = 8 * t)
    (r : ℝ) :
    (N : ℝ) ^ (3 / 4 : ℝ) * Real.sqrt (C * s ^ (3 / 2 : ℝ) * t ^ r) =
      (8 : ℝ) ^ (3 / 4 : ℝ) * Real.sqrt C * t ^ (3 / 4 + r / 2) := by
  have hroot : Real.sqrt (C * s ^ (3 / 2 : ℝ) * t ^ r) =
      Real.sqrt C * s ^ (3 / 4 : ℝ) * t ^ (r / 2) := by
    rw [Real.sqrt_mul (mul_nonneg hC (Real.rpow_nonneg hs.le _)), Real.sqrt_mul hC,
      sqrt_positive_time_rpow hs, sqrt_positive_time_rpow ht]
    norm_num
  calc
    _ = Real.sqrt C * ((N : ℝ) ^ (3 / 4 : ℝ) * s ^ (3 / 4 : ℝ)) * t ^ (r / 2) := by
      rw [hroot]; ring
    _ = Real.sqrt C * ((N : ℝ) * s) ^ (3 / 4 : ℝ) * t ^ (r / 2) := by
      rw [Real.mul_rpow (Nat.cast_nonneg _) hs.le]
    _ = Real.sqrt C * ((8 : ℝ) ^ (3 / 4 : ℝ) * t ^ (3 / 4 : ℝ)) * t ^ (r / 2) := by
      rw [hNs, Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 8) ht.le]
    _ = (8 : ℝ) ^ (3 / 4 : ℝ) * Real.sqrt C *
        (t ^ (3 / 4 : ℝ) * t ^ (r / 2)) := by ring
    _ = _ := by rw [← Real.rpow_add ht]

end OTSelector.Probability
