import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Analysis.RealPowerInterpolation

Conditions: Nonnegative bounds a,b, x≤a and x≤b, and an interpolation exponent in [0,1].

Objects: The weighted real-power bound, and the stated small-parameter substitution.

Proof detail: Raise each bound to a nonnegative exponent, multiply, and combine x powers; treat zero and endpoint exponents using real-power conventions.

## Mathematical sources

- [Stephen Boyd, Convex Optimization](https://web.stanford.edu/~boyd/cvxbook/bv_cvxbook.pdf#page=85): Section 3.1.5, powers and geometric mean examples, pp. 71–73.

Source relation: Elementary monotonic-power corollary; the application exponent is computed in Lean.
-/

/-! The two actual small-momentum traffic estimates yield positive decay in both
the endpoint-shell scale and the birth-distance scale. -/
open Real
noncomputable section
namespace OTSelector.Probability

/-- Two nonnegative upper bounds interpolate without any probabilistic premise. -/
theorem le_rpow_interpolation_of_two_bounds
    {x a b θ : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) (hxa : x ≤ a) (hxb : x ≤ b) :
    x ≤ a ^ (1 - θ) * b ^ θ := by
  by_cases hx : x ≤ 0
  · exact hx.trans (mul_nonneg (Real.rpow_nonneg ha.le _) (Real.rpow_nonneg hb.le _))
  · have hxpos : 0 < x := lt_of_not_ge hx
    calc
      x = x ^ (1 - θ) * x ^ θ := by
        rw [← Real.rpow_add hxpos, sub_add_cancel, Real.rpow_one]
      _ ≤ _ := mul_le_mul (Real.rpow_le_rpow hxpos.le hxa (sub_nonneg.mpr hθ1))
        (Real.rpow_le_rpow hxpos.le hxb hθ0)
        (Real.rpow_nonneg hxpos.le _) (Real.rpow_nonneg ha.le _)

/-- The actual two small-momentum bounds interpolate to the precise positive
powers used by the original interleaved birth-traffic double series. -/
theorem interleaved_smallTraffic_interpolation
    {x A t σ k : ℝ} (hA : 0 ≤ A) (ht : 0 < t) (hσ : 0 < σ) (hk : 0 < k)
    (hfirst : x ≤ A * t ^ (k / 4))
    (hsecond : x ≤ A * (t ^ (-(k + 2) / 2) * σ ^ (1 / 2 : ℝ))) :
    x ≤ A * (t ^ (k / 8) * σ ^ (k / (4 * (3 * k + 4)))) := by
  by_cases hAzero : A = 0
  · simpa only [hAzero, zero_mul] using hfirst
  have hApos : 0 < A := lt_of_le_of_ne hA (Ne.symm hAzero)
  let θ : ℝ := k / (2 * (3 * k + 4))
  have hd : 0 < 3 * k + 4 := by linarith
  have hθ0 : 0 ≤ θ := by dsimp [θ]; positivity
  have hθ1 : θ ≤ 1 := by
    dsimp [θ]
    apply (div_le_iff₀ (mul_pos (by norm_num) hd)).mpr
    linarith
  have hxfirst : x / A ≤ t ^ (k / 4) := by
    apply (div_le_iff₀ hApos).mpr
    simpa only [mul_comm] using hfirst
  have hxsecond : x / A ≤ t ^ (-(k + 2) / 2) * σ ^ (1 / 2 : ℝ) := by
    apply (div_le_iff₀ hApos).mpr
    simpa only [mul_comm] using hsecond
  have h := le_rpow_interpolation_of_two_bounds
    (Real.rpow_pos_of_pos ht _) (mul_pos (Real.rpow_pos_of_pos ht _)
      (Real.rpow_pos_of_pos hσ _)) hθ0 hθ1 hxfirst hxsecond
  have he : (t ^ (k / 4)) ^ (1 - θ) *
      (t ^ (-(k + 2) / 2) * σ ^ (1 / 2 : ℝ)) ^ θ =
      t ^ (k / 8) * σ ^ (k / (4 * (3 * k + 4))) := by
    rw [Real.mul_rpow (Real.rpow_nonneg ht.le _) (Real.rpow_nonneg hσ.le _),
      ← Real.rpow_mul ht.le, ← Real.rpow_mul ht.le, ← Real.rpow_mul hσ.le,
      ← mul_assoc, ← Real.rpow_add ht]
    have he₁ : k / 4 * (1 - θ) + (-(k + 2) / 2) * θ = k / 8 := by
      dsimp [θ]
      field_simp
      ring
    have he₂ : (1 / 2 : ℝ) * θ = k / (4 * (3 * k + 4)) := by
      dsimp [θ]
      field_simp
      norm_num
    rw [he₁, he₂]
  rw [he] at h
  have hmul := (div_le_iff₀ hApos).mp h
  simpa only [mul_comm] using hmul

end OTSelector.Probability
