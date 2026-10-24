import OTSelector.Analysis.RealPowerInterpolation
import OTSelector.Probability.InterleavedDyadicSummability

/-! Rank-zero birth sums retain their true momentum decay. Discarding it
would incorrectly leave a constant in both dyadic indices. -/
open Real
noncomputable section
namespace OTSelector.Probability

/-- The sharper full-momentum first bound in the zero-residue branch yields
positive decay in both original physical scales, without assuming positive rank. -/
theorem rankZero_smallTraffic_interpolation
    {x A t σ : ℝ} (hA : 0 ≤ A) (ht : 0 < t) (hσ : 0 < σ)
    (hfirst : x ≤ A * t ^ (3 / 4 : ℝ))
    (hsecond : x ≤ A * (t ^ (-1 : ℝ) * σ ^ (1 / 2 : ℝ))) :
    x ≤ A * (t ^ (3 / 8 : ℝ) * σ ^ (3 / 28 : ℝ)) := by
  by_cases hAz : A = 0
  · simpa only [hAz, zero_mul] using hfirst
  have hAp : 0 < A := lt_of_le_of_ne hA (Ne.symm hAz)
  have hx₁ : x / A ≤ t ^ (3 / 4 : ℝ) := by
    apply (div_le_iff₀ hAp).mpr
    simpa only [mul_comm] using hfirst
  have hx₂ : x / A ≤ t ^ (-1 : ℝ) * σ ^ (1 / 2 : ℝ) := by
    apply (div_le_iff₀ hAp).mpr
    simpa only [mul_comm] using hsecond
  have h := le_rpow_interpolation_of_two_bounds
    (Real.rpow_pos_of_pos ht _) (mul_pos (Real.rpow_pos_of_pos ht _)
      (Real.rpow_pos_of_pos hσ _))
    (θ := (3 / 14 : ℝ)) (by norm_num) (by norm_num) hx₁ hx₂
  have he : (t ^ (3 / 4 : ℝ)) ^ (1 - 3 / 14 : ℝ) *
      (t ^ (-1 : ℝ) * σ ^ (1 / 2 : ℝ)) ^ (3 / 14 : ℝ) =
      t ^ (3 / 8 : ℝ) * σ ^ (3 / 28 : ℝ) := by
    rw [Real.mul_rpow (Real.rpow_nonneg ht.le _) (Real.rpow_nonneg hσ.le _),
      ← Real.rpow_mul ht.le, ← Real.rpow_mul ht.le, ← Real.rpow_mul hσ.le,
      ← mul_assoc, ← Real.rpow_add ht]
    norm_num
  rw [he] at h
  simpa only [mul_comm] using (div_le_iff₀ hAp).mp h

/-- The complete rank-zero branch, including all original exceptional bands,
has a summable double dyadic bound with an internally chosen threshold slope. -/
theorem exists_summable_original_rankZero_birth_levels
    {K₀ E t q c : ℝ} (hK₀ : 0 ≤ K₀) (hE : 0 ≤ E) (ht : 0 ≤ t)
    (hq : 0 < q) (hc : 0 < c) :
    ∃ C > 0, Summable (fun z : ℕ × ℕ ↦
      Real.sqrt (interleavedLevelThreshold K₀ C z.1 z.2 * E) *
        ((t / (2 : ℝ) ^ z.1) ^ (1 / (2 * q)) *
            (1 / (2 : ℝ) ^ z.2) ^ (1 / 2 : ℝ) +
          (t / (2 : ℝ) ^ z.1) ^ (3 / 8 : ℝ) *
            (1 / (2 : ℝ) ^ z.2) ^ (3 / 28 : ℝ)) +
        (2 : ℝ) ^ z.2 * Real.exp (-c * interleavedLevelThreshold K₀ C z.1 z.2)) :=
  exists_summable_interleaved_dyadic_birth_bound hK₀ hE ht
    (div_pos (by norm_num) (mul_pos (by norm_num) hq)) (by norm_num) (by norm_num) hc

end OTSelector.Probability
