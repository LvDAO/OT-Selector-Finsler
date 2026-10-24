import OTSelector.Probability.BirthAnyRankDyadicSummability

/-! The actual physical constants, finite clock-cover size and original count
exponential-moment prefactor preserve the same full dyadic summability. -/
noncomputable section
namespace OTSelector.Probability

/-- Actual fixed geometric and count-tail constants can be retained in the
complete original birth-level profile, at every residue rank including zero. -/
theorem exists_summable_original_birth_profile_with_constants
    {K₀ E t q c A B : ℝ} (hK₀ : 0 ≤ K₀) (hE : 0 ≤ E) (ht : 0 ≤ t)
    (hq : 0 < q) (hc : 0 < c) (hA : 0 ≤ A) (hB : 0 ≤ B) (k : ℕ) :
    ∃ C > 0, Summable (fun z : ℕ × ℕ ↦
      A * (Real.sqrt (interleavedLevelThreshold K₀ C z.1 z.2 * E) *
        ((t / (2 : ℝ) ^ z.1) ^ (1 / (2 * q)) * (1 / (2 : ℝ) ^ z.2) ^ (1 / 2 : ℝ) +
          (t / (2 : ℝ) ^ z.1) ^ (if k = 0 then (3 / 8 : ℝ) else (k : ℝ) / 8) *
            (1 / (2 : ℝ) ^ z.2) ^
              (if k = 0 then (3 / 28 : ℝ) else (k : ℝ) / (4 * (3 * (k : ℝ) + 4))))) +
      B * ((2 : ℝ) ^ z.2 * Real.exp (-c * interleavedLevelThreshold K₀ C z.1 z.2))) := by
  obtain ⟨C, hC, hs⟩ := exists_summable_original_birth_levels_any_rank hK₀ hE ht hq hc k
  refine ⟨C, hC, ?_⟩
  apply (hs.mul_left (max A B)).of_nonneg_of_le (fun z ↦ by positivity)
  intro z
  have hx : 0 ≤ Real.sqrt (interleavedLevelThreshold K₀ C z.1 z.2 * E) *
      ((t / (2 : ℝ) ^ z.1) ^ (1 / (2 * q)) * (1 / (2 : ℝ) ^ z.2) ^ (1 / 2 : ℝ) +
        (t / (2 : ℝ) ^ z.1) ^ (if k = 0 then (3 / 8 : ℝ) else (k : ℝ) / 8) *
          (1 / (2 : ℝ) ^ z.2) ^
            (if k = 0 then (3 / 28 : ℝ) else (k : ℝ) / (4 * (3 * (k : ℝ) + 4)))) := by positivity
  have hy : 0 ≤ (2 : ℝ) ^ z.2 * Real.exp (-c * interleavedLevelThreshold K₀ C z.1 z.2) := by positivity
  have ha := mul_le_mul_of_nonneg_right (le_max_left A B) hx
  have hb := mul_le_mul_of_nonneg_right (le_max_right A B) hy
  nlinarith

end OTSelector.Probability
