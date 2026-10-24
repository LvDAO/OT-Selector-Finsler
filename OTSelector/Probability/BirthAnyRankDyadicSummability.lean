import OTSelector.Probability.RankZeroBirthTrafficInterpolation

/-! The original birth-level double series sums at every actual residue rank,
using the regular momentum-only branch at rank zero. -/
open Real
noncomputable section
namespace OTSelector.Probability

/-- The actual birth-level norm majorant is double-dyadically summable for every
natural residue rank; positive rank is not a new geometric assumption. -/
theorem exists_summable_original_birth_levels_any_rank
    {K₀ E t q c : ℝ} (hK₀ : 0 ≤ K₀) (hE : 0 ≤ E) (ht : 0 ≤ t)
    (hq : 0 < q) (hc : 0 < c) (k : ℕ) :
    ∃ C > 0, Summable (fun z : ℕ × ℕ ↦
      Real.sqrt (interleavedLevelThreshold K₀ C z.1 z.2 * E) *
        ((t / (2 : ℝ) ^ z.1) ^ (1 / (2 * q)) * (1 / (2 : ℝ) ^ z.2) ^ (1 / 2 : ℝ) +
          (t / (2 : ℝ) ^ z.1) ^ (if k = 0 then (3 / 8 : ℝ) else (k : ℝ) / 8) *
            (1 / (2 : ℝ) ^ z.2) ^
              (if k = 0 then (3 / 28 : ℝ) else (k : ℝ) / (4 * (3 * (k : ℝ) + 4)))) +
        (2 : ℝ) ^ z.2 * Real.exp (-c * interleavedLevelThreshold K₀ C z.1 z.2)) := by
  by_cases hk : k = 0
  · simpa [hk] using
      exists_summable_original_rankZero_birth_levels hK₀ hE ht hq hc
  · simpa [hk] using
      exists_summable_original_interleaved_birth_levels hK₀ hE ht hq
        (k := (k : ℝ)) (by exact_mod_cast Nat.pos_of_ne_zero hk) hc

end OTSelector.Probability
