import OTSelector.MeasureTheory.Lp.FiniteBandEnergySum
import OTSelector.Probability.RankZeroBirthTrafficInterpolation

/-! The actual rank-zero first-moment band estimate retains a positive endpoint
time decay after finite-band Minkowski; it is not weakened to the constant t^0. -/
open Set MeasureTheory
open scoped ENNReal BigOperators
noncomputable section
namespace OTSelector.Probability

/-- The true number of original width-s birth bands cancels the elapsed-time
power and leaves the sharper positive `t^(3/4)` rank-zero coefficient. -/
theorem rankZero_birthBand_first_norm_scale
    {N : ℕ} {t s C : ℝ} (ht : 0 < t) (hs : 0 < s) (hC : 0 ≤ C)
    (hNs : (N : ℝ) * s = 8 * t) :
    (N : ℝ) ^ (3 / 4 : ℝ) * Real.sqrt (C * s ^ (3 / 2 : ℝ)) =
      (8 : ℝ) ^ (3 / 4 : ℝ) * Real.sqrt C * t ^ (3 / 4 : ℝ) := by
  have hsqrt : Real.sqrt (s ^ (3 / 2 : ℝ)) = s ^ (3 / 4 : ℝ) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hs.le]
    norm_num
  rw [Real.sqrt_mul hC, hsqrt]
  calc
    _ = Real.sqrt C * ((N : ℝ) ^ (3 / 4 : ℝ) * s ^ (3 / 4 : ℝ)) := by ring
    _ = Real.sqrt C * ((N : ℝ) * s) ^ (3 / 4 : ℝ) := by
      rw [Real.mul_rpow (Nat.cast_nonneg _) hs.le]
    _ = _ := by rw [hNs, Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 8) ht.le]; ring

/-- The same original bounded-phase contribution has a summable positive
rank-zero endpoint-scale bound after summing its own finite mark bands. -/
theorem rankZero_birthBand_traffic_memLp_two_of_first_moment
    {Ω ι : Type*} [MeasurableSpace Ω] (P : Measure Ω) (bands : Finset ι)
    (T : ι → Ω → ℝ) (hT : ∀ i ∈ bands, MemLp (T i) 2 P)
    (v : ι → ℝ) (hv : ∀ i, 0 ≤ v i) {V t s C : ℝ}
    (ht : 0 < t) (hs : 0 < s) (hC : 0 ≤ C)
    (hNs : (bands.card : ℝ) * s = 8 * t)
    (hV : (∑ i ∈ bands, v i) ≤ V)
    (hmean : ∀ i ∈ bands, (∫ x, T i x ^ 2 ∂P) ≤
      (C * s ^ (3 / 2 : ℝ)) * Real.sqrt (v i)) :
    MemLp (fun x ↦ ∑ i ∈ bands, T i x) 2 P ∧
      eLpNorm (fun x ↦ ∑ i ∈ bands, T i x) 2 P ≤
        ENNReal.ofReal ((8 : ℝ) ^ (3 / 4 : ℝ) * Real.sqrt C *
          V ^ (1 / 4 : ℝ) * t ^ (3 / 4 : ℝ)) := by
  have h := finiteBand_traffic_memLp_two_of_sqrt_energy_budget P bands T hT
    (fun _ ↦ 0) v (fun _ ↦ le_rfl) hv (cE := 0) (cV := C * s ^ (3 / 2 : ℝ))
    (E := 0) (by norm_num) (mul_nonneg hC (Real.rpow_nonneg hs.le _))
    (by simp) hV (by simpa only [zero_mul, zero_add] using hmean)
  refine ⟨h.1, h.2.trans ?_⟩
  apply ENNReal.ofReal_le_ofReal
  simp only [Real.sqrt_zero, zero_mul, zero_add]
  have heq := rankZero_birthBand_first_norm_scale ht hs hC hNs
  calc
    _ = ((bands.card : ℝ) ^ (3 / 4 : ℝ) * Real.sqrt (C * s ^ (3 / 2 : ℝ))) *
        V ^ (1 / 4 : ℝ) := by ring
    _ = (8 : ℝ) ^ (3 / 4 : ℝ) * Real.sqrt C * V ^ (1 / 4 : ℝ) *
        t ^ (3 / 4 : ℝ) := by rw [heq]; ring
    _ ≤ _ := le_rfl

end OTSelector.Probability
