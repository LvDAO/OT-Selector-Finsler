import OTSelector.Probability.BirthBandPowerTrafficLtwo
import OTSelector.Analysis.RealPowerEnergyBudget

/-! The actual shared birth-band energy estimates yield the precise large and
two small-phase level norms used by the full-path double dyadic series. -/
open Set MeasureTheory
open scoped ENNReal BigOperators
noncomputable section
namespace OTSelector.Probability

/-- The literal birth-band large physical traffic sum has its
precise shared-energy L2 level bound after the actual number of bands is applied. -/
theorem birthBand_large_traffic_level_norm
    {Ω ι : Type*} [MeasurableSpace Ω] (P : Measure Ω) (bands : Finset ι)
    (T : ι → Ω → ℝ) (hT : ∀ i ∈ bands, MemLp (T i) 2 P)
    (e v : ι → ℝ) (he : ∀ i, 0 ≤ e i) (hv : ∀ i, 0 ≤ v i)
    {E t s C q : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) (hs : 0 < s) (hC : 0 ≤ C)
    (hNs : (bands.card : ℝ) * s = 8 * t)
    (hE : (∑ i ∈ bands, e i) ≤ E) (hV : (∑ i ∈ bands, v i) ≤ E)
    (hmean : ∀ i ∈ bands, (∫ x, T i x ^ 2 ∂P) ≤
      C * s ^ 2 * (t ^ (-2 + 1 / q) * e i + t ^ (-1 + 1 / q) * v i)) :
    MemLp (fun x ↦ ∑ i ∈ bands, T i x) 2 P ∧
      eLpNorm (fun x ↦ ∑ i ∈ bands, T i x) 2 P ≤ ENNReal.ofReal (2 * Real.sqrt 8 * Real.sqrt C * Real.sqrt E * t ^ (1 / (2 * q)) * Real.sqrt (s / t)) := by
  have h := birthBand_traffic_memLp_two_of_quadratic_power_budget P bands T hT e v he hv
    ht hs hC hNs hE hV (-2 + 1 / q) (-1 + 1 / q) hmean
  have hp₁ : (-2 + 1 / q) / 2 + 1 = 1 / (2 * q) := by ring
  have hp₂ : (-1 + 1 / q) / 2 + 1 = (1 / (2 * q)) + 1 / 2 := by ring
  rw [hp₁, hp₂] at h
  refine ⟨h.1, h.2.trans (ENNReal.ofReal_le_ofReal ?_)⟩
  have hb := sqrt_energy_power_pair_le (a := 1 / (2 * q)) (b := (1 / 2 : ℝ))
    ht ht1 (σ := s / t) (by positivity)
    (A := Real.sqrt 8 * Real.sqrt C) (by positivity) (by norm_num) (V := E) le_rfl
  simpa only [mul_assoc] using hb

/-- The literal birth-band small second physical traffic sum has its
precise shared-energy L2 level bound after the actual number of bands is applied. -/
theorem birthBand_small_second_traffic_level_norm
    {Ω ι : Type*} [MeasurableSpace Ω] (P : Measure Ω) (bands : Finset ι)
    (T : ι → Ω → ℝ) (hT : ∀ i ∈ bands, MemLp (T i) 2 P)
    (e v : ι → ℝ) (he : ∀ i, 0 ≤ e i) (hv : ∀ i, 0 ≤ v i)
    {E t s C k : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) (hs : 0 < s) (hC : 0 ≤ C)
    (hNs : (bands.card : ℝ) * s = 8 * t)
    (hE : (∑ i ∈ bands, e i) ≤ E) (hV : (∑ i ∈ bands, v i) ≤ E)
    (hmean : ∀ i ∈ bands, (∫ x, T i x ^ 2 ∂P) ≤
      C * s ^ 2 * (t ^ (-(k + 4)) * e i + t ^ (-(k + 3)) * v i)) :
    MemLp (fun x ↦ ∑ i ∈ bands, T i x) 2 P ∧
      eLpNorm (fun x ↦ ∑ i ∈ bands, T i x) 2 P ≤ ENNReal.ofReal (2 * Real.sqrt 8 * Real.sqrt C * Real.sqrt E * t ^ (-(k + 2) / 2) * Real.sqrt (s / t)) := by
  have h := birthBand_traffic_memLp_two_of_quadratic_power_budget P bands T hT e v he hv
    ht hs hC hNs hE hV (-(k + 4)) (-(k + 3)) hmean
  have hp₁ : (-(k + 4)) / 2 + 1 = -(k + 2) / 2 := by ring
  have hp₂ : (-(k + 3)) / 2 + 1 = (-(k + 2) / 2) + 1 / 2 := by ring
  rw [hp₁, hp₂] at h
  refine ⟨h.1, h.2.trans (ENNReal.ofReal_le_ofReal ?_)⟩
  have hb := sqrt_energy_power_pair_le (a := -(k + 2) / 2) (b := (1 / 2 : ℝ))
    ht ht1 (σ := s / t) (by positivity)
    (A := Real.sqrt 8 * Real.sqrt C) (by positivity) (by norm_num) (V := E) le_rfl
  simpa only [mul_assoc] using hb

/-- The literal birth-band small first physical traffic sum has its
precise shared-energy L2 level bound after the actual number of bands is applied. -/
theorem birthBand_small_first_traffic_level_norm
    {Ω ι : Type*} [MeasurableSpace Ω] (P : Measure Ω) (bands : Finset ι)
    (T : ι → Ω → ℝ) (hT : ∀ i ∈ bands, MemLp (T i) 2 P)
    (e v : ι → ℝ) (he : ∀ i, 0 ≤ e i) (hv : ∀ i, 0 ≤ v i)
    {E t s C k : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) (hs : 0 < s) (hC : 0 ≤ C)
    (hE1 : 1 ≤ E)
    (hNs : (bands.card : ℝ) * s = 8 * t)
    (hE : (∑ i ∈ bands, e i) ≤ E) (hV : (∑ i ∈ bands, v i) ≤ E)
    (hmean : ∀ i ∈ bands, (∫ x, T i x ^ 2 ∂P) ≤
      C * s ^ (3 / 2 : ℝ) * (t ^ ((k - 3) / 2) * Real.sqrt (e i) + t ^ (k / 2) * Real.sqrt (v i))) :
    MemLp (fun x ↦ ∑ i ∈ bands, T i x) 2 P ∧
      eLpNorm (fun x ↦ ∑ i ∈ bands, T i x) 2 P ≤ ENNReal.ofReal (2 * (8 : ℝ) ^ (3 / 4 : ℝ) * Real.sqrt C * Real.sqrt E * t ^ (k / 4)) := by
  have h := birthBand_traffic_memLp_two_of_sqrt_power_budget P bands T hT e v he hv
    ht hs hC hNs hE hV ((k - 3) / 2) (k / 2) hmean
  have hp₁ : (3 / 4 : ℝ) + ((k - 3) / 2) / 2 = k / 4 := by ring
  have hp₂ : (3 / 4 : ℝ) + (k / 2) / 2 = (k / 4) + 3 / 4 := by ring
  rw [hp₁, hp₂] at h
  refine ⟨h.1, h.2.trans (ENNReal.ofReal_le_ofReal ?_)⟩
  have hb := fourthRoot_energy_power_pair_le (a := k / 4) (b := (3 / 4 : ℝ))
    ht ht1 (A := (8 : ℝ) ^ (3 / 4 : ℝ) * Real.sqrt C) (by positivity) (by norm_num)
    (V := E) (by linarith) le_rfl hE1
  simpa only [mul_assoc] using hb

end OTSelector.Probability
