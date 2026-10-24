import OTSelector.MeasureTheory.Lp.FiniteBandEnergySum
import OTSelector.Probability.BirthBandCountPowerScale

/-! The literal finite original birth-band traffic sum has its exact physical
level powers after Minkowski and the shared original energy budget. -/
open Set MeasureTheory
open scoped ENNReal BigOperators
noncomputable section
namespace OTSelector.Probability

/-- Actual quadratic per-band mean-square estimates give the precise positive
elapsed-scale gain in the literal birth-level L2 norm. -/
theorem birthBand_traffic_memLp_two_of_quadratic_power_budget
    {Ω ι : Type*} [MeasurableSpace Ω] (P : Measure Ω) (bands : Finset ι)
    (T : ι → Ω → ℝ) (hT : ∀ i ∈ bands, MemLp (T i) 2 P)
    (e v : ι → ℝ) (he : ∀ i, 0 ≤ e i) (hv : ∀ i, 0 ≤ v i)
    {E V t s C : ℝ} (ht : 0 < t) (hs : 0 < s) (hC : 0 ≤ C)
    (hNs : (bands.card : ℝ) * s = 8 * t)
    (hE : (∑ i ∈ bands, e i) ≤ E) (hV : (∑ i ∈ bands, v i) ≤ V)
    (rE rV : ℝ)
    (hmean : ∀ i ∈ bands, (∫ x, T i x ^ 2 ∂P) ≤
      C * s ^ 2 * (t ^ rE * e i + t ^ rV * v i)) :
    MemLp (fun x ↦ ∑ i ∈ bands, T i x) 2 P ∧
      eLpNorm (fun x ↦ ∑ i ∈ bands, T i x) 2 P ≤
        ENNReal.ofReal (Real.sqrt 8 * Real.sqrt C * Real.sqrt (s / t) *
          (t ^ (rE / 2 + 1) * Real.sqrt E + t ^ (rV / 2 + 1) * Real.sqrt V)) := by
  have h := finiteBand_traffic_memLp_two_of_quadratic_energy_budget P bands T hT e v he hv
    (cE := C * s ^ 2 * t ^ rE) (cV := C * s ^ 2 * t ^ rV)
    (by positivity) (by positivity) hE hV
    (by intro i hi; simpa only [mul_add, mul_assoc] using hmean i hi)
  refine ⟨h.1, h.2.trans ?_⟩
  apply ENNReal.ofReal_le_ofReal
  apply le_of_eq
  have hE' := birthBand_sqrt_quadratic_coefficient ht hs hC hNs rE
  have hV' := birthBand_sqrt_quadratic_coefficient ht hs hC hNs rV
  calc
    _ = (Real.sqrt (bands.card : ℝ) * Real.sqrt (C * s ^ 2 * t ^ rE)) * Real.sqrt E +
        (Real.sqrt (bands.card : ℝ) * Real.sqrt (C * s ^ 2 * t ^ rV)) * Real.sqrt V := by ring
    _ = _ := by rw [hE', hV']; ring

/-- Actual square-root energy per-band means keep the two physical endpoint
powers separately, including the sharper full-momentum decay at rank zero. -/
theorem birthBand_traffic_memLp_two_of_sqrt_power_budget
    {Ω ι : Type*} [MeasurableSpace Ω] (P : Measure Ω) (bands : Finset ι)
    (T : ι → Ω → ℝ) (hT : ∀ i ∈ bands, MemLp (T i) 2 P)
    (e v : ι → ℝ) (he : ∀ i, 0 ≤ e i) (hv : ∀ i, 0 ≤ v i)
    {E V t s C : ℝ} (ht : 0 < t) (hs : 0 < s) (hC : 0 ≤ C)
    (hNs : (bands.card : ℝ) * s = 8 * t)
    (hE : (∑ i ∈ bands, e i) ≤ E) (hV : (∑ i ∈ bands, v i) ≤ V)
    (rE rV : ℝ)
    (hmean : ∀ i ∈ bands, (∫ x, T i x ^ 2 ∂P) ≤
      C * s ^ (3 / 2 : ℝ) * (t ^ rE * Real.sqrt (e i) + t ^ rV * Real.sqrt (v i))) :
    MemLp (fun x ↦ ∑ i ∈ bands, T i x) 2 P ∧
      eLpNorm (fun x ↦ ∑ i ∈ bands, T i x) 2 P ≤
        ENNReal.ofReal ((8 : ℝ) ^ (3 / 4 : ℝ) * Real.sqrt C *
          (t ^ (3 / 4 + rE / 2) * E ^ (1 / 4 : ℝ) +
            t ^ (3 / 4 + rV / 2) * V ^ (1 / 4 : ℝ))) := by
  have h := finiteBand_traffic_memLp_two_of_sqrt_energy_budget P bands T hT e v he hv
    (cE := C * s ^ (3 / 2 : ℝ) * t ^ rE) (cV := C * s ^ (3 / 2 : ℝ) * t ^ rV)
    (mul_nonneg (mul_nonneg hC (Real.rpow_nonneg hs.le _)) (Real.rpow_nonneg ht.le _))
    (mul_nonneg (mul_nonneg hC (Real.rpow_nonneg hs.le _)) (Real.rpow_nonneg ht.le _)) hE hV
    (by intro i hi; simpa only [mul_add, mul_assoc] using hmean i hi)
  refine ⟨h.1, h.2.trans ?_⟩
  apply ENNReal.ofReal_le_ofReal
  apply le_of_eq
  have hE' := birthBand_fourthRoot_coefficient ht hs hC hNs rE
  have hV' := birthBand_fourthRoot_coefficient ht hs hC hNs rV
  calc
    _ = ((bands.card : ℝ) ^ (3 / 4 : ℝ) * Real.sqrt (C * s ^ (3 / 2 : ℝ) * t ^ rE)) *
        E ^ (1 / 4 : ℝ) +
        ((bands.card : ℝ) ^ (3 / 4 : ℝ) * Real.sqrt (C * s ^ (3 / 2 : ℝ) * t ^ rV)) *
        V ^ (1 / 4 : ℝ) := by ring
    _ = _ := by rw [hE', hV']; ring

end OTSelector.Probability
