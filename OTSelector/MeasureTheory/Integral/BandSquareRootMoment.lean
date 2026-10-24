import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.MeasureTheory.Integral.MeanInequalities

/-!
## Lemma skeleton

* **Conditions:** A measurable real energy and any measured band; a larger mass cutoff is optional.
* **Objects:** First square-root energy moment bounded by square-root energy times square-root band mass; the ENNReal square-root conversion is included.
* **Proof detail:** Rewrite the clipped real square root as the one-half ENNReal power; use Hölder with the constant-one function on the band, then mass monotonicity.

## Mathematical sources

* Sheldon Axler, *Measure, Integration & Real Analysis (author PDF, 12 June 2026)*, Section 7A, Theorem 7.9, pp. 196–197 (Hölder); Theorem 7.10, p. 197 (finite-measure Lq to Lp).
  https://measure.axler.net/MIRA.pdf#page=211

**Relationship to the sources:** Extended nonnegative Cauchy–Schwarz/Hölder specialization, including negative real energies through ofReal and zero/infinite cases.
-/

/-! Cauchy-Schwarz on the same actual mark band controls first moments by its
own energy and original band mass, with no independence of clock and momentum. -/
open Set MeasureTheory
open scoped ENNReal
noncomputable section
namespace OTSelector.Probability

/-- Clipping the real negative half-line before taking its square root agrees
with the nonnegative square root on the extended nonnegative line. -/
theorem ofReal_sqrt_eq_rpow (x : ℝ) :
    ENNReal.ofReal (Real.sqrt x) = (ENNReal.ofReal x) ^ (1 / 2 : ℝ) := by
  by_cases hx : 0 ≤ x
  · rw [Real.sqrt_eq_rpow, ENNReal.ofReal_rpow_of_nonneg hx (by norm_num)]
  · rw [Real.sqrt_eq_zero_of_nonpos (le_of_not_ge hx), ENNReal.ofReal_zero,
      ENNReal.ofReal_of_nonpos (le_of_not_ge hx), ENNReal.zero_rpow_of_pos (by norm_num)]

/-- A band's square-root energy first moment keeps both its own second moment
and its exact original mass. No moment finiteness assumption is needed for the bound. -/
theorem setLIntegral_sqrt_le_sqrt_energy_mul_sqrt_mass
    {X : Type*} [MeasurableSpace X] (ν : Measure X) (B : Set X)
    {e : X → ℝ} (he : Measurable e) :
    (∫⁻ m in B, ENNReal.ofReal (Real.sqrt (e m)) ∂ν) ≤
      (∫⁻ m in B, ENNReal.ofReal (e m) ∂ν) ^ (1 / 2 : ℝ) * (ν B) ^ (1 / 2 : ℝ) := by
  have h := ENNReal.lintegral_mul_norm_pow_le
    (μ := ν.restrict B) he.ennreal_ofReal.aemeasurable
    (measurable_const.aemeasurable : AEMeasurable (fun _ : X ↦ (1 : ℝ≥0∞)) (ν.restrict B))
    (p := (1 / 2 : ℝ)) (q := (1 / 2 : ℝ)) (by norm_num) (by norm_num) (by norm_num)
  simpa only [← ofReal_sqrt_eq_rpow, ENNReal.one_rpow, mul_one,
    lintegral_one, Measure.restrict_apply_univ] using h

/-- A smaller actual original band-mass bound may be substituted after the
same-band Cauchy-Schwarz step, still retaining the true band energy. -/
theorem setLIntegral_sqrt_le_sqrt_energy_mul_sqrt_mass_bound
    {X : Type*} [MeasurableSpace X] (ν : Measure X) {B : Set X}
    {e : X → ℝ} (he : Measurable e) {m : ℝ≥0∞} (hB : ν B ≤ m) :
    (∫⁻ x in B, ENNReal.ofReal (Real.sqrt (e x)) ∂ν) ≤
      (∫⁻ x in B, ENNReal.ofReal (e x) ∂ν) ^ (1 / 2 : ℝ) * m ^ (1 / 2 : ℝ) := by
  apply (setLIntegral_sqrt_le_sqrt_energy_mul_sqrt_mass ν B he).trans
  exact mul_le_mul_right (ENNReal.rpow_le_rpow hB (by norm_num)) _

end OTSelector.Probability
