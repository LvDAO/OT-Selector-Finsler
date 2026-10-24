import Mathlib.MeasureTheory.Integral.MeanInequalities

/-!
## Lemma skeleton

* **Conditions:** A measurable extended nonnegative u; the count-weighted form also has a measurable p, restricted mass cutoff and u<=M p on that restriction.
* **Objects:** Square-integral Cauchy–Schwarz and its count-times-momentum-square consequence.
* **Proof detail:** Apply Hölder with 1 and u; restrict the measure and compare u squared with M squared times p squared.

## Mathematical sources

* Sheldon Axler, *Measure, Integration & Real Analysis (author PDF, 12 June 2026)*, Section 7A, Theorem 7.9, pp. 196–197 (Hölder); Theorem 7.10, p. 197 (finite-measure Lq to Lp).
  https://measure.axler.net/MIRA.pdf#page=211

**Relationship to the sources:** Extended nonnegative specialization of the L2 inequality; it does not assume finite first or second moments in advance.
-/

/-! Finite contributor Cauchy-Schwarz retains the original quadratic mark
moment. Extended nonnegative integrals keep all zero and infinite cases valid. -/
open Set MeasureTheory
open scoped ENNReal
noncomputable section
namespace OTSelector.Probability

/-- Cauchy-Schwarz over the same original contributor measure, without any
independence or finiteness assumption on its weighted second moment. -/
theorem lintegral_sq_le_measure_mul_lintegral_sq
    {X : Type*} [MeasurableSpace X] (μ : Measure X)
    {u : X → ℝ≥0∞} (hu : Measurable u) :
    (∫⁻ x, u x ∂μ) ^ 2 ≤ μ univ * ∫⁻ x, u x ^ 2 ∂μ := by
  have hp (z : ℝ≥0∞) : (z ^ (2 : ℕ)) ^ (1 / 2 : ℝ) = z := by
    rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
    norm_num
  have hr (z : ℝ≥0∞) : (z ^ (1 / 2 : ℝ)) ^ (2 : ℕ) = z := by
    rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
    norm_num
  have hh := ENNReal.lintegral_mul_norm_pow_le
    (μ := μ) (hu.pow_const (2 : ℕ)).aemeasurable
    (measurable_const.aemeasurable : AEMeasurable (fun _ : X ↦ (1 : ℝ≥0∞)) μ)
    (p := (1 / 2 : ℝ)) (q := (1 / 2 : ℝ)) (by norm_num) (by norm_num) (by norm_num)
  simp only [hp, ENNReal.one_rpow, mul_one, lintegral_one] at hh
  calc
    _ ≤ ((∫⁻ x, u x ^ 2 ∂μ) ^ (1 / 2 : ℝ) * (μ univ) ^ (1 / 2 : ℝ)) ^ 2 := by
      gcongr
    _ = _ := by rw [mul_pow, hr, hr]; exact mul_comm _ _

/-- A finite same-scene count and the actual pointwise normalized momentum
bound give the quadratic contributor estimate used for bounded-phase traffic. -/
theorem setLIntegral_sq_le_count_mul_momentumSquare
    {X : Type*} [MeasurableSpace X] (μ : Measure X) {S : Set X}
    {u p : X → ℝ≥0∞} (hu : Measurable u) (hp : Measurable p)
    {K M : ℝ≥0∞} (hcount : μ S ≤ K)
    (hpoint : ∀ᵐ x ∂μ.restrict S, u x ≤ M * p x) :
    (∫⁻ x in S, u x ∂μ) ^ 2 ≤ K * M ^ 2 * ∫⁻ x in S, p x ^ 2 ∂μ := by
  have he : (∫⁻ x in S, u x ^ 2 ∂μ) ≤ M ^ 2 * ∫⁻ x in S, p x ^ 2 ∂μ := by
    rw [← lintegral_const_mul (M ^ 2) (hp.pow_const (2 : ℕ))]
    apply lintegral_mono_ae
    filter_upwards [hpoint] with x hx
    calc
      _ ≤ (M * p x) ^ 2 := by gcongr
      _ = _ := mul_pow _ _ _
  have h := lintegral_sq_le_measure_mul_lintegral_sq (μ.restrict S) hu
  rw [Measure.restrict_apply_univ] at h
  calc
    _ ≤ _ := h
    _ ≤ K * (M ^ 2 * ∫⁻ x in S, p x ^ 2 ∂μ) := by gcongr
    _ = _ := by rw [mul_assoc]

end OTSelector.Probability
