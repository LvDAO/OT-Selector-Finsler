import Mathlib.MeasureTheory.Function.L2Space

/-!
## Lemma skeleton

* **Conditions:** Measurable extended nonnegative T, measurable bad event A, and a finite lower-integral bound R for T squared on A-complement.
* **Objects:** The actual real-valued good-event readout is in L2 and its squared integral is at most R.toReal.
* **Proof detail:** The finite moment forces T to be finite almost everywhere on the good event; convert its ENNReal square integral to the real representative and the MemLp criterion.

## Mathematical sources

* Sheldon Axler, *Measure, Integration & Real Analysis (author PDF, 12 June 2026)*, Section 7A, Theorem 7.9, pp. 196–197 (Hölder); Theorem 7.10, p. 197 (finite-measure Lq to Lp).
  https://measure.axler.net/MIRA.pdf#page=211
* Sheldon Axler, *Measure, Integration & Real Analysis (author PDF, 12 June 2026)*, Section 8A, Theorem 8.11, p. 218; Example 8.14, p. 219 (L2 Cauchy–Schwarz).
  https://measure.axler.net/MIRA.pdf#page=233

**Relationship to the sources:** Finite-moment-to-L2 adapter; the toReal conversion is justified on the contributing event.
-/

/-! A finite actual nonnegative mean-square bound gives the literal real-valued
good-event traffic L2 and mean-square bound, with no prior integrability premise. -/
open Set MeasureTheory
open scoped ENNReal
noncomputable section
namespace OTSelector.Probability

/-- The real-valued good-event readout inherits its L2 bound from the same
nonnegative square integral, including all extended-real edge cases. -/
theorem memLp_two_of_goodEvent_lintegral_sq_le
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    {T : Ω → ℝ≥0∞} (hT : Measurable T) {A : Set Ω} (hA : MeasurableSet A)
    {R : ℝ≥0∞} (hR : R ≠ ∞)
    (hbound : (∫⁻ s, Aᶜ.indicator (fun z ↦ T z ^ (2 : ℕ)) s ∂P) ≤ R) :
    MemLp (Aᶜ.indicator (fun s ↦ (T s).toReal)) 2 P ∧
      (∫ s, (Aᶜ.indicator (fun z ↦ (T z).toReal) s) ^ 2 ∂P) ≤ R.toReal := by
  let U : Ω → ℝ≥0∞ := Aᶜ.indicator (fun z ↦ T z ^ (2 : ℕ))
  have hU : Measurable U := (hT.pow_const (2 : ℕ)).indicator hA.compl
  have hfin : (∫⁻ s, U s ∂P) ≠ ∞ := ne_top_of_le_ne_top hR hbound
  have hi := integrable_toReal_of_lintegral_ne_top hU.aemeasurable hfin
  have heq (s : Ω) : (Aᶜ.indicator (fun z ↦ (T z).toReal) s) ^ 2 = (U s).toReal := by
    by_cases hs : s ∈ Aᶜ
    · simp only [U, indicator_of_mem hs, ENNReal.toReal_pow]
    · simp only [U, indicator_of_notMem hs, zero_pow (by norm_num : (2 : ℕ) ≠ 0),
        ENNReal.toReal_zero]
  have hiSq : Integrable (fun s ↦ (Aᶜ.indicator (fun z ↦ (T z).toReal) s) ^ 2) P := by
    simpa only [heq] using hi
  refine ⟨(memLp_two_iff_integrable_sq
    (hT.ennreal_toReal.aestronglyMeasurable.indicator hA.compl)).mpr hiSq, ?_⟩
  calc
    _ = ∫ s, (U s).toReal ∂P := integral_congr_ae (Filter.Eventually.of_forall heq)
    _ = (∫⁻ s, U s ∂P).toReal := integral_toReal hU.aemeasurable (ae_lt_top hU hfin)
    _ ≤ _ := ENNReal.toReal_mono hR hbound

end OTSelector.Probability
