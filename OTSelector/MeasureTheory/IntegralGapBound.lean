import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Real

/-!
## Lemma skeleton

* **Conditions:** A finite measure, measurable event, integrable almost-everywhere nonnegative real function, and an eventwise lower bound r.
* **Objects:** r times real event mass is bounded by the full integral.
* **Proof detail:** For r>0 integrate r times the event indicator; for r<=0 use nonnegative total integral.

## Mathematical sources

* Rick Durrett, *Probability: Theory and Examples, 5th edition (11 January 2019)*, Section 1.6.1, Theorem 1.6.4 and equation (1.6.1), pp. 29–30.
  https://sites.math.duke.edu/~rtd/PTE/PTE5_011119.pdf#page=37
* Sheldon Axler, *Measure, Integration & Real Analysis (author PDF, 12 June 2026)*, Section 3A, Theorem 3.23, p. 84; Section 3B, Theorem 3.25, p. 88.
  https://measure.axler.net/MIRA.pdf#page=99

**Relationship to the sources:** Indicator/Markov inequality in a form valid also when r is nonpositive.
-/

/-!
# A pointwise gap bounds the measure of its exceptional event

If a nonnegative integrable function is at least `r` on a measurable event, then
`r` times the event's real measure is at most the integral.  The statement is
used for the legal-clock gap: a positive original support distance forces a
positive potential-clock gap whenever the transport slack is small.
-/

open Set MeasureTheory
open scoped ENNReal

noncomputable section
namespace OTSelector.Probability

/-- A pointwise lower bound on a measurable event controls its real measure by
the integral, for nonnegative integrable functions. -/
theorem measureReal_le_integral_of_gap
    {α : Type*} [MeasurableSpace α] (ν : Measure α) [IsFiniteMeasure ν]
    (w : α → ℝ) (E : Set α) (hE : MeasurableSet E)
    {r : ℝ} (hw : Integrable w ν)
    (hw_nonneg : ∀ᵐ e ∂ν, 0 ≤ w e)
    (hgap : ∀ᵐ e ∂ν, e ∈ E → r ≤ w e) :
    r * ν.real E ≤ ∫ e, w e ∂ν := by
  have hind : Integrable (E.indicator (fun _ ↦ (1 : ℝ))) ν :=
    Integrable.indicator (integrable_const (1 : ℝ)) hE
  have hleft : r * ν.real E = ∫ e, r * E.indicator (fun _ ↦ (1 : ℝ)) e ∂ν := by
    rw [integral_const_mul, integral_indicator hE]
    simp [measureReal_def]
  rw [hleft]
  apply integral_mono_ae (hind.const_mul r) hw
  filter_upwards [hw_nonneg, hgap] with e hwne hge
  by_cases he : e ∈ E
  · simpa only [indicator_of_mem he, mul_one] using hge he
  · simpa only [indicator_of_notMem he, mul_zero] using hwne

end OTSelector.Probability
