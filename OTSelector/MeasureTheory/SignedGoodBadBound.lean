import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
## Lemma skeleton

* **Conditions:** Almost-everywhere signed bounds for value and core, nonnegative repair, and a good-event value inequality under an arbitrary measure.
* **Objects:** A global almost-everywhere good/bad inequality with penalty (A+L) times the bad indicator of count.
* **Proof detail:** Intersect the four almost-everywhere sets; split on the bad event and use the value upper bound plus the lower bound for core in its bad branch.

## Mathematical sources

* Terence Tao, *Analysis I*, Sections 4.3 (absolute value) and 7.1 (finite series), in particular Proposition 7.1.11.
  https://github.com/teorth/analysis/blob/main/Analysis/Section_7_1.lean

**Relationship to the sources:** Pointwise signed algebra and null-set intersection. Despite the original application filename, this statement contains no integration or expectation assertion.
-/

/-! A signed retained core pays only its negative probe part when removing a bad event. -/
open Set MeasureTheory
namespace OTSelector.Reconstruction

/-- A genuine good-event comparison and the coarse absolute value bound imply
one unmasked cost bound. Only the core's negative part is charged on bad events;
no nonnegative or quadratic bound is imposed on the signed core itself. -/
theorem screeningValue_ae_le_unmaskedCost_of_good
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (value core repair count : Ω → ℝ) (bad : Set Ω) (A L : ℝ)
    (hvalue : ∀ᵐ ω ∂P, |value ω| ≤ count ω*A)
    (hcore : ∀ᵐ ω ∂P, -(L*count ω) ≤ core ω)
    (hrepair : ∀ᵐ ω ∂P, 0 ≤ repair ω)
    (hgood : ∀ᵐ ω ∂P, ω ∉ bad → value ω ≤ core ω+repair ω) :
    ∀ᵐ ω ∂P, value ω ≤ core ω+repair ω+(A+L)*bad.indicator count ω := by
  filter_upwards [hvalue,hcore,hrepair,hgood] with ω hv hc hr hg
  by_cases hb : ω ∈ bad
  · rw [indicator_of_mem hb]
    have hv' := (le_abs_self (value ω)).trans hv
    nlinarith
  · rw [indicator_of_notMem hb,mul_zero,add_zero]
    exact hg hb

end OTSelector.Reconstruction
