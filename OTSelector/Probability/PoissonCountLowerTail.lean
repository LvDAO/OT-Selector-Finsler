import OTSelector.Probability.PoissonCountDeviationTransfer

/-!
Conditions: A measurable Poisson count under the original probability law, positive deviation threshold and, for the lower-half event, strictly positive rate.

Objects: Quantitative deviation and lower-half-count probability bounds in terms of sqrt(a) divided by the deviation threshold.

Proof detail: Apply Markov to the true absolute centered deviation and include the lower-half-count event in the corresponding positive-deviation event.

References: Gunter Last; Mathew Penrose: Section 1.1, equations (1.8)–(1.10), p. 2; Rick Durrett: Section 1.6.1, Theorem 1.6.4 and equation (1.6.1), pp. 29–30.
Relation: A direct capacity-event consequence of the actual Poisson law. It introduces no independence premise or concentration statement for an adaptively selected unrelated count.
-/

/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Reconstruction.OriginalReservePoissonCountLowerTail.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Reconstruction.OriginalReservePoissonCountLowerTail`; the selected original proof blocks follow. -/
section

/-! Actual Poisson laws produce quantitative lower-count capacity events. -/
open Set MeasureTheory ProbabilityTheory
open scoped NNReal
noncomputable section
namespace OTSelector.Reconstruction

/-- The true count-deviation event has its Markov bound on the same probability
space; no independence from any other exceptional event is used. -/
theorem poissonCount_deviation_probability_of_hasLaw {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (f : Ω → ℕ) (hf : Measurable f) (a : ℝ≥0)
    (hlaw : HasLaw f (poissonMeasure a) P) {δ : ℝ} (hδ : 0 < δ) :
    P.real {p | δ < |(f p : ℝ) - (a : ℝ)|} ≤ Real.sqrt (a : ℝ) / δ := by
  have hd := poissonCount_deviation_of_hasLaw P f hf a hlaw
  have hmark := mul_meas_ge_le_integral_of_nonneg
    (Filter.Eventually.of_forall fun p ↦ abs_nonneg ((f p : ℝ) - (a : ℝ))) hd.1 δ
  have hm : P.real {p | δ < |(f p : ℝ) - (a : ℝ)|} ≤
      P.real {p | δ ≤ |(f p : ℝ) - (a : ℝ)|} := measureReal_mono (by
        intro p hp
        exact (show δ < |(f p : ℝ) - (a : ℝ)| from hp).le)
  calc
    _ ≤ P.real {p | δ ≤ |(f p : ℝ) - (a : ℝ)|} := hm
    _ ≤ (∫ p, |(f p : ℝ) - (a : ℝ)| ∂P) / δ := by
      apply (le_div_iff₀ hδ).mpr
      simpa only [mul_comm] using hmark
    _ ≤ _ := div_le_div_of_nonneg_right hd.2 hδ.le

/-- A positive genuine Poisson mean produces its actual half-mean reserve
capacity event; null classes are handled separately by their true zero law. -/
theorem poissonCount_lower_probability_of_hasLaw {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (f : Ω → ℕ) (hf : Measurable f) (a : ℝ≥0)
    (hlaw : HasLaw f (poissonMeasure a) P) (ha : 0 < (a : ℝ)) :
    P.real {p | (f p : ℝ) < (a : ℝ) / 2} ≤ Real.sqrt (a : ℝ) / ((a : ℝ) / 2) := by
  have hsub : {p | (f p : ℝ) < (a : ℝ) / 2} ⊆
      {p | (a : ℝ) / 2 < |(f p : ℝ) - (a : ℝ)|} := by
    intro p hp
    have h := neg_le_abs ((f p : ℝ) - (a : ℝ))
    change (f p : ℝ) < (a : ℝ) / 2 at hp
    change (a : ℝ) / 2 < |(f p : ℝ) - (a : ℝ)|
    linarith
  exact (measureReal_mono hsub).trans
    (poissonCount_deviation_probability_of_hasLaw P f hf a hlaw (half_pos ha))

end OTSelector.Reconstruction

end
end
