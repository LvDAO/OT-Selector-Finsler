import OTSelector.MeasureTheory.LusinCompactCore
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Geometry.LusinCompactProperty.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Geometry.LusinCompactProperty`; the selected original proof blocks follow. -/
section

/-!
Conditions: A finite inner-regular measure, a measurable or almost-everywhere measurable map into the stated second-countable target, and an almost-everywhere property.

Objects: A large compact set with continuous readout where the property holds at every point.

Proof detail: Remove a measurable null envelope of the exceptional set before applying Lusin and compact inner regularity.

Sources: D. H. Fremlin, Section 418J (second-countable target Lusin theorem), with compact inner regularity in Section 416 (https://www1.essex.ac.uk/maths/people/fremlin/chap41.pdf#page=110); D. H. Fremlin, Definition 411B, pp. 3–4, and Lemma 412A(c), pp. 10–11 (https://www1.essex.ac.uk/maths/people/fremlin/chap41.pdf#page=3).
Relation: Lusin/inner-regularity corollary; the property itself need not have a measurable truth set.
-/

/-!
# Compact continuity cores retaining an almost-everywhere property

Remove a measurable null envelope of the bad points before applying Lusin's theorem.
The resulting compact set retains the original function and the property at every point,
even when the property itself has not been proved measurable.
-/

open Set MeasureTheory
open scoped ENNReal

namespace OTSelector.Geometry

/-- An almost-everywhere property can hold at every point of a compact Lusin core,
with arbitrarily small loss of the original measure. No measurability of the property
or completeness of the measure is required. -/
theorem exists_lusin_compact_core_with_ae_property
    {E Y : Type*} [TopologicalSpace E] [PolishSpace E]
    [MeasurableSpace E] [BorelSpace E] [TopologicalSpace Y] [MeasurableSpace Y]
    [OpensMeasurableSpace Y] [SecondCountableTopology Y]
    {ν : Measure E} {s : Set E} (hs : MeasurableSet s) (hνs : ν s ≠ ∞)
    {f : E → Y} (hf : Measurable f) {P : E → Prop}
    (hP : ∀ᵐ x ∂ν.restrict s, P x) {ε : ℝ≥0∞} (hε : ε ≠ 0) :
    ∃ K ⊆ s, IsCompact K ∧ ν (s \ K) < ε ∧ ContinuousOn f K ∧ ∀ x ∈ K, P x := by
  have hnull : ν {x | x ∈ s ∧ ¬P x} = 0 := by
    simpa only [not_imp] using ae_iff.mp ((ae_restrict_iff' hs).mp hP)
  obtain ⟨N, hNbad, hNm, hNzero⟩ := exists_measurable_superset_of_null hnull
  obtain ⟨K, hsub, hc, hmass, hcont⟩ := exists_lusin_compact_core (hs.diff hNm)
    (ne_top_of_le_ne_top hνs (measure_mono sdiff_subset)) hf hε
  refine ⟨K, hsub.trans sdiff_subset, hc, ?_, hcont, ?_⟩
  · calc
      ν (s \ K) ≤ ν ((s \ N) \ K ∪ N) := measure_mono (by
        intro x hx
        by_cases hxN : x ∈ N
        · exact Or.inr hxN
        · exact Or.inl ⟨⟨hx.1, hxN⟩, hx.2⟩)
      _ ≤ ν ((s \ N) \ K) + ν N := measure_union_le _ _
      _ = ν ((s \ N) \ K) := by rw [hNzero, add_zero]
      _ < ε := hmass
  · intro x hx
    by_contra hj
    exact (hsub hx).2 (hNbad ⟨(hsub hx).1, hj⟩)

end OTSelector.Geometry

end
