import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Measure.RegularityCompacts

/-!
## Lemma skeleton

* **Conditions:** A measurable or a.e.-measurable map on a Polish source; finite mass on the chosen set.
* **Objects:** A compact subset losing arbitrarily little measure with continuous restricted map.
* **Proof detail:** Apply Lusin with a second-countable target and compact inner regularity.

## Mathematical sources

* D. H. Fremlin, *Measure Theory, Volume 4*, Section 418J (second-countable target Lusin theorem), with compact inner regularity in Section 416.
  https://www1.essex.ac.uk/maths/people/fremlin/chap41.pdf#page=110

**Relationship to the sources:** The a.e. version and specified measurable-set compact core are direct regular-measure refinements of 418J.
-/

/-!
# Compact Lusin cores

A measurable map on a Polish space becomes continuous after discarding arbitrarily
little measure from any measurable set of finite measure. The compact core is compact
in the original topology; no compactness of the ambient space is assumed.
-/

open Set MeasureTheory TopologicalSpace
open scoped ENNReal

namespace OTSelector.Geometry

private theorem continuousOn_of_finer_compact
    {E F : Type*} {t t' : TopologicalSpace E} [TopologicalSpace F]
    [@T2Space E t] (hle : t' ≤ t) {f : E → F}
    (hf : @Continuous E F t' _ f) {K : Set E} (hK : @IsCompact E t' K) :
    @IsCompact E t K ∧ @ContinuousOn E F t _ f K := by
  have hc : @Continuous E E t' t id := continuous_id_of_le hle
  have hcompact (s : Set E) (hs : @IsCompact E t' s) : @IsCompact E t s := by
    simpa only [image_id] using @IsCompact.image E E t' t s id hs hc
  refine ⟨hcompact K hK, (@continuousOn_iff_isClosed E F t _ f K).mpr ?_⟩
  intro s hs
  refine ⟨f ⁻¹' s ∩ K, ?_, by simp only [inter_assoc, inter_self]⟩
  exact @IsCompact.isClosed E t _ _ (hcompact _ (hK.inter_left (hs.preimage hf)))

/-- A measurable function has a compact continuity core in each measurable set of finite
measure, with arbitrarily small discarded measure. All compactness and continuity in the
conclusion refer to the original topology. -/
theorem exists_lusin_compact_core
    {E F : Type*} [t : TopologicalSpace E] [PolishSpace E]
    [MeasurableSpace E] [BorelSpace E] [TopologicalSpace F] [MeasurableSpace F]
    [OpensMeasurableSpace F] [SecondCountableTopology F]
    {μ : Measure E} {s : Set E} (hs : MeasurableSet s) (hμs : μ s ≠ ∞)
    {f : E → F} (hf : Measurable f) {ε : ℝ≥0∞} (hε : ε ≠ 0) :
    ∃ K ⊆ s, IsCompact K ∧ μ (s \ K) < ε ∧ ContinuousOn f K := by
  obtain ⟨t', hle, hcont, hpolish⟩ := hf.exists_continuous
  have hborel : @borel E t' = @borel E t :=
    MeasureTheory.borel_eq_borel_of_le hpolish inferInstance hle
  let : TopologicalSpace E := t'
  let : PolishSpace E := hpolish
  let : BorelSpace E := ⟨by rw [hborel]; exact BorelSpace.measurable_eq⟩
  obtain ⟨K, hKs, hK, hsmall⟩ := hs.exists_isCompact_sdiff_lt hμs hε
  obtain ⟨hKold, hfK⟩ := continuousOn_of_finer_compact hle hcont hK
  exact ⟨K, hKs, hKold, hsmall, hfK⟩

/-- The compact-core conclusion applies to an almost-everywhere measurable function itself,
not just to a measurable representative: the exceptional null set is excluded from the core. -/
theorem exists_lusin_compact_core_of_aemeasurable
    {E F : Type*} [TopologicalSpace E] [PolishSpace E]
    [MeasurableSpace E] [BorelSpace E] [TopologicalSpace F] [MeasurableSpace F]
    [OpensMeasurableSpace F] [SecondCountableTopology F]
    {μ : Measure E} {s : Set E} (hs : MeasurableSet s) (hμs : μ s ≠ ∞)
    {f : E → F} (hf : AEMeasurable f μ) {ε : ℝ≥0∞} (hε : ε ≠ 0) :
    ∃ K ⊆ s, IsCompact K ∧ μ (s \ K) < ε ∧ ContinuousOn f K := by
  obtain ⟨N, hNbad, hNmeas, hNzero⟩ :=
    exists_measurable_superset_of_null (ae_iff.mp hf.ae_eq_mk)
  obtain ⟨K, hKsub, hK, hsmall, hfK⟩ :=
    exists_lusin_compact_core (hs.diff hNmeas)
      (ne_top_of_le_ne_top hμs (measure_mono sdiff_subset)) hf.measurable_mk hε
  refine ⟨K, hKsub.trans sdiff_subset, hK, ?_, hfK.congr ?_⟩
  · calc
      μ (s \ K) ≤ μ ((s \ N) \ K ∪ N) := measure_mono (by
        intro x hx
        by_cases hxN : x ∈ N
        · exact Or.inr hxN
        · exact Or.inl ⟨⟨hx.1, hxN⟩, hx.2⟩)
      _ ≤ μ ((s \ N) \ K) + μ N := measure_union_le _ _
      _ = μ ((s \ N) \ K) := by rw [hNzero, add_zero]
      _ < ε := hsmall
  · intro x hx
    by_contra hne
    exact (hKsub hx).2 (hNbad hne)

end OTSelector.Geometry
