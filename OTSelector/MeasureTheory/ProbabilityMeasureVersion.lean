import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

/-!
## Lemma skeleton

* **Conditions:** A measurable measure-valued map normalized almost everywhere and one fallback probability.
* **Objects:** A probability-valued version equal to the original almost everywhere.
* **Proof detail:** Use measurable if-then-else on the measurable unit-mass event.

## Mathematical sources

* D. H. Fremlin, *Measure Theory, Volume 4*, Sections 418A–418C, measurable maps, products, and limits into metrizable/Polish spaces.
  https://www1.essex.ac.uk/maths/people/fremlin/chap41.pdf#page=106
* D. H. Fremlin, *Measure Theory, Volume 4*, Section 452A–452F (integration of families and disintegrations), 452M (product disintegration).
  https://www1.essex.ac.uk/maths/people/fremlin/chap45.pdf#page=18

**Relationship to the sources:** The subtype/fallback constructor is a Lean implementation of measurable pasting, not a separate classical theorem.
-/

/-!
# Measurable probability versions of almost surely normalized measures

A fixed probability law completes only the exceptional nonprobability event.
The original random measure is retained exactly almost everywhere.
-/
open Set MeasureTheory
noncomputable section
namespace OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
variable {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]

/-- Complete the exceptional event using one fixed probability measure. -/
def probabilityMeasureVersion (Γ : Ω → Measure X) (fallback : ProbabilityMeasure X)
    (ω : Ω) : ProbabilityMeasure X := by
  classical
  refine ⟨if IsProbabilityMeasure (Γ ω) then Γ ω else (fallback : Measure X), ?_⟩
  split_ifs with h
  · exact h
  · infer_instance

/-- Giry measurability is retained without topological assumptions on the
original experiment. -/
theorem measurable_probabilityMeasureVersion
    (Γ : Ω → Measure X) (hΓ : Measurable Γ) (fallback : ProbabilityMeasure X) :
    Measurable (probabilityMeasureVersion Γ fallback) := by
  classical
  apply Measurable.subtype_mk
  change Measurable (fun ω ↦ if IsProbabilityMeasure (Γ ω) then Γ ω else (fallback : Measure X))
  exact Measurable.ite (ProbabilityMeasure.measurableSet_isProbabilityMeasure.preimage hΓ)
    hΓ measurable_const

omit [MeasurableSpace Ω] in
/-- Every normalized realization is the literal original measure. -/
theorem coe_probabilityMeasureVersion_of_probability
    (Γ : Ω → Measure X) (fallback : ProbabilityMeasure X) (ω : Ω)
    (h : IsProbabilityMeasure (Γ ω)) :
    (probabilityMeasureVersion Γ fallback ω : Measure X) = Γ ω := by
  simp only [probabilityMeasureVersion, ProbabilityMeasure.coe_mk, ite_eq_left h]

/-- Almost sure normalization changes no original random plan or readout. -/
theorem probabilityMeasureVersion_ae_eq
    (R : Measure Ω) (Γ : Ω → Measure X) (fallback : ProbabilityMeasure X)
    (hΓ : ∀ᵐ ω ∂R, IsProbabilityMeasure (Γ ω)) :
    (fun ω ↦ (probabilityMeasureVersion Γ fallback ω : Measure X)) =ᵐ[R] Γ :=
  hΓ.mono fun ω hω ↦ coe_probabilityMeasureVersion_of_probability Γ fallback ω hω

end OTSelector.Probability
