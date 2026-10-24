import OTSelector.MeasureTheory.LocalFiniteMeasure
import OTSelector.MeasureTheory.LocalFiniteMeasure.Measurability
import OTSelector.MeasureTheory.LocalFiniteMeasurePolish
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Probability.ProbabilityMeasureWeakBorel.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Probability.ProbabilityMeasureWeakBorel`; the selected original proof blocks follow. -/
section

/-!
# MeasureTheory.ProbabilityMeasureWeakBorel

Conditions: A second-countable, sigma-compact, locally compact Hausdorff Borel carrier with the stated pseudo-metrizability; individual declarations explicitly omit unnecessary instances.
Objects: The probability slice of the compact-test measure carrier, its weak topology and the pre-existing evaluation/Giry measurable structure.
Proof detail: Compare the compact-test and weak topologies on total-mass-one measures using Portmanteau; use measurable open evaluations and the generating pi-system to identify the Borel sigma-algebra.

## Mathematical sources

- D. H. Fremlin, *Measure Theory, Volume 4*: Section 437J(d), (f), (g) and Sections 437K–437L, narrow topology and semicontinuous evaluation. https://www1.essex.ac.uk/maths/people/fremlin/chap43.pdf#page=61
- Olav Kallenberg, *Random Measures, Theory and Applications (Springer 2017)*: Chapter 4 opening, pp. 109–110, and Section 4.1 “Weak and vague topologies”, pp. 111–117. https://link.springer.com/chapter/10.1007/978-3-319-41598-7_4
- D. H. Fremlin, *Measure Theory, Volume 4*: Sections 418A–418C, measurable maps, products, and limits into metrizable/Polish spaces. https://www1.essex.ac.uk/maths/people/fremlin/chap41.pdf#page=106

Source relation: A representation-specific proof of weak-Borel/evaluation compatibility on the probability slice. It establishes the converse sigma-algebra inclusion, rather than inferring it from measurable tests alone.
-/

/-!
# The weak Borel measurability of Giry-measurable probability fields

Probability measures are viewed inside the proved Polish compact-test carrier. On the
probability slice, Portmanteau turns compact-test convergence back into weak convergence.
This yields a measurable passage from Giry-measurable fields to the actual weak Borel space.
-/

open Set Function Filter MeasureTheory Topology TopologicalSpace
open OTSelector.Probability
open scoped CompactlySupported BoundedContinuousFunction

noncomputable section
namespace OTSelector.Probability

variable {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
  [T2Space X] [LocallyCompactSpace X] [BorelSpace X]
  [PseudoMetrizableSpace X] [SigmaCompactSpace X] [SecondCountableTopology X]

/-- The probability slice of the actual compact-test measure carrier. -/
abbrev ProbabilityVagueCarrier (X : Type*) [TopologicalSpace X] [MeasurableSpace X] :=
  {μ : LocalFiniteMeasure X // IsProbabilityMeasure (μ : Measure X)}

/-- A probability measure in its unchanged compact-test carrier. -/
def probabilityToVagueCarrier (μ : ProbabilityMeasure X) : ProbabilityVagueCarrier X :=
  ⟨⟨(μ : Measure X), inferInstance⟩, inferInstance⟩

/-- The same actual probability recovered from its compact-test carrier. -/
def vagueCarrierToProbability (μ : ProbabilityVagueCarrier X) : ProbabilityMeasure X :=
  ⟨(μ.val : Measure X), μ.property⟩

omit [SecondCountableTopology X] in
/-- Weak convergence preserves every compact continuous test. -/
theorem continuous_probabilityToVagueCarrier :
    Continuous (probabilityToVagueCarrier : ProbabilityMeasure X → ProbabilityVagueCarrier X) := by
  apply Continuous.subtype_mk
  apply LocalFiniteMeasure.isEmbedding_testIntegral.continuous_iff.mpr
  apply continuous_pi
  intro g
  change Continuous (fun μ : ProbabilityMeasure X ↦ ∫ x, g.toBoundedContinuousFunction x ∂μ)
  exact ProbabilityMeasure.continuous_integral_boundedContinuousFunction g.toBoundedContinuousFunction

/-- On the probability slice, convergence of actual compact tests implies weak convergence. -/
theorem continuous_vagueCarrierToProbability :
    Continuous (vagueCarrierToProbability : ProbabilityVagueCarrier X → ProbabilityMeasure X) := by
  apply continuous_iff_seqContinuous.mpr
  intro μs μ hlim
  apply tendsto_of_forall_isOpen_le_liminf_nat'
  intro G hG
  change (μ.val : Measure X) G ≤ liminf (fun n ↦ ((μs n).val : Measure X) G) atTop
  have hlim' : Tendsto (fun n ↦ (μs n).val) atTop (𝓝 μ.val) :=
    (continuous_subtype_val.tendsto μ).comp hlim
  exact (LocalFiniteMeasure.lowerSemicontinuous_measure_open hG).le_liminf μ.val |>.trans
    (liminf_le_liminf_of_le hlim')

/-- Every Giry-measurable probability field is measurable for the actual weak Borel space.
No compact-support restriction on the field's probabilities is required. -/
theorem measurable_probabilityField_weakBorel_of_measurable_measure
    {Ω : Type*} [MeasurableSpace Ω] (Γ : Ω → ProbabilityMeasure X)
    (hΓ : Measurable (fun ω ↦ (Γ ω : Measure X))) :
    @Measurable Ω (ProbabilityMeasure X) inferInstance (borel (ProbabilityMeasure X)) Γ := by
  let field : Ω → ProbabilityVagueCarrier X := fun ω ↦ probabilityToVagueCarrier (Γ ω)
  have hfield : Measurable field := by
    apply Measurable.subtype_mk
    apply measurable_localFiniteMeasure_of_measurable_measure
    exact hΓ
  let _instWeakBorel : MeasurableSpace (ProbabilityMeasure X) := borel (ProbabilityMeasure X)
  have _instWeakBorelSpace : BorelSpace (ProbabilityMeasure X) := ⟨rfl⟩
  exact continuous_vagueCarrierToProbability.measurable.comp hfield

omit [SecondCountableTopology X] in
/-- Weak Borel probabilities form a Giry-measurable field of the unchanged actual measures. -/
theorem measurable_probabilityMeasure_toMeasure_weakBorel :
    @Measurable (ProbabilityMeasure X) (Measure X) (borel (ProbabilityMeasure X)) inferInstance
      (fun μ ↦ (μ : Measure X)) := by
  let _instWeakBorel : MeasurableSpace (ProbabilityMeasure X) := borel (ProbabilityMeasure X)
  have _instWeakBorelSpace : BorelSpace (ProbabilityMeasure X) := ⟨rfl⟩
  apply Measurable.measure_of_isPiSystem_of_isProbabilityMeasure
    (by rw [BorelSpace.measurable_eq (α := X)]; rfl) isPiSystem_isOpen
  intro U hU
  exact (LocalFiniteMeasure.lowerSemicontinuous_measure_open hU).measurable.comp
    (continuous_subtype_val.comp continuous_probabilityToVagueCarrier).measurable

/-- The pre-existing Giry sigma algebra is exactly the Borel sigma algebra of the actual
weak topology. This theorem does not replace either of the existing structures. -/
theorem probabilityMeasure_giry_eq_weakBorel :
    (inferInstance : MeasurableSpace (ProbabilityMeasure X)) = borel (ProbabilityMeasure X) := by
  apply le_antisymm
  · have hid : @Measurable (ProbabilityMeasure X) (ProbabilityMeasure X)
        (borel (ProbabilityMeasure X)) inferInstance id :=
      measurable_probabilityMeasure_toMeasure_weakBorel.subtype_mk
    intro A hA
    exact hid hA
  · have hid := measurable_probabilityField_weakBorel_of_measurable_measure
      (id : ProbabilityMeasure X → ProbabilityMeasure X) measurable_subtype_coe
    intro A hA
    exact hid hA

/-- The actual weak topology and pre-existing Giry structure satisfy the Borel-space contract. -/
theorem probabilityMeasure_weakBorelSpace : BorelSpace (ProbabilityMeasure X) :=
  ⟨probabilityMeasure_giry_eq_weakBorel⟩

/-- A probability field measurable for the existing Giry structure is weak-Borel measurable. -/
theorem measurable_probabilityField_weakBorel_of_giry
    {Ω : Type*} [MeasurableSpace Ω] (Γ : Ω → ProbabilityMeasure X) (hΓ : Measurable Γ) :
    @Measurable Ω (ProbabilityMeasure X) inferInstance (borel (ProbabilityMeasure X)) Γ :=
  measurable_probabilityField_weakBorel_of_measurable_measure Γ
    (measurable_subtype_coe.comp hΓ)

end OTSelector.Probability

end
end
