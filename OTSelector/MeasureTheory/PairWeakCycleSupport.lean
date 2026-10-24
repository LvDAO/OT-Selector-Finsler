import OTSelector.MeasureTheory.LocalFiniteMeasure
import OTSelector.MeasureTheory.LocalFiniteMeasure.Measurability
import OTSelector.MeasureTheory.LocalFiniteMeasurePair
import OTSelector.MeasureTheory.LocalFiniteMeasurePolish
import OTSelector.Transport.CyclicMonotonicity.CountableRectangleSupport
import OTSelector.Transport.CyclicMonotonicity.CountableTargetRigidity
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Probability.CavitySemidiscreteLocalVersion.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Probability.CavitySemidiscreteLocalVersion`; the selected original proof blocks follow. -/
section

/-!
# MeasureTheory.PairWeakCycleSupport

Conditions: Topological measurable carriers with the precise local-compactness/countability hypotheses in each signature; the weak support theorem also supplies continuous cost, countable bases and vanishing two-cycle witnesses.
Objects: A finite almost-sure version of a random measure, the arithmetic average of two locally finite plans, and monotonicity of the limiting average’s support.
Proof detail: Set nonfinite exceptional values to zero, prove measurable decoding, commute averaging with compact-test integrals, and transfer countably many lower-semicontinuous support witnesses to the weak limit.

## Mathematical sources

- Olav Kallenberg, *Random Measures, Theory and Applications (Springer 2017)*: Chapter 4 opening, pp. 109–110, and Section 4.1 “Weak and vague topologies”, pp. 111–117. https://link.springer.com/chapter/10.1007/978-3-319-41598-7_4
- D. H. Fremlin, *Measure Theory, Volume 4*: Section 437J(d), (f), (g) and Sections 437K–437L, narrow topology and semicontinuous evaluation. https://www1.essex.ac.uk/maths/people/fremlin/chap43.pdf#page=61
- D. H. Fremlin, *Measure Theory, Volume 4*: Sections 418A–418C, measurable maps, products, and limits into metrizable/Polish spaces. https://www1.essex.ac.uk/maths/people/fremlin/chap41.pdf#page=106
- OT-Selector project, *Empirical optimal transport selection on general Finsler manifolds, main.tex*: Section Differentiability from a common diffuse representation, Theorem thm:highd-pressure-differentiability; closing opposite-tilt supergradient/secant squeeze. ../main.tex#L4573

Source relation: Classical measurable-version and vague-topology operations combined with the manuscript’s two-cycle witness argument. Continuity of averaging alone does not prove cyclic monotonicity without the supplied witness decay.
-/

/-!
# Almost surely finite original plans in the vague scene space
-/

open MeasureTheory Set Filter Topology TopologicalSpace
open scoped ENNReal CompactlySupported Classical

noncomputable section
namespace OTSelector.Probability

variable {V X : Type*} [MeasurableSpace V]
  [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
  [T2Space X] [LocallyCompactSpace X] [PseudoMetrizableSpace X]
  [SigmaCompactSpace X] [SecondCountableTopology X]

/-- An actual finite random plan, set to zero only on its nonfinite exceptional event. -/
def finitePlanLocalVersion (π : V → Measure X) (v : V) : LocalFiniteMeasure X := by
  by_cases h : π v univ < ⊤
  · have : IsFiniteMeasure (π v) := ⟨h⟩
    exact ⟨π v, inferInstance⟩
  · exact ⟨0, inferInstance⟩

omit [MeasurableSpace V] [T2Space X] [LocallyCompactSpace X]
  [SecondCountableTopology X] in
@[simp]
theorem coe_finitePlanLocalVersion (π : V → Measure X) (v : V) :
    (finitePlanLocalVersion π v : Measure X) = if π v univ < ⊤ then π v else 0 := by
  by_cases h : π v univ < ⊤ <;> simp [finitePlanLocalVersion, h]

/-- No all-environment feasibility assumption is needed to construct the random vague plan. -/
theorem measurable_finitePlanLocalVersion (π : V → Measure X) (hπ : Measurable π) :
    Measurable (finitePlanLocalVersion π) := by
  apply measurable_localFiniteMeasure_of_measurable_measure
  simp only [coe_finitePlanLocalVersion]
  exact Measurable.ite
    (measurableSet_lt ((Measure.measurable_coe MeasurableSet.univ).comp hπ) measurable_const)
    hπ measurable_const

omit [T2Space X] [LocallyCompactSpace X] [SecondCountableTopology X] in
/-- On the original probability space the version is the original plan almost surely. -/
theorem finitePlanLocalVersion_ae_eq (P : Measure V) (π : V → Measure X)
    (hfinite : ∀ᵐ v ∂P, IsFiniteMeasure (π v)) :
    (fun v ↦ (finitePlanLocalVersion π v : Measure X)) =ᵐ[P] π := by
  filter_upwards [hfinite] with v hv
  rw [coe_finitePlanLocalVersion, ite_eq_left (measure_lt_top (π v) univ)]

namespace LocalFiniteMeasure

/-- The arithmetic mean of two actual locally finite measures. -/
def cavityAverage (π : LocalFiniteMeasure X × LocalFiniteMeasure X) : LocalFiniteMeasure X := by
  have : IsFiniteMeasureOnCompacts ((π.1 : Measure X) + (π.2 : Measure X)) := by
    constructor
    intro K hK
    rw [Measure.add_apply]
    exact ENNReal.add_lt_top.mpr ⟨hK.measure_lt_top, hK.measure_lt_top⟩
  exact ⟨(2 : ℝ≥0∞)⁻¹ • ((π.1 : Measure X) + (π.2 : Measure X)),
    IsFiniteMeasureOnCompacts.smul _ (by norm_num)⟩

omit [BorelSpace X] [T2Space X] [LocallyCompactSpace X] [PseudoMetrizableSpace X]
  [SigmaCompactSpace X] [SecondCountableTopology X] in
@[simp]
theorem coe_cavityAverage (π : LocalFiniteMeasure X × LocalFiniteMeasure X) :
    (cavityAverage π : Measure X) =
      (2 : ℝ≥0∞)⁻¹ • ((π.1 : Measure X) + (π.2 : Measure X)) := rfl

omit [T2Space X] [LocallyCompactSpace X] [PseudoMetrizableSpace X]
  [SigmaCompactSpace X] [SecondCountableTopology X] in
/-- Averaging commutes with every actual compact-test integral. -/
theorem testIntegral_cavityAverage (π : LocalFiniteMeasure X × LocalFiniteMeasure X)
    (f : C_c(X, ℝ)) : testIntegral (cavityAverage π) f =
      (2 : ℝ)⁻¹ * (testIntegral π.1 f + testIntegral π.2 f) := by
  unfold testIntegral
  rw [coe_cavityAverage, integral_smul_measure, integral_add_measure f.integrable f.integrable]
  simp

omit [T2Space X] [LocallyCompactSpace X] [PseudoMetrizableSpace X]
  [SigmaCompactSpace X] [SecondCountableTopology X] in
/-- The averaged actual plan is continuous for the proved vague topology. -/
theorem continuous_cavityAverage :
    Continuous (cavityAverage : LocalFiniteMeasure X × LocalFiniteMeasure X → _) := by
  apply continuous_induced_rng.mpr
  apply continuous_pi
  intro f
  change Continuous (fun π ↦ testIntegral (cavityAverage π) f)
  simp only [testIntegral_cavityAverage]
  exact ((continuous_testIntegral f).comp continuous_fst |>.add
    ((continuous_testIntegral f).comp continuous_snd)).const_mul _

end LocalFiniteMeasure
section Scene
variable {Y : Type*} [TopologicalSpace Y] [MeasurableSpace Y] [BorelSpace Y]
  [T2Space Y] [LocallyCompactSpace Y] [PseudoMetrizableSpace Y]
  [SigmaCompactSpace Y] [SecondCountableTopology Y]

omit [T2Space X] [SecondCountableTopology X] [T2Space Y] in
/-- Open rectangle masses of the averaged actual scene are lower semicontinuous. -/
theorem lowerSemicontinuous_cavityAverage_open {U : Set (X × Y)} (hU : IsOpen U) :
    LowerSemicontinuous (fun π : CavityLocalScene X Y ↦
      (LocalFiniteMeasure.cavityAverage π : Measure (X × Y)) U) :=
  (LocalFiniteMeasure.lowerSemicontinuous_measure_open hU).comp
    LocalFiniteMeasure.continuous_cavityAverage

/-- Every weak limit of the original two-plan laws inherits support monotonicity
from vanishing actual rectangular witnesses. The vague carrier and its lower
semicontinuity are supplied by the constructed measure space. -/
theorem ae_cavityAverage_support_twoCycle_of_weak_witness
    (P : ProbabilityMeasure (CavityLocalScene X Y))
    (Pn : ℕ → ProbabilityMeasure (CavityLocalScene X Y))
    (hweak : Tendsto Pn atTop (𝓝 P))
    (c : X → Y → ℝ) (hc : Continuous (Function.uncurry c))
    {BX : Set (Set X)} {BY : Set (Set Y)}
    (hBX : IsTopologicalBasis BX) (hBY : IsTopologicalBasis BY)
    (hBXcount : BX.Countable) (hBYcount : BY.Countable)
    (hmean : ∀ i : CavityBasisCycleIndex BX BY, CavityBasisCycleValid c i →
      Tendsto (fun n ↦ ∫⁻ π, cavityBasisCycleWitness
        (LocalFiniteMeasure.cavityAverage π : Measure (X × Y)) i ∂(Pn n : Measure (CavityLocalScene X Y)))
        atTop (𝓝 0)) :
    ∀ᵐ π ∂(P : Measure (CavityLocalScene X Y)), OTSelector.Reconstruction.IsTwoCycleMonotone c
      (LocalFiniteMeasure.cavityAverage π : Measure (X × Y)).support := by
  exact ae_isTwoCycleMonotone_support_of_weak_witness_tendsto_zero P Pn hweak
    (fun π ↦ (LocalFiniteMeasure.cavityAverage π : Measure (X × Y)))
    c hc hBX hBY hBXcount hBYcount
    (fun _ hU ↦ lowerSemicontinuous_cavityAverage_open hU) hmean

end Scene
end OTSelector.Probability

end
end
