import OTSelector.MeasureTheory.LocalFiniteMeasure.Measurability
import OTSelector.Probability.CavitySemidiscretePlanMeasurable
import OTSelector.MeasureTheory.LocalFiniteMeasurePolish

/-!
Conditions: A family of locally finite measures is measurable as an ordinary measure-valued map in the stated topology/Borel setting.

Objects: Measurability of the same family as LocalFiniteMeasure.

Proof detail: Use the measurable embedding into a standard-Borel presentation and the actual measure/test-evaluation identities.

Sources: D. H. Fremlin, Section 424B(b)–(d), 424C–424D, pp. 30–31; Section 424G, p. 31 (https://www1.essex.ac.uk/maths/people/fremlin/chap42.pdf#page=30); D. H. Fremlin, Sections 418A–418C, measurable maps, products, and limits into metrizable/Polish spaces (https://www1.essex.ac.uk/maths/people/fremlin/chap41.pdf#page=106).
Relation: Borel-presentation adapter for the locally finite-measure encoding; no density or Markov structure is asserted.
-/

/-!
# Actual semidiscrete plans in the diffuse vague carrier

The measurable measure-valued plans built from original allocation coefficients
lift to the compact-test Borel space. Finite mass is derived from the exact
source marginal, and no separate scene measurability premise is needed.
-/

open MeasureTheory Set TopologicalSpace
open scoped BigOperators ENNReal CompactlySupported

noncomputable section
namespace OTSelector.Probability

variable {V X : Type*} [MeasurableSpace V]
  [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
  [T2Space X] [LocallyCompactSpace X] [PseudoMetrizableSpace X]
  [SigmaCompactSpace X] [SecondCountableTopology X]



section Allocation
variable {m : ℕ} {S Y : Type*} [MeasurableSpace S] [MeasurableSpace Y]

/-- Actual feasibility supplies finiteness of the entire source-label plan. -/
theorem IsSemidiscreteAllocation.isFiniteMeasure_allocationMeasure
    {μ : Measure S} [IsFiniteMeasure μ] {p : Fin (m + 1) → ℝ}
    {a : S → Fin (m + 1) → ℝ} (ha : IsSemidiscreteAllocation μ p a) :
    IsFiniteMeasure (semidiscreteAllocationMeasure μ a) := by
  constructor
  have heq : semidiscreteAllocationMeasure μ a univ = μ univ := by
    calc
      _ = (semidiscreteAllocationMeasure μ a).map Prod.fst univ := by
        rw [Measure.map_apply measurable_fst MeasurableSet.univ, preimage_univ]
      _ = μ univ := congrArg (fun ν ↦ ν univ) ha.isCoupling.1
  rw [heq]
  exact measure_lt_top μ univ

omit [MeasurableSpace V] [TopologicalSpace X] [BorelSpace X] [T2Space X]
  [LocallyCompactSpace X] [PseudoMetrizableSpace X] [SigmaCompactSpace X]
  [SecondCountableTopology X] in
/-- Every finite scaled actual allocation plan is locally finite after its actual
source and target observation maps. -/
theorem IsSemidiscreteAllocation.isFiniteMeasure_scaled_parameterizedPlan
    {μ : Measure S} [IsFiniteMeasure μ] (a : V × S → Fin (m + 1) → ℝ)
    (p : V → Fin (m + 1) → ℝ) (ha : ∀ v, IsSemidiscreteAllocation μ (p v) (fun s ↦ a (v, s)))
    (f : V × S → X) (y : V → Fin (m + 1) → Y)
    (N : V → ℝ) (v : V) :
    IsFiniteMeasure (ENNReal.ofReal (N v) • parameterizedSemidiscretePlan μ a f y v) := by
  have := (ha v).isFiniteMeasure_allocationMeasure
  unfold parameterizedSemidiscretePlan
  constructor
  simp only [Measure.smul_apply, smul_eq_mul]
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top _ _)

end Allocation

variable {m : ℕ} {S Y : Type*} [MeasurableSpace S]
  [TopologicalSpace Y] [MeasurableSpace Y] [BorelSpace Y]
  [T2Space Y] [LocallyCompactSpace Y] [PseudoMetrizableSpace Y]
  [SigmaCompactSpace Y] [SecondCountableTopology Y]

/-- The original finite allocation plan as a member of the actual vague carrier. -/
def parameterizedSemidiscreteLocalPlan
    (μ : Measure S) [IsFiniteMeasure μ] (a : V × S → Fin (m + 1) → ℝ)
    (p : V → Fin (m + 1) → ℝ) (ha : ∀ v, IsSemidiscreteAllocation μ (p v) (fun s ↦ a (v, s)))
    (f : V × S → X) (y : V → Fin (m + 1) → Y) (N : V → ℝ) (v : V) :
    LocalFiniteMeasure (X × Y) := by
  haveI := IsSemidiscreteAllocation.isFiniteMeasure_scaled_parameterizedPlan a p ha f y N v
  exact ⟨ENNReal.ofReal (N v) • parameterizedSemidiscretePlan μ a f y v, inferInstance⟩

/-- Jointly measurable original coefficients, physical endpoints and mass scaling
produce a Borel random diffuse plan. -/
theorem measurable_parameterizedSemidiscreteLocalPlan
    (μ : Measure S) [IsFiniteMeasure μ] (a : V × S → Fin (m + 1) → ℝ)
    (p : V → Fin (m + 1) → ℝ) (hfeas : ∀ v, IsSemidiscreteAllocation μ (p v) (fun s ↦ a (v, s)))
    (ha : ∀ j, Measurable (fun z ↦ a z j))
    (f : V × S → X) (hf : Measurable f)
    (y : V → Fin (m + 1) → Y) (hy : ∀ j, Measurable (fun v ↦ y v j))
    (N : V → ℝ) (hN : Measurable N) :
    Measurable (parameterizedSemidiscreteLocalPlan μ a p hfeas f y N) := by
  apply measurable_localFiniteMeasure_of_measurable_measure
  exact measurable_scaled_parameterizedSemidiscretePlan μ a ha f hf y hy _ hN.ennreal_ofReal

end OTSelector.Probability
