import OTSelector.Reconstruction.FinslerPhysicalSceneRootedMacroscopicWitness
import OTSelector.Transport.CyclicMonotonicity.OpenDomainCycleSupport
import OTSelector.Probability.CavitySemidiscreteSpatialBasis

/-!
# Full average-plan cycle support at the retained actual macroscopic root

The root tag is kept jointly with both physical plans and the original integer
configuration. Countable open witnesses produce one common almost-sure legal
cycle statement on the full arithmetic-average support inside the macro window.
-/

open Set Function Filter MeasureTheory ProbabilityTheory TopologicalSpace OTSelector.Probability
open scoped Topology ENNReal
noncomputable section
namespace OTSelector.Reconstruction
open PointProcess PointProcess.LocalConfiguration
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

variable {ι : Type*} [Fintype ι]
variable (base : (ι → ℝ) × ℝ)
local instance macroCycleSupportStandardBorel : StandardBorelSpace ((ι → ℝ) × ℝ) := inferInstance
local instance macroCycleSupportConfigTopology : TopologicalSpace (LocalConfiguration base) := vagueTopology _
local instance macroCycleSupportConfigBorel : BorelSpace (LocalConfiguration base) := vagueBorelSpace
local instance macroCycleSupportConfigPolish : PolishSpace (LocalConfiguration base) := vaguePolishSpace
local instance macroCycleSupportPlanPolish : PolishSpace
    (LocalFiniteMeasure (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ))) := LocalFiniteMeasure.instPolishSpace
local notation "MacroScene" => (ι → ℝ) × (CavityLocalScene ((ι → ℝ) × ℝ) ((ι → ℝ) × ℝ) × LocalConfiguration base)

/-- The actual joint macro-window witnesses exclude every strict legal exchange
on the full arithmetic-average support, on one common probability-one event. -/
theorem ae_macroscopic_average_legal_twoCycle_support_of_basis_witness_zero
    (R : ProbabilityMeasure MacroScene) (Emacro : Set (ι → ℝ))
    (c : ((ι → ℝ) × ℝ) → ((ι → ℝ) × ℝ) → ℝ)
    (D : Set (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ))) (hD : IsOpen D)
    (hc : ContinuousOn (Function.uncurry c) D)
    (hzero : ∀ i : CavityBasisCycleIndex
        (cavitySpatialBasis (ι := ι) (A := ℝ)) (cavitySpatialBasis (ι := ι) (A := ℝ)),
      CavityLegalBasisCycleValid c D i →
        ∀ᵐ s ∂(R : Measure MacroScene), physicalSceneMacroscopicAverageWitness base Emacro
          (i.1.1.1.val ×ˢ i.1.1.2.val) (i.1.2.1.val ×ˢ i.1.2.2.val) s = 0) :
    ∀ᵐ s ∂(R : Measure MacroScene), s.1 ∈ Emacro →
      IsTwoCycleMonotoneOn c D
        (((LocalFiniteMeasure.cavityAverage s.2.1 : Measure _).support) ∩ D) := by
  let _instCount : Countable (cavitySpatialBasis (ι := ι) (A := ℝ)) :=
    countable_cavitySpatialBasis.to_subtype
  have hall : ∀ᵐ s ∂(R : Measure MacroScene),
      ∀ i : CavityBasisCycleIndex
        (cavitySpatialBasis (ι := ι) (A := ℝ)) (cavitySpatialBasis (ι := ι) (A := ℝ)),
        CavityLegalBasisCycleValid c D i → physicalSceneMacroscopicAverageWitness base Emacro
          (i.1.1.1.val ×ˢ i.1.1.2.val) (i.1.2.1.val ×ˢ i.1.2.2.val) s = 0 := by
    apply ae_all_iff.mpr
    intro i
    by_cases hi : CavityLegalBasisCycleValid c D i
    · exact (hzero i hi).mono fun _ h _ ↦ h
    · exact Eventually.of_forall fun _ h ↦ False.elim (hi h)
  filter_upwards [hall] with s hs hmacro
  apply support_legal_twoCycle_of_basis_witness_zero c D hD hc
    isTopologicalBasis_cavitySpatialBasis isTopologicalBasis_cavitySpatialBasis
    (LocalFiniteMeasure.cavityAverage s.2.1 : Measure _)
  intro i hi
  have hw := hs i hi
  simpa only [physicalSceneMacroscopicAverageWitness,
    Set.indicator_of_mem (show s ∈ Prod.fst ⁻¹' Emacro from hmacro),
    cavityBasisCycleWitness] using hw

end OTSelector.Reconstruction
