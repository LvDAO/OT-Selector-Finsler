import OTSelector.MeasureTheory.ProbabilityMeasureVersion
import OTSelector.Reconstruction.FinslerPhysicalSceneRootedGlobal
import OTSelector.Reconstruction.FinslerPhysicalSceneRootedMarginals
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

/-!
# Original global allocation plans as random probability measures

Feasibility makes the original finite plan a probability almost surely.
Only the exceptional event is completed by the original product population;
the sampled target cloud and every realized allocation remain unchanged.
-/
open Set Function MeasureTheory OTSelector.Probability
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false
variable {Ω M : Type*} [MeasurableSpace Ω] [MeasurableSpace M] {n : ℕ}

/-- Probability completion of the actual original global allocation field. -/
def physicalSceneOriginalAllocationProbabilityPlanFamily
    (μ ν : Measure M) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (alloc : Ω → M → Fin (n + 1) → ℝ) (Y : Ω → Fin (n + 1) → M) :
    Ω → ProbabilityMeasure (M × M) :=
  probabilityMeasureVersion (physicalSceneGlobalAllocationFamily μ alloc Y)
    ⟨μ.prod ν, inferInstance⟩

/-- Joint original coefficient and target measurability supplies the entire
probability-plan field on the unchanged experiment. -/
theorem measurable_physicalSceneOriginalAllocationProbabilityPlanFamily
    (μ ν : Measure M) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (alloc : Ω → M → Fin (n + 1) → ℝ)
    (halloc : ∀ k, Measurable (fun z : Ω × M ↦ alloc z.1 z.2 k))
    (Y : Ω → Fin (n + 1) → M) (hY : ∀ k, Measurable (fun w ↦ Y w k)) :
    Measurable (physicalSceneOriginalAllocationProbabilityPlanFamily μ ν alloc Y) :=
  measurable_probabilityMeasureVersion _
    (measurable_physicalSceneGlobalAllocationFamily μ alloc halloc Y hY) _

/-- Actual feasibility supplies mass one before probability completion. -/
theorem ae_isProbabilityMeasure_physicalSceneGlobalAllocationFamily
    (R : Measure Ω) (μ : Measure M) [IsProbabilityMeasure μ]
    (alloc : Ω → M → Fin (n + 1) → ℝ) (Y : Ω → Fin (n + 1) → M)
    (p : Ω → Fin (n + 1) → ℝ)
    (hfeas : ∀ᵐ w ∂R, IsSemidiscreteAllocation μ (p w) (alloc w)) :
    ∀ᵐ w ∂R, IsProbabilityMeasure (physicalSceneGlobalAllocationFamily μ alloc Y w) := by
  filter_upwards [physicalSceneGlobalAllocationFamily_ae_eq R μ alloc Y p hfeas, hfeas]
    with w heq hw
  refine ⟨?_⟩
  rw [heq, ← Measure.fst_univ, physicalSceneAllocationPlan_fst hw (Y w)]
  exact measure_univ

/-- The probability realization is exactly the original plan almost surely. -/
theorem physicalSceneOriginalAllocationProbabilityPlanFamily_ae_eq
    (R : Measure Ω) (μ ν : Measure M) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (alloc : Ω → M → Fin (n + 1) → ℝ) (Y : Ω → Fin (n + 1) → M)
    (p : Ω → Fin (n + 1) → ℝ)
    (hfeas : ∀ᵐ w ∂R, IsSemidiscreteAllocation μ (p w) (alloc w)) :
    (fun w ↦ (physicalSceneOriginalAllocationProbabilityPlanFamily μ ν alloc Y w : Measure (M × M)))
      =ᵐ[R] physicalSceneGlobalAllocationFamily μ alloc Y :=
  probabilityMeasureVersion_ae_eq R _ _
    (ae_isProbabilityMeasure_physicalSceneGlobalAllocationFamily R μ alloc Y p hfeas)

/-- The original deterministic source marginal is retained on the same event. -/
theorem ae_fst_physicalSceneOriginalAllocationProbabilityPlanFamily
    (R : Measure Ω) (μ ν : Measure M) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (alloc : Ω → M → Fin (n + 1) → ℝ) (Y : Ω → Fin (n + 1) → M)
    (p : Ω → Fin (n + 1) → ℝ)
    (hfeas : ∀ᵐ w ∂R, IsSemidiscreteAllocation μ (p w) (alloc w)) :
    ∀ᵐ w ∂R,
      (physicalSceneOriginalAllocationProbabilityPlanFamily μ ν alloc Y w : Measure (M × M)).fst = μ := by
  filter_upwards [physicalSceneOriginalAllocationProbabilityPlanFamily_ae_eq R μ ν alloc Y p hfeas,
    physicalSceneGlobalAllocationFamily_ae_eq R μ alloc Y p hfeas, hfeas] with w heq hraw hw
  rw [heq, hraw, physicalSceneAllocationPlan_fst hw (Y w)]

/-- Two actual opposite-tilt allocations give a joint law on their original
global probability plans, using the same original random environment. -/
def physicalSceneOriginalAllocationPlanPairLaw
    (R : Measure Ω) [IsProbabilityMeasure R]
    (μ ν : Measure M) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (ap am : Ω → M → Fin (n + 1) → ℝ)
    (hpm : ∀ k, Measurable (fun z : Ω × M ↦ ap z.1 z.2 k))
    (hmm : ∀ k, Measurable (fun z : Ω × M ↦ am z.1 z.2 k))
    (Y : Ω → Fin (n + 1) → M) (hY : ∀ k, Measurable (fun w ↦ Y w k)) :
    ProbabilityMeasure (ProbabilityMeasure (M × M) × ProbabilityMeasure (M × M)) :=
  ProbabilityMeasure.map (⟨R, inferInstance⟩ : ProbabilityMeasure Ω)
    ((measurable_physicalSceneOriginalAllocationProbabilityPlanFamily μ ν ap hpm Y hY).prodMk
      (measurable_physicalSceneOriginalAllocationProbabilityPlanFamily μ ν am hmm Y hY)).aemeasurable

end OTSelector.Reconstruction
