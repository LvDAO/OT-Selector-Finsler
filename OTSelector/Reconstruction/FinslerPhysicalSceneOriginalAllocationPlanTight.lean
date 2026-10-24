import OTSelector.Reconstruction.FinslerPhysicalSceneOriginalAllocationPlanLaw
import OTSelector.MeasureTheory.CommonCompactCarrier

/-!
# Original global probability-plan laws are uniformly tight

The actual compact population supports supply one compact weak cohort for
both original plans. No energy estimate is required for this global tightness.
-/
open Set Function Filter MeasureTheory OTSelector.Probability
open scoped Topology ENNReal
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false
variable {Ω M : Type*} [MeasurableSpace Ω] [MeasurableSpace M] {n : ℕ}

/-- Original feasibility and endpoint carriers supply almost sure membership
in the actual compact probability-plan cohort. -/
theorem ae_mem_probabilityCompactCarrier_originalAllocation
    (R : Measure Ω) (μ ν : Measure M) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (alloc : Ω → M → Fin (n + 1) → ℝ) (Y : Ω → Fin (n + 1) → M)
    (p : Ω → Fin (n + 1) → ℝ)
    (hfeas : ∀ᵐ w ∂R, IsSemidiscreteAllocation μ (p w) (alloc w))
    {A B : Set M} (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hμA : ∀ᵐ x ∂μ, x ∈ A) (hYB : ∀ᵐ w ∂R, ∀ k, Y w k ∈ B) :
    ∀ᵐ w ∂R, physicalSceneOriginalAllocationProbabilityPlanFamily μ ν alloc Y w ∈
      probabilityCompactCarrier (A ×ˢ B) := by
  filter_upwards [physicalSceneOriginalAllocationProbabilityPlanFamily_ae_eq R μ ν alloc Y p hfeas,
    ae_physicalSceneGlobalAllocationFamily_carried R μ alloc Y p hfeas hA hB hμA hYB]
    with w heq hcarrier
  change (physicalSceneOriginalAllocationProbabilityPlanFamily μ ν alloc Y w : Measure (M × M))
    (A ×ˢ B)ᶜ = 0
  rw [heq]
  exact ae_iff.mp hcarrier

/-- All original paired-plan laws share a compact weak carrier determined
only by the original compact population supports. -/
theorem isTightMeasureSet_originalAllocationPlanPairLaw
    [TopologicalSpace M] [T2Space M] [BorelSpace M] [SecondCountableTopology M]
    {I : Type*} {Ωi : I → Type*} [∀ i, MeasurableSpace (Ωi i)]
    (m : I → ℕ) (R : ∀ i, Measure (Ωi i)) [∀ i, IsProbabilityMeasure (R i)]
    (μ ν : Measure M) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (ap am : ∀ i, Ωi i → M → Fin (m i + 1) → ℝ)
    (hpm : ∀ i k, Measurable (fun z : Ωi i × M ↦ ap i z.1 z.2 k))
    (hmm : ∀ i k, Measurable (fun z : Ωi i × M ↦ am i z.1 z.2 k))
    (Y : ∀ i, Ωi i → Fin (m i + 1) → M)
    (hY : ∀ i k, Measurable (fun w ↦ Y i w k))
    (p : ∀ i, Ωi i → Fin (m i + 1) → ℝ)
    (hfp : ∀ i, ∀ᵐ w ∂R i, IsSemidiscreteAllocation μ (p i w) (ap i w))
    (hfm : ∀ i, ∀ᵐ w ∂R i, IsSemidiscreteAllocation μ (p i w) (am i w))
    {A B : Set M} (hA : IsCompact A) (hB : IsCompact B)
    (hμA : ∀ᵐ x ∂μ, x ∈ A) (hYB : ∀ i, ∀ᵐ w ∂R i, ∀ k, Y i w k ∈ B) :
    IsTightMeasureSet (range (fun i ↦
      (physicalSceneOriginalAllocationPlanPairLaw (R i) μ ν (ap i) (am i) (hpm i) (hmm i)
        (Y i) (hY i) : Measure (ProbabilityMeasure (M × M) × ProbabilityMeasure (M × M))))) := by
  let C := probabilityCompactCarrier (A ×ˢ B)
  have hC : IsCompact C := isCompact_probabilityCompactCarrier (hA.prod hB)
  have hCm : MeasurableSet C := measurableSet_probabilityCompactCarrier
    (hA.measurableSet.prod hB.measurableSet)
  apply isTightMeasureSet_of_common_compact_carrier _ (C ×ˢ C) (hC.prod hC)
  intro i
  have hplus := ae_mem_probabilityCompactCarrier_originalAllocation (R i) μ ν
    (ap i) (Y i) (p i) (hfp i) hA.measurableSet hB.measurableSet hμA (hYB i)
  have hminus := ae_mem_probabilityCompactCarrier_originalAllocation (R i) μ ν
    (am i) (Y i) (p i) (hfm i) hA.measurableSet hB.measurableSet hμA (hYB i)
  have hpair := (measurable_physicalSceneOriginalAllocationProbabilityPlanFamily μ ν
    (ap i) (hpm i) (Y i) (hY i)).prodMk
      (measurable_physicalSceneOriginalAllocationProbabilityPlanFamily μ ν
        (am i) (hmm i) (Y i) (hY i))
  change (R i).map (fun w ↦
    (physicalSceneOriginalAllocationProbabilityPlanFamily μ ν (ap i) (Y i) w,
      physicalSceneOriginalAllocationProbabilityPlanFamily μ ν (am i) (Y i) w)) (C ×ˢ C)ᶜ = 0
  rw [Measure.map_apply hpair (hCm.prod hCm).compl]
  exact ae_iff.mp (hplus.and hminus)

end OTSelector.Reconstruction
