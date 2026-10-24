import OTSelector.Reconstruction.OriginalScreeningBoundaryBudgetFullSlabMass
import OTSelector.Reconstruction.OriginalStageResidualDensityEndpointReadouts

/-! The actual full-main delta is the true full-current flux plus both full-input boundary masses. -/
open Set Function Filter MeasureTheory Module Manifold
open scoped ENNReal Topology ContDiff
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OTSelector.Reconstruction
open OTSelector.Geometry ContinuousFinslerNorm OTSelector.Probability

/-- Finite genuine clock prefixes differ by precisely their two original half slabs. -/
theorem originalMarkedClockPrefix_sub_eq_halfSlabs {X : Type*} [MeasurableSpace X]
    (σ : Measure (X × ℝ)) [IsFiniteMeasure σ] {s t : ℝ} (hst : s ≤ t) :
    σ.real {p | p.2 < t} - σ.real {p | p.2 < s} = σ.real {p | p.2 ∈ Ico s t} ∧
    σ.real {p | p.2 ≤ t} - σ.real {p | p.2 ≤ s} = σ.real {p | p.2 ∈ Ioc s t} := by
  have hs : {p : X × ℝ | p.2 < s} ⊆ {p | p.2 < t} := fun _ hp ↦ hp.trans_le hst
  have ht : {p : X × ℝ | p.2 ≤ s} ⊆ {p | p.2 ≤ t} := fun _ hp ↦ hp.trans hst
  have hS := measureReal_sdiff (μ := σ) hs (measurableSet_lt measurable_snd measurable_const)
  have hT := measureReal_sdiff (μ := σ) ht (measurableSet_le measurable_snd measurable_const)
  have eS : {p : X × ℝ | p.2 < t} \ {p | p.2 < s} = {p | p.2 ∈ Ico s t} := by
    ext p
    simp only [Set.mem_sdiff, Set.mem_ofPred_eq, mem_Ico, not_lt, and_comm]
  have eT : {p : X × ℝ | p.2 ≤ t} \ {p | p.2 ≤ s} = {p | p.2 ∈ Ioc s t} := by
    ext p
    simp only [Set.mem_sdiff, Set.mem_ofPred_eq, mem_Ioc, not_le, and_comm]
  exact ⟨by rw [eS] at hS; exact hS.symm, by rw [eT] at hT; exact hT.symm⟩

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}

omit [BorelSpace E] in
/-- The genuine full slab count/cut error is exactly the increment of the paper's actual
full-main delta, retaining source strict prefixes and target closed prefixes. -/
theorem originalScreeningFullSlabCutError_eq_fullCutError_sub
    (S : CalibratedLevelSeedPatch F u) (w : S.covector.ker) (R : ℝ)
    (scene : LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))
    {s t : ℝ} (hst : s ≤ t)
    [IsFiniteMeasure ((legalInputColorMeasure _ scene.2 0).restrict {p | p.1 ∈ haarRootCube _ R})]
    [IsFiniteMeasure ((legalInputColorMeasure _ scene.2 1).restrict {p | p.1 ∈ haarRootCube _ R})] :
    originalScreeningFullSlabCutError S w R s t scene =
      originalStageFullCutError S w R t (originalEuclideanMollifier _) scene -
      originalStageFullCutError S w R s (originalEuclideanMollifier _) scene := by
  have hs := (originalMarkedClockPrefix_sub_eq_halfSlabs
    ((legalInputColorMeasure _ scene.2 0).restrict {p | p.1 ∈ haarRootCube _ R}) hst).1
  have ht := (originalMarkedClockPrefix_sub_eq_halfSlabs
    ((legalInputColorMeasure _ scene.2 1).restrict {p | p.1 ∈ haarRootCube _ R}) hst).2
  unfold originalScreeningFullSlabCutError originalStageFullCutError originalStageMainInputPrefix
  rw [← hs, ← ht]
  ring

namespace OriginalSeedConditionalMoments
variable {S : CalibratedLevelSeedPatch F u} {w : S.covector.ker} {μ ν : Measure ℝ}
  (D : OriginalSeedConditionalMoments S w μ ν)
include D

/-- The paper's actual full-main delta at every fixed physical cut is the literal original
prefix-current boundary flux plus both same-scene full-input reflected masses. Actual
clock support removes the first cut and first prefix internally. -/
theorem ae_originalStageFullCutError_eq_flux_add_inputMasses
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {gap diameter : ℝ} (hbounds : ConditionalClockSupportBounds μ ν gap diameter)
    {g : ℝ → ℝ → ℝ}
    (Q : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν
      (D.originalFocalKinetic gap) g)
    {R : ℝ} (hR : 1 ≤ R) {c : ℝ} (hc : D.lo + (S.level : ℝ) ≤ c) :
    let η := originalEuclideanMollifier (finrank ℝ S.covector.ker)
    let lo := D.lo + (S.level : ℝ)
    ∀ᵐ scene ∂(Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))),
      originalStageFullCutError S w R c η scene =
        originalStageAxisBoundaryPairing
          (fun z ↦ originalSeedPathClockSetCurrent S w (fun x ↦ η (x-z)) (Ioc lo c) scene) R (fun _ ↦ 1) +
        originalScreeningReflectedInputMass R (Ico lo c) 0 scene -
        originalScreeningReflectedInputMass R (Ioc lo c) 1 scene := by
  let : IsProbabilityMeasure μ := D.support.source.probability
  let : IsProbabilityMeasure ν := D.support.target.probability
  filter_upwards [D.ae_originalScreening_fullSlabCutError_eq_flux_add_inputMasses hF hw hbounds Q hR hc,
    D.ae_originalStageEndpointReadouts Q R,
    Q.ae_finite_reflectedInputOuterWindow R 0, Q.ae_finite_reflectedInputOuterWindow R 1]
      with scene hslab hends hfinS hfinT
  have hsub : {p : LegalMarkedPhysicalPoint (finrank ℝ S.covector.ker) | p.1 ∈ haarRootCube _ R} ⊆
      haarRootCube _ (R+1) ×ˢ (univ : Set ℝ) := by
    intro p hp
    exact ⟨⟨fun i ↦ by linarith [hp.1 i], fun i ↦ by linarith [hp.2 i]⟩, mem_univ _⟩
  let : IsFiniteMeasure ((legalInputColorMeasure _ scene.2 0).restrict {p | p.1 ∈ haarRootCube _ R}) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact (measure_mono hsub).trans_lt hfinS⟩
  let : IsFiniteMeasure ((legalInputColorMeasure _ scene.2 1).restrict {p | p.1 ∈ haarRootCube _ R}) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact (measure_mono hsub).trans_lt hfinT⟩
  rw [originalScreeningFullSlabCutError_eq_fullCutError_sub S w R scene hc] at hslab
  have hzero : originalStageFullCutError S w R (D.lo + (S.level : ℝ)) (originalEuclideanMollifier _) scene = 0 := by
    rw [originalStageFullCutError, hends.2.2.1, hends.1]
    simp only [integral_zero_measure, integral_zero, sub_self]
  simpa only [hzero, sub_zero] using hslab

end OriginalSeedConditionalMoments
end OTSelector.Reconstruction
