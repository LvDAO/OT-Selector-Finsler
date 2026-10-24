import OTSelector.Reconstruction.OriginalScreeningBoundaryBudgetOrientedSlabMass
import OTSelector.Reconstruction.OriginalScreeningBoundaryBudgetWindowEndpoints
import OTSelector.Reconstruction.OriginalScreeningBoundaryBudgetFullCutIdentity

/-! The actual full-main delta is the true full-current flux plus both full-input boundary masses. -/
open Set Function Filter MeasureTheory Module Manifold
open scoped ENNReal Topology ContDiff
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OTSelector.Reconstruction
open OTSelector.Geometry ContinuousFinslerNorm OTSelector.Probability

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}

omit [BorelSpace E] in
/-- The genuine full slab count/cut error is exactly the increment of the paper's actual
full-main delta, retaining source strict prefixes and target closed prefixes. -/
theorem originalScreeningOrientedFullSlabCutError_eq_fullCutError_sub
    (S : CalibratedLevelSeedPatch F u) (w : S.covector.ker)
    (b : OrthonormalBasis (Fin (finrank ℝ S.covector.ker)) ℝ
      (EuclideanSpace ℝ (Fin (finrank ℝ S.covector.ker)))) (R : ℝ)
    (scene : LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))
    {s t : ℝ} (hst : s ≤ t)
    [IsFiniteMeasure ((legalInputColorMeasure _ scene.2 0).restrict {p | p.1 ∈ originalCenteredPhysicalCubeRegion b (2*R)})]
    [IsFiniteMeasure ((legalInputColorMeasure _ scene.2 1).restrict {p | p.1 ∈ originalCenteredPhysicalCubeRegion b (2*R)})] :
    originalScreeningOrientedFullSlabCutError S w b R s t scene =
      originalOrientedStageFullCutError S w b R t scene -
      originalOrientedStageFullCutError S w b R s scene := by
  have hs := (originalMarkedClockPrefix_sub_eq_halfSlabs
    ((legalInputColorMeasure _ scene.2 0).restrict {p | p.1 ∈ originalCenteredPhysicalCubeRegion b (2*R)}) hst).1
  have ht := (originalMarkedClockPrefix_sub_eq_halfSlabs
    ((legalInputColorMeasure _ scene.2 1).restrict {p | p.1 ∈ originalCenteredPhysicalCubeRegion b (2*R)}) hst).2
  unfold originalScreeningOrientedFullSlabCutError originalOrientedStageFullCutError originalStageMainInputWindowPrefix
  rw [← hs, ← ht]
  ring

namespace OriginalSeedConditionalMoments
variable {S : CalibratedLevelSeedPatch F u} {w : S.covector.ker} {μ ν : Measure ℝ}
  (D : OriginalSeedConditionalMoments S w μ ν)
include D

/-- The paper's actual full-main delta at every fixed physical cut is the literal original
prefix-current boundary flux plus both same-scene full-input reflected masses. Actual
clock support removes the first cut and first prefix internally. -/
theorem ae_originalOrientedStageFullCutError_eq_flux_add_inputMasses
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {gap diameter : ℝ} (hbounds : ConditionalClockSupportBounds μ ν gap diameter)
    {g : ℝ → ℝ → ℝ}
    (Q : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν
      (D.originalFocalKinetic gap) g)
    (b : OrthonormalBasis (Fin (finrank ℝ S.covector.ker)) ℝ
      (EuclideanSpace ℝ (Fin (finrank ℝ S.covector.ker))))
    {R : ℝ} (hR : 1 ≤ R) {c : ℝ} (hc : D.lo + (S.level : ℝ) ≤ c) :
    let η := originalEuclideanMollifier (finrank ℝ S.covector.ker)
    let lo := D.lo + (S.level : ℝ)
    ∀ᵐ scene ∂(Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))),
      originalOrientedStageFullCutError S w b R c scene =
        originalScreeningPhysicalCurrentBoundaryPairing b
          (fun z ↦ originalSeedPathClockSetCurrent S w (fun x ↦ η (x-z)) (Ioc lo c) scene) (2*R) (fun _ ↦ 1) +
        originalScreeningOrientedReflectedInputMass b R (Ico lo c) 0 scene -
        originalScreeningOrientedReflectedInputMass b R (Ioc lo c) 1 scene := by
  let : IsProbabilityMeasure μ := D.support.source.probability
  let : IsProbabilityMeasure ν := D.support.target.probability
  filter_upwards [D.ae_originalScreening_orientedFullSlabCutError_eq_flux_add_inputMasses hF hw hbounds Q b hR hc,
    D.ae_all_originalStageMainInputWindowPrefix_extremes Q,
    Q.ae_finite_orientedReflectedInputOuterWindow b (2*R) 0, Q.ae_finite_orientedReflectedInputOuterWindow b (2*R) 1]
      with scene hslab hends hfinS hfinT
  have hsub : {p : LegalMarkedPhysicalPoint (finrank ℝ S.covector.ker) |
      p.1 ∈ originalCenteredPhysicalCubeRegion b (2*R)} ⊆
      originalCenteredPhysicalCubeRegion b (2*R+2) ×ˢ (univ : Set ℝ) := by
    intro p hp
    exact ⟨originalCenteredPhysicalCubeRegion_mono b (by linarith) hp, mem_univ _⟩
  let : IsFiniteMeasure ((legalInputColorMeasure _ scene.2 0).restrict {p | p.1 ∈ originalCenteredPhysicalCubeRegion b (2*R)}) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact (measure_mono hsub).trans_lt hfinS⟩
  let : IsFiniteMeasure ((legalInputColorMeasure _ scene.2 1).restrict {p | p.1 ∈ originalCenteredPhysicalCubeRegion b (2*R)}) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact (measure_mono hsub).trans_lt hfinT⟩
  rw [originalScreeningOrientedFullSlabCutError_eq_fullCutError_sub S w b R scene hc] at hslab
  have hzero : originalOrientedStageFullCutError S w b R (D.lo + (S.level : ℝ)) scene = 0 := by
    rw [originalOrientedStageFullCutError, (hends.2.2 _).1, hends.1]
    simp only [integral_zero_measure, integral_zero, sub_self]
  simpa only [hzero, sub_zero] using hslab

end OriginalSeedConditionalMoments
end OTSelector.Reconstruction
