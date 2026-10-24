import OTSelector.Reconstruction.OriginalStageResidualDensityOrientedRetainedCut

/-! Actual same-frame retained endpoints have equal raw and reflected canonical smoothing. -/
open Set Function Filter MeasureTheory Module Manifold
open scoped ENNReal ContDiff Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OTSelector.Reconstruction
open OTSelector.Geometry ContinuousFinslerNorm OTSelector.Probability
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
namespace OriginalSeedConditionalMoments
variable {S : CalibratedLevelSeedPatch F u} {w : S.covector.ker} {μ ν : Measure ℝ}
  (D : OriginalSeedConditionalMoments S w μ ν)
include D

/-- Both unchanged original retained endpoints lie deeply enough that the same physical
canonical reflected kernel is the original raw kernel for every cube observation. -/
theorem ae_ae_all_originalOrientedRetainedEndpoints_reflectedKernel_eq_raw
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {kin : ℝ → ℝ → (Fin (finrank ℝ S.covector.ker) → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (Q : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν kin g)
    (b : OrthonormalBasis (Fin (finrank ℝ S.covector.ker)) ℝ
      (EuclideanSpace ℝ (Fin (finrank ℝ S.covector.ker))))
    {R ell : ℝ} (hell : 1 ≤ ell) (hR : 2 * (originalStageFrameCollarFactor b * ell) ≤ R) :
    ∀ᵐ scene ∂(Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))),
      ∀ᵐ e ∂(originalStageRestrictedPathPlan (originalOrientedPathLengthRetained S w b R ell) scene :
        Measure (LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker))),
      ∀ z ∈ originalCenteredPhysicalCubeRegion b (2 * R),
        originalCanonicalOrientedReflectedKernel b R z e.1.1 = originalEuclideanMollifier _ (z - e.1.1) ∧
        originalCanonicalOrientedReflectedKernel b R z e.2.1 = originalEuclideanMollifier _ (z - e.2.1) := by
  filter_upwards [D.ae_ae_original_pairKernel_interior_forward Q] with scene hlegal
  rw [physicalScenePairKernel_apply] at hlegal
  have hedge := ae_of_ae_map measurable_physicalPairAnchor.aemeasurable hlegal
  have hA := (measurableSet_originalOrientedPathLengthRetained S hF hw b R ell).preimage measurable_physicalPairAnchor
  filter_upwards [ae_restrict_of_ae hedge, ae_restrict_mem hA] with e he hret
  have hC : 1 ≤ originalStageFrameCollarFactor b * ell := by nlinarith [one_le_originalStageFrameCollarFactor b]
  have hsource : e.1.1 ∈ originalCenteredPhysicalCubeRegion b (2 * (R - 1)) := by
    rw [mem_originalCenteredPhysicalCubeRegion_iff]
    have hh : 2 * (R - 1) / 2 = R - 1 := by ring
    rw [hh]
    exact (show haarRootCube (Fin (finrank ℝ S.covector.ker)) (R - 2 * (originalStageFrameCollarFactor b * ell)) ⊆
      haarRootCube (Fin (finrank ℝ S.covector.ker)) (R - 1) from by
        intro x hx
        constructor <;> intro i <;> dsimp at * <;> linarith [hx.1 i, hx.2 i]) hret.1
  have htarget : e.2.1 ∈ originalCenteredPhysicalCubeRegion b (2 * (R - 1)) := by
    have hi := D.originalOrientedPathLengthRetained_target_mem_innerCube hF hw b (by linarith) hR hret he.1 he.2.1 he.2.2
    have hpos : e.1.1 + (e.2.1 - e.1.1) = e.2.1 := by abel
    change e.1.1 + (e.2.1 - e.1.1) ∈ originalCenteredPhysicalCubeRegion b
      (2 * (R - originalStageFrameCollarFactor b * ell)) at hi
    rw [hpos] at hi
    exact originalCenteredPhysicalCubeRegion_mono b (by linarith) hi
  intro z hz
  exact ⟨originalCanonicalOrientedReflectedKernel_eq_raw_of_inner b hz hsource,
    originalCanonicalOrientedReflectedKernel_eq_raw_of_inner b hz htarget⟩

/-- Every further actual edge restriction, including a true clock class, has identical
raw and reflected retained endpoint smoothing in the same chosen physical cube. -/
theorem ae_all_originalOrientedRetainedEndpoints_reflectedSmoothing_eq_raw
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {kin : ℝ → ℝ → (Fin (finrank ℝ S.covector.ker) → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (Q : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν kin g)
    (b : OrthonormalBasis (Fin (finrank ℝ S.covector.ker)) ℝ
      (EuclideanSpace ℝ (Fin (finrank ℝ S.covector.ker))))
    {R ell : ℝ} (hell : 1 ≤ ell) (hR : 2 * (originalStageFrameCollarFactor b * ell) ≤ R) :
    ∀ᵐ scene ∂(Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))),
      ∀ (B : Set (LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker))) (z : Fin (finrank ℝ S.covector.ker) → ℝ),
      z ∈ originalCenteredPhysicalCubeRegion b (2 * R) →
      (∫ e in B, originalCanonicalOrientedReflectedKernel b R z e.1.1
        ∂(originalStageRestrictedPathPlan (originalOrientedPathLengthRetained S w b R ell) scene : Measure (LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker)))) =
        (∫ e in B, originalEuclideanMollifier _ (z - e.1.1)
          ∂(originalStageRestrictedPathPlan (originalOrientedPathLengthRetained S w b R ell) scene : Measure (LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker)))) ∧
      (∫ e in B, originalCanonicalOrientedReflectedKernel b R z e.2.1
        ∂(originalStageRestrictedPathPlan (originalOrientedPathLengthRetained S w b R ell) scene : Measure (LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker)))) =
        (∫ e in B, originalEuclideanMollifier _ (z - e.2.1)
          ∂(originalStageRestrictedPathPlan (originalOrientedPathLengthRetained S w b R ell) scene : Measure (LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker)))) := by
  filter_upwards [D.ae_ae_all_originalOrientedRetainedEndpoints_reflectedKernel_eq_raw hF hw Q b hell hR] with scene hs
  intro B z hz
  constructor
  · apply integral_congr_ae
    filter_upwards [ae_restrict_of_ae hs] with e he
    exact (he z hz).1
  · apply integral_congr_ae
    filter_upwards [ae_restrict_of_ae hs] with e he
    exact (he z hz).2

end OriginalSeedConditionalMoments
end OTSelector.Reconstruction
