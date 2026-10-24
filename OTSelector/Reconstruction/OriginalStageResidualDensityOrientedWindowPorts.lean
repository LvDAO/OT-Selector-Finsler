import OTSelector.Reconstruction.OriginalStageResidualDensityOrientedRetentionGeometry
import OTSelector.Reconstruction.OriginalStageResidualDensityWindowPorts

/-! Exact original retained/port conservation in the same chosen physical cube. -/
open Set Function Filter MeasureTheory Module Manifold
open scoped ENNReal ContDiff Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OTSelector.Reconstruction
open OTSelector.Geometry ContinuousFinslerNorm OTSelector.Probability

/-- The literal centered physical cube in the selected orientation is compact. -/
theorem isCompact_originalStagePhysicalCube {q : ℕ}
    (b : OrthonormalBasis (Fin q) ℝ (EuclideanSpace ℝ (Fin q))) (L : ℝ) :
    IsCompact (originalCenteredPhysicalCubeRegion b L) :=
  isCompact_Icc.image (orthonormalPhysicalCubeMap b).continuous

/-- Increasing physical side length includes the smaller cube in the same actual frame. -/
theorem originalCenteredPhysicalCubeRegion_mono {q : ℕ}
    (b : OrthonormalBasis (Fin q) ℝ (EuclideanSpace ℝ (Fin q))) {L₁ L₂ : ℝ} (hL : L₁ ≤ L₂) :
    originalCenteredPhysicalCubeRegion b L₁ ⊆ originalCenteredPhysicalCubeRegion b L₂ := by
  intro x hx
  rw [mem_originalCenteredPhysicalCubeRegion_iff] at hx ⊢
  constructor <;> intro i
  · have h := hx.1 i
    dsimp [haarRootCube] at h ⊢
    linarith
  · have h := hx.2 i
    dsimp [haarRootCube] at h ⊢
    linarith

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {S : CalibratedLevelSeedPatch F u} {w : S.covector.ker} {μ ν : Measure ℝ}
namespace OriginalSeedConditionalMoments
variable (D : OriginalSeedConditionalMoments S w μ ν)
include D

/-- The original two colored window measures equal the same actual retained marginals plus
true ports in the chosen orientation. Endpoint inclusion is derived from the original paths. -/
theorem ae_originalOriented_windows_eq_retained_add_ports
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {kin : ℝ → ℝ → (Fin (finrank ℝ S.covector.ker) → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (Q : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν kin g)
    (b : OrthonormalBasis (Fin (finrank ℝ S.covector.ker)) ℝ
      (EuclideanSpace ℝ (Fin (finrank ℝ S.covector.ker))))
    {R ell : ℝ} (hell : 0 ≤ ell) (hR : 2 * (originalStageFrameCollarFactor b * ell) ≤ R) :
    ∀ᵐ scene ∂(Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))),
      let A := originalOrientedPathLengthRetained S w b R ell
      let K := originalCenteredPhysicalCubeRegion b (2 * R)
      (legalInputColorMeasure _ scene.2 0).restrict {p | p.1 ∈ K} =
        (originalStageRestrictedPathPlan A scene : Measure (LegalMarkedPhysicalEdge _)).fst +
        (originalStageWindowSourcePortPlan A K scene : Measure (LegalMarkedPhysicalEdge _)).fst ∧
      (legalInputColorMeasure _ scene.2 1).restrict {p | p.1 ∈ K} =
        (originalStageRestrictedPathPlan A scene : Measure (LegalMarkedPhysicalEdge _)).snd +
        (originalStageWindowTargetPortPlan A K scene : Measure (LegalMarkedPhysicalEdge _)).snd := by
  filter_upwards [Q.full_matching, D.ae_ae_original_pairKernel_interior_forward Q]
    with scene hfull hclock
  dsimp only
  have hedge : ∀ᵐ e ∂(scene.1.1 : Measure (LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker))),
      e.1.2 - (S.level : ℝ) ∈ Ioo D.lo D.hi ∧ e.2.2 - (S.level : ℝ) ∈ Ioo D.lo D.hi ∧ e.1.2 < e.2.2 := by
    rw [physicalScenePairKernel_apply] at hclock
    exact ae_of_ae_map measurable_physicalPairAnchor.aemeasurable hclock
  apply hfull.originalStage_window_eq_restricted_add_ports
    (measurableSet_originalOrientedPathLengthRetained S hF hw b R ell)
    (isCompact_originalStagePhysicalCube b (2 * R)).measurableSet
  · filter_upwards [hedge] with e he hret
    have hp := D.originalOrientedPathLengthRetained_path_mem_innerCube hF hw b hell hR hret
      he.1 he.2.1 (left_mem_Icc.mpr he.2.2.le)
    apply originalCenteredPhysicalCubeRegion_mono b (show
      2 * (R - originalStageFrameCollarFactor b * ell) ≤ 2 * R by
        have := mul_nonneg (le_trans zero_le_one (one_le_originalStageFrameCollarFactor b)) hell
        linarith)
    have hsource := originalSeedCompletePath_source S w e.1.1 (physicalPairAnchor e).2
    change originalSeedCompletePath S w e.1.1 (physicalPairAnchor e).2 e.1.2 = e.1.1 at hsource
    change originalSeedCompletePath S w e.1.1 (physicalPairAnchor e).2 e.1.2 ∈ _ at hp
    rwa [hsource] at hp
  · filter_upwards [hedge] with e he hret
    have hp := D.originalOrientedPathLengthRetained_target_mem_innerCube hF hw b hell hR hret
      he.1 he.2.1 he.2.2
    apply originalCenteredPhysicalCubeRegion_mono b (show
      2 * (R - originalStageFrameCollarFactor b * ell) ≤ 2 * R by
        have := mul_nonneg (le_trans zero_le_one (one_le_originalStageFrameCollarFactor b)) hell
        linarith)
    have heq : e.1.1 + (e.2.1 - e.1.1) = e.2.1 := by abel
    simpa only [physicalPairAnchor, heq] using hp

end OriginalSeedConditionalMoments
end OTSelector.Reconstruction
