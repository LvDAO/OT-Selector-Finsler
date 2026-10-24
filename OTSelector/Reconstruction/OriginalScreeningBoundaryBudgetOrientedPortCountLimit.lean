import OTSelector.Reconstruction.OriginalScreeningBoundaryBudgetOrientedPortCountBounds
import OTSelector.Reconstruction.OriginalPortDensityLimit

/-! Both literal port plans have vanishing expected count per the same oriented cube volume. -/
open Set Function Filter MeasureTheory Module Manifold
open scoped ENNReal Topology ContDiff
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OTSelector.Reconstruction
open OTSelector.Geometry ContinuousFinslerNorm OTSelector.Probability
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {S : CalibratedLevelSeedPatch F u} {w : S.covector.ker} {μ ν : Measure ℝ}

/-- The actual same-frame source ports have negligible expected count per the physical
cube volume for every diverging sublinear original path cutoff. -/
theorem tendsto_originalOrientedStage_sourcePort_count_density_zero
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {kin : ℝ → ℝ → (Fin (finrank ℝ S.covector.ker) → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (Q : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν kin g)
    (b : OrthonormalBasis (Fin (finrank ℝ S.covector.ker)) ℝ
      (EuclideanSpace ℝ (Fin (finrank ℝ S.covector.ker))))
    {ell : ℝ → ℝ} (hell : ∀ᶠ R in atTop, 0 ≤ ell R)
    (hlarge : Tendsto ell atTop atTop) (hsmall : Tendsto (fun R ↦ ell R/R) atTop (𝓝 0)) :
    Tendsto (fun R : ℝ ↦
      (∫⁻ scene, (originalStageWindowSourcePortPlan (originalOrientedPathLengthRetained S w b R (ell R))
        (originalCenteredPhysicalCubeRegion b (2*R)) scene :
          Measure (LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker))) univ
        ∂(Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker)))).toReal /
      volume.real (originalCenteredPhysicalCubeRegion b (2*R))) atTop (𝓝 0) := by
  let : IsProbabilityMeasure (legalMarkedJointPalm (finrank ℝ S.covector.ker) Q.law) := Q.palm_probability
  have hC : 0 ≤ originalStageFrameCollarFactor b := by linarith [one_le_originalStageFrameCollarFactor b]
  have hscale : Tendsto (fun R ↦ (originalStageFrameCollarFactor b*ell R)/R) atTop (𝓝 0) := by
    simpa only [mul_div_assoc, mul_zero] using hsmall.const_mul (originalStageFrameCollarFactor b)
  simp only [measureReal_def, volume_originalOrientedTraffic_cube]
  apply tendsto_normalized_haarCube_count_of_collar_tail (Fin (finrank ℝ S.covector.ker))
    (ell := fun R ↦ originalStageFrameCollarFactor b*ell R) (k := 2)
    (tail := fun R ↦ (legalMarkedJointPalm (finrank ℝ S.covector.ker) Q.law)
      {m | ell R < originalSeedPairPathLength S w m}) (by norm_num)
    (hell.mono fun R hR ↦ mul_nonneg hC hR) hscale (fun _ ↦ measure_ne_top _ _)
    ((tendsto_original_truePalm_pathLength_tail_real hF hw Q).comp hlarge)
  apply Eventually.of_forall
  intro R
  simpa only [volume_originalOrientedTraffic_collar, volume_originalOrientedTraffic_cube] using
    lintegral_originalOrientedStageSourcePorts_le_collar_and_pathTail hF hw Q b R (ell R)

namespace OriginalSeedConditionalMoments
variable (D : OriginalSeedConditionalMoments S w μ ν)
include D

/-- The literal target ports of that same retained set have negligible expected count,
using the actual original target marginal and unchanged true-Palm path tail. -/
theorem tendsto_originalOrientedStage_targetPort_count_density_zero
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {kin : ℝ → ℝ → (Fin (finrank ℝ S.covector.ker) → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (Q : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν kin g)
    (b : OrthonormalBasis (Fin (finrank ℝ S.covector.ker)) ℝ
      (EuclideanSpace ℝ (Fin (finrank ℝ S.covector.ker))))
    {ell : ℝ → ℝ} (hell : ∀ᶠ R in atTop, 0 ≤ ell R)
    (hlarge : Tendsto ell atTop atTop) (hsmall : Tendsto (fun R ↦ ell R/R) atTop (𝓝 0)) :
    Tendsto (fun R : ℝ ↦
      (∫⁻ scene, (originalStageWindowTargetPortPlan (originalOrientedPathLengthRetained S w b R (ell R))
        (originalCenteredPhysicalCubeRegion b (2*R)) scene :
          Measure (LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker))) univ
        ∂(Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker)))).toReal /
      volume.real (originalCenteredPhysicalCubeRegion b (2*R))) atTop (𝓝 0) := by
  let : IsProbabilityMeasure (legalMarkedJointPalm (finrank ℝ S.covector.ker) Q.law) := Q.palm_probability
  have hC : 0 ≤ originalStageFrameCollarFactor b := by linarith [one_le_originalStageFrameCollarFactor b]
  have hscale : Tendsto (fun R ↦ (originalStageFrameCollarFactor b*ell R)/R) atTop (𝓝 0) := by
    simpa only [mul_div_assoc, mul_zero] using hsmall.const_mul (originalStageFrameCollarFactor b)
  simp only [measureReal_def, volume_originalOrientedTraffic_cube]
  apply tendsto_normalized_haarCube_count_of_collar_tail (Fin (finrank ℝ S.covector.ker))
    (ell := fun R ↦ originalStageFrameCollarFactor b*ell R) (k := 3)
    (tail := fun R ↦ (legalMarkedJointPalm (finrank ℝ S.covector.ker) Q.law)
      {m | ell R < originalSeedPairPathLength S w m}) (by norm_num)
    (hell.mono fun R hR ↦ mul_nonneg hC hR) hscale (fun _ ↦ measure_ne_top _ _)
    ((tendsto_original_truePalm_pathLength_tail_real hF hw Q).comp hlarge)
  filter_upwards [hell, eventually_collar_mul_le_radius (k := (3:ℝ)) hscale] with R hellR hR
  simpa only [volume_originalOrientedTraffic_collar, volume_originalOrientedTraffic_cube] using
    D.lintegral_originalOrientedStageTargetPorts_le_collar_and_pathTail hF hw Q b hellR hR

end OriginalSeedConditionalMoments
end OTSelector.Reconstruction
