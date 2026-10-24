import OTSelector.Reconstruction.OriginalReserveMappedWindowJoining
import OTSelector.Reconstruction.OriginalIIDCubePopulationCouplingOrientedCubeVolume
import OTSelector.Reconstruction.OriginalStageResidualDensityOrientedWindowPorts
import OTSelector.Reconstruction.FinslerOriginalConditionalMoments

/-! The actual same-frame reserve experiment and its complete original input share one joining. -/
open Set Function MeasureTheory ProbabilityTheory Filter Topology Module Manifold
open scoped ENNReal NNReal BigOperators Classical ContDiff
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability OTSelector.Geometry ContinuousFinslerNorm
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
namespace OriginalSeedConditionalMoments
variable {S : CalibratedLevelSeedPatch F u} {w : S.covector.ker} {μ ν : Measure ℝ}
  (D : OriginalSeedConditionalMoments S w μ ν)
include D

omit [BorelSpace E] in
/-- The same chosen physical frame, original conditional clocks and unchanged
cube sampler produce the actual reserve-only whole-input joining. Clock support
and the spatial normalization are derived internally from their genuine producers. -/
theorem exists_originalReserve_orientedWindow_joining
    {kin : ℝ → ℝ → (Fin (finrank ℝ S.covector.ker) → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (N : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν kin g)
    (b : OrthonormalBasis (Fin (finrank ℝ S.covector.ker)) ℝ
      (EuclideanSpace ℝ (Fin (finrank ℝ S.covector.ker))))
    {R : ℝ} (hR : 0 < R) :
    letI : IsProbabilityMeasure μ := D.support.source.probability
    letI : IsProbabilityMeasure ν := D.support.target.probability
    ∃ J : ProbabilityMeasure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker) ×
        TwoMarkedCloudSpace (finrank ℝ S.covector.ker) ℝ ℝ),
      (J : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker) ×
        TwoMarkedCloudSpace (finrank ℝ S.covector.ker) ℝ ℝ)).map Prod.fst = (N.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))) ∧
      (J : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker) ×
        TwoMarkedCloudSpace (finrank ℝ S.covector.ker) ℝ ℝ)).map Prod.snd = twoMarkedCloudLaw (finrank ℝ S.covector.ker) ℝ ℝ μ ν
        (volume (originalCenteredPhysicalCubeRegion b (2 * R))).toNNReal ∧
      ∀ᵐ p ∂(J : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker) ×
        TwoMarkedCloudSpace (finrank ℝ S.covector.ker) ℝ ℝ)),
        (p.1.2 : Measure (LegalColoredInputPoint (finrank ℝ S.covector.ker))).restrict
          ((Prod.fst ∘ Prod.fst) ⁻¹' originalCenteredPhysicalCubeRegion b (2 * R)) =
          legalInputTwoBlockMeasure _ (originalMappedReserveCloudArrays _
            (originalOrientedRawCubePhysicalMap b R) p.2) := by
  let : IsProbabilityMeasure μ := D.support.source.probability
  let : IsProbabilityMeasure ν := D.support.target.probability
  let A := Icc (D.lo + (S.level : ℝ)) (D.hi + (S.level : ℝ))
  have hμ : μ.support ⊆ A := by
    intro x hx
    have h := D.support.source.support_bounds x hx
    constructor <;> linarith [h.1, h.2]
  have hν : ν.support ⊆ A := by
    intro x hx
    have h := D.support.target.support_bounds x hx
    constructor <;> linarith [h.1, h.2]
  have hKpos : volume (originalCenteredPhysicalCubeRegion b (2 * R)) ≠ 0 := by
    rw [volume_originalOrientedTraffic_cube b R,
      volume_haarRootCube (Fin (finrank ℝ S.covector.ker)) hR.le, Fintype.card_fin]
    exact (ENNReal.ofReal_pos.mpr (pow_pos (by positivity) _)).ne'
  exact N.exists_originalReserve_fullMappedWindow_joining
    (isCompact_originalStagePhysicalCube b (2 * R)) hKpos
    (measurable_originalOrientedRawCubePhysicalMap b R)
    (map_originalUnitCube_oriented_eq_normalizedFiniteLaw b hR)
    isCompact_Icc hμ hν

end OriginalSeedConditionalMoments
end OTSelector.Reconstruction
