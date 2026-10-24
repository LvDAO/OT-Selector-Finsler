import OTSelector.Reconstruction.OriginalReserveOrientedDilatedWindowJoining

/-! Actual reserve intensity determines the literal Poisson count in the same original physical cube. -/
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
/-- The canonical original reserve dilation internally gives Poisson count rate theta
times physical volume while preserving the same original indices, marks and frame. -/
theorem exists_originalReserve_intensityOrientedWindow_joining
    {kin : ℝ → ℝ → (Fin (finrank ℝ S.covector.ker) → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (N : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν kin g)
    (b : OrthonormalBasis (Fin (finrank ℝ S.covector.ker)) ℝ
      (EuclideanSpace ℝ (Fin (finrank ℝ S.covector.ker))))
    (hq : 0 < finrank ℝ S.covector.ker) {θ R : ℝ} (hθ : 0 < θ) (hR : 0 < R) :
    letI : IsProbabilityMeasure μ := D.support.source.probability
    letI : IsProbabilityMeasure ν := D.support.target.probability
    ∃ J : ProbabilityMeasure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker) ×
        TwoMarkedCloudSpace (finrank ℝ S.covector.ker) ℝ ℝ),
      (J : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker) ×
        TwoMarkedCloudSpace (finrank ℝ S.covector.ker) ℝ ℝ)).map Prod.fst =
          (N.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))) ∧
      (J : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker) ×
        TwoMarkedCloudSpace (finrank ℝ S.covector.ker) ℝ ℝ)).map Prod.snd =
          twoMarkedCloudLaw (finrank ℝ S.covector.ker) ℝ ℝ μ ν
            (Real.toNNReal θ * (volume (originalCenteredPhysicalCubeRegion b (2 * R))).toNNReal) ∧
      ∀ᵐ p ∂(J : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker) ×
        TwoMarkedCloudSpace (finrank ℝ S.covector.ker) ℝ ℝ)),
        ((legalMarkedInputSceneDilation _ (legalIntensityDilation (finrank ℝ S.covector.ker) θ)
          (legalIntensityDilation_pos (finrank ℝ S.covector.ker) hθ).ne' p.1).2 :
          Measure (LegalColoredInputPoint (finrank ℝ S.covector.ker))).restrict
          ((Prod.fst ∘ Prod.fst) ⁻¹' originalCenteredPhysicalCubeRegion b (2 * R)) =
          legalInputTwoBlockMeasure _ (originalMappedReserveCloudArrays _
            (originalOrientedRawCubePhysicalMap b R) p.2) := by
  let : IsProbabilityMeasure μ := D.support.source.probability
  let : IsProbabilityMeasure ν := D.support.target.probability
  obtain ⟨J, hleft, hright, heq⟩ := D.exists_originalReserve_orientedDilatedWindow_joining N b
    (legalIntensityDilation_pos (finrank ℝ S.covector.ker) hθ) hR
  rw [originalOrientedReserveIntensity_count_rate hq b hθ hR.le] at hright
  exact ⟨J, hleft, hright, heq⟩

end OriginalSeedConditionalMoments
end OTSelector.Reconstruction
