import OTSelector.Reconstruction.OriginalReserveOrientedWindowJoining
import OTSelector.Reconstruction.OriginalReserveMappedWindowMeasures
import OTSelector.Reconstruction.OriginalReserveOrientedWindowIntensity

/-! The same original reserve scene supplies the actual dilated physical-window finite arrays. -/
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
/-- The full original reserve is preserved before dilation. Its literal cube
sampler supplies every actual dilated physical-window atom, with count rate
computed from the true preimage cube rather than assigned to selected endpoints. -/
theorem exists_originalReserve_orientedDilatedWindow_joining
    {kin : ℝ → ℝ → (Fin (finrank ℝ S.covector.ker) → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (N : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν kin g)
    (b : OrthonormalBasis (Fin (finrank ℝ S.covector.ker)) ℝ
      (EuclideanSpace ℝ (Fin (finrank ℝ S.covector.ker))))
    {c R : ℝ} (hc : 0 < c) (hR : 0 < R) :
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
            (volume (originalCenteredPhysicalCubeRegion b (2 * (R / c)))).toNNReal ∧
      ∀ᵐ p ∂(J : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker) ×
        TwoMarkedCloudSpace (finrank ℝ S.covector.ker) ℝ ℝ)),
        ((legalMarkedInputSceneDilation _ c hc.ne' p.1).2 :
          Measure (LegalColoredInputPoint (finrank ℝ S.covector.ker))).restrict
          ((Prod.fst ∘ Prod.fst) ⁻¹' originalCenteredPhysicalCubeRegion b (2 * R)) =
          legalInputTwoBlockMeasure _ (originalMappedReserveCloudArrays _
            (originalOrientedRawCubePhysicalMap b R) p.2) := by
  let : IsProbabilityMeasure μ := D.support.source.probability
  let : IsProbabilityMeasure ν := D.support.target.probability
  obtain ⟨J, hleft, hright, heq⟩ := D.exists_originalReserve_orientedWindow_joining N b (div_pos hR hc)
  refine ⟨J, hleft, hright, ?_⟩
  filter_upwards [heq] with p hp
  change ((p.1.2 : Measure (LegalColoredInputPoint (finrank ℝ S.covector.ker))).map
    (legalColoredInputDilation _ c hc.ne')).restrict
      ((Prod.fst ∘ Prod.fst) ⁻¹' originalCenteredPhysicalCubeRegion b (2 * R)) = _
  rw [originalColoredInput_orientedWindow_dilation b hc R, hp,
    originalMappedReserveCloudArrays_oriented_dilation b hc.ne' R]

end OriginalSeedConditionalMoments
end OTSelector.Reconstruction
