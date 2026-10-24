import OTSelector.Reconstruction.OriginalReserveFullWorkingWholeInputExperiment

/-! A genuine common-original experiment is produced at every positive working radius. -/
open Set Function MeasureTheory ProbabilityTheory Filter Topology Module Manifold
open scoped ENNReal NNReal BigOperators Classical ContDiff
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability OTSelector.Geometry ContinuousFinslerNorm
set_option backward.isDefEq.respectTransparency false
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
namespace OriginalSeedConditionalMoments
variable {S : CalibratedLevelSeedPatch F u} {w : S.covector.ker} {μ ν : Measure ℝ}
  (D : OriginalSeedConditionalMoments S w μ ν)
include D

omit [BorelSpace E] in
/-- The same two original experiments and physical frame produce the complete
working input family at every positive radius. Whole-reserve and FULL identities
remain on each genuine experiment; no finished family is an input hypothesis. -/
theorem exists_originalReserve_fullWorkingWholeInputExperimentFamily
    {kin : ℝ → ℝ → (Fin (finrank ℝ S.covector.ker) → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (Main Reserve : LegalWeightedStationaryPoissonMatching
      (finrank ℝ S.covector.ker) μ ν kin g)
    (b : OrthonormalBasis (Fin (finrank ℝ S.covector.ker)) ℝ
      (EuclideanSpace ℝ (Fin (finrank ℝ S.covector.ker))))
    (hq : 0 < finrank ℝ S.covector.ker) {ρ : ℝ} (hρ : 0 < ρ) :
    letI : IsProbabilityMeasure μ := D.support.source.probability
    letI : IsProbabilityMeasure ν := D.support.target.probability
    ∃ Y : ∀ R : ℝ, 0 < R → OriginalReserveFullWorkingInputExperiment Main Reserve b ρ R,
    ∀ (R : ℝ) (hR : 0 < R),
    ∀ᵐ p ∂((Y R hR).fullLaw : Measure (OriginalReserveUnitExperimentSpace (finrank ℝ S.covector.ker) ×
      TwoMarkedCloudSpace (finrank ℝ S.covector.ker) ℝ ℝ)),
      ((legalMarkedInputSceneDilation (finrank ℝ S.covector.ker)
        (legalIntensityDilation (finrank ℝ S.covector.ker) ρ)
        (legalIntensityDilation_pos (finrank ℝ S.covector.ker) hρ).ne' p.1.2.1).2 :
          Measure (LegalColoredInputPoint (finrank ℝ S.covector.ker))).restrict
        ((Prod.fst ∘ Prod.fst) ⁻¹' originalCenteredPhysicalCubeRegion b (2*R)) =
        legalInputTwoBlockMeasure _ (originalMappedReserveCloudArrays _
          (originalOrientedRawCubePhysicalMap b R) p.1.2.2) ∧
      ((originalReserveMainIntensityInputReadout (finrank ℝ S.covector.ker) ρ hρ p.1).2 :
        Measure (LegalColoredInputPoint (finrank ℝ S.covector.ker))).restrict
        ((Prod.fst ∘ Prod.fst) ⁻¹' originalCenteredPhysicalCubeRegion b (2*R)) =
        legalInputTwoBlockMeasure _ (originalMappedReserveCloudArrays _
          (originalOrientedRawCubePhysicalMap b R) p.2) := by
  let : IsProbabilityMeasure μ := D.support.source.probability
  let : IsProbabilityMeasure ν := D.support.target.probability
  choose Y hY using fun (R : ℝ) (hR : 0 < R) ↦
    D.exists_originalReserve_fullWorkingWholeInputExperiment Main Reserve b hq hρ hR
  exact ⟨Y, hY⟩

end OriginalSeedConditionalMoments
end OTSelector.Reconstruction
