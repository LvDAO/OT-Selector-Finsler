import OTSelector.Reconstruction.OriginalReserveIntensityOrientedWindowJoining
import OTSelector.Reconstruction.OriginalReserveUnitInputReadouts

/-! One original experiment carries the actual unit input, retained main and literal independent reserve arrays. -/
open Set Function MeasureTheory ProbabilityTheory Filter Topology Module Manifold
open scoped ENNReal NNReal BigOperators Classical ContDiff
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability OTSelector.Geometry ContinuousFinslerNorm
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
local instance originalReserveUnitExperimentInputPolish (q : ℕ) : PolishSpace
    (LocalFiniteMeasure (LegalColoredInputPoint q)) := LocalFiniteMeasure.instPolishSpace
local instance originalReserveUnitExperimentPlanPolish (q : ℕ) : PolishSpace
    (LocalFiniteMeasure (LegalMarkedPhysicalEdge q)) := LocalFiniteMeasure.instPolishSpace

/-- Original main scene, whole original reserve identity witness, and its original cube sampler. -/
abbrev OriginalReserveUnitExperimentSpace (q : ℕ) := LegalMarkedOptimalInputScene q ×
  (LegalMarkedOptimalInputScene q × TwoMarkedCloudSpace q ℝ ℝ)

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
namespace OriginalSeedConditionalMoments
variable {S : CalibratedLevelSeedPatch F u} {w : S.covector.ker} {μ ν : Measure ℝ}
  (D : OriginalSeedConditionalMoments S w μ ν)
include D

omit [BorelSpace E] in
/-- The complete original independent pair, actual complementary-dilation unit
input, literal theta-volume iid reserve sampler and full finite-window input
identity all hold in one joining. No law is assigned to adaptively selected ports. -/
theorem exists_originalReserve_unitInput_orientedExperiment
    {kin : ℝ → ℝ → (Fin (finrank ℝ S.covector.ker) → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (M₀ N : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν kin g)
    (b : OrthonormalBasis (Fin (finrank ℝ S.covector.ker)) ℝ
      (EuclideanSpace ℝ (Fin (finrank ℝ S.covector.ker))))
    (hq : 0 < finrank ℝ S.covector.ker) {θ R : ℝ}
    (hθ : 0 < θ) (hθ1 : θ < 1) (hR : 0 < R) :
    letI : IsProbabilityMeasure μ := D.support.source.probability
    letI : IsProbabilityMeasure ν := D.support.target.probability
    ∃ L : ProbabilityMeasure (OriginalReserveUnitExperimentSpace (finrank ℝ S.covector.ker)),
      (L : Measure (OriginalReserveUnitExperimentSpace (finrank ℝ S.covector.ker))).map (fun p ↦ (p.1, p.2.1)) =
        (M₀.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))).prod (N.law : Measure _) ∧
      (L : Measure (OriginalReserveUnitExperimentSpace (finrank ℝ S.covector.ker))).map
        (originalReserveUnitInputReadout (finrank ℝ S.covector.ker) θ hθ hθ1) =
          (legalOriginalIntensityReserveLaw M₀ N θ hθ hθ1 : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))) ∧
      (L : Measure (OriginalReserveUnitExperimentSpace (finrank ℝ S.covector.ker))).map
        (originalReserveMainSamplerReadout (finrank ℝ S.covector.ker) θ hθ1) =
          (legalMarkedInputDilationLaw (finrank ℝ S.covector.ker) (legalIntensityDilation (finrank ℝ S.covector.ker) (1 - θ))
            (legalIntensityDilation_pos (finrank ℝ S.covector.ker) (sub_pos.mpr hθ1)).ne' M₀.law :
              Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))).prod
            (twoMarkedCloudLaw (finrank ℝ S.covector.ker) ℝ ℝ μ ν
              (Real.toNNReal θ * (volume (originalCenteredPhysicalCubeRegion b (2 * R))).toNNReal)) ∧
      ∀ᵐ p ∂(L : Measure (OriginalReserveUnitExperimentSpace (finrank ℝ S.covector.ker))),
        ((legalMarkedInputSceneDilation (finrank ℝ S.covector.ker) (legalIntensityDilation (finrank ℝ S.covector.ker) θ)
          (legalIntensityDilation_pos (finrank ℝ S.covector.ker) hθ).ne' p.2.1).2 :
            Measure (LegalColoredInputPoint (finrank ℝ S.covector.ker))).restrict
          ((Prod.fst ∘ Prod.fst) ⁻¹' originalCenteredPhysicalCubeRegion b (2 * R)) =
          legalInputTwoBlockMeasure _ (originalMappedReserveCloudArrays _
            (originalOrientedRawCubePhysicalMap b R) p.2.2) ∧
        ((originalReserveUnitInputReadout (finrank ℝ S.covector.ker) θ hθ hθ1 p).2 :
          Measure (LegalColoredInputPoint (finrank ℝ S.covector.ker))).restrict
          ((Prod.fst ∘ Prod.fst) ⁻¹' originalCenteredPhysicalCubeRegion b (2 * R)) =
          (((originalReserveMainSamplerReadout (finrank ℝ S.covector.ker) θ hθ1 p).1).2 :
            Measure (LegalColoredInputPoint (finrank ℝ S.covector.ker))).restrict
            ((Prod.fst ∘ Prod.fst) ⁻¹' originalCenteredPhysicalCubeRegion b (2 * R)) +
          legalInputTwoBlockMeasure _ (originalMappedReserveCloudArrays _
            (originalOrientedRawCubePhysicalMap b R) p.2.2) := by
  let : IsProbabilityMeasure μ := D.support.source.probability
  let : IsProbabilityMeasure ν := D.support.target.probability
  obtain ⟨J, hleft, hright, heq⟩ :=
    D.exists_originalReserve_intensityOrientedWindow_joining N b hq hθ hR
  let L : ProbabilityMeasure (OriginalReserveUnitExperimentSpace (finrank ℝ S.covector.ker)) :=
    ⟨(M₀.law : Measure _).prod (J : Measure _), inferInstance⟩
  have hpair : (L : Measure (OriginalReserveUnitExperimentSpace (finrank ℝ S.covector.ker))).map
      (fun p ↦ (p.1, p.2.1)) =
      (M₀.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))).prod (N.law : Measure _) := by
    change ((M₀.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))).prod
      (J : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker) × TwoMarkedCloudSpace (finrank ℝ S.covector.ker) ℝ ℝ))).map
        (Prod.map id Prod.fst) = _
    rw [← Measure.map_prod_map _ _ measurable_id measurable_fst, Measure.map_id, hleft]
  refine ⟨L, hpair, ?_, ?_, ?_⟩
  · change (L : Measure (OriginalReserveUnitExperimentSpace (finrank ℝ S.covector.ker))).map
      ((legalOriginalDilatedReserveScene _ (legalIntensityDilation (finrank ℝ S.covector.ker) (1 - θ))
        (legalIntensityDilation (finrank ℝ S.covector.ker) θ) (legalIntensityDilation_pos (finrank ℝ S.covector.ker) (sub_pos.mpr hθ1)).ne'
          (legalIntensityDilation_pos (finrank ℝ S.covector.ker) hθ).ne') ∘ (fun p ↦ (p.1, p.2.1))) = _
    rw [← Measure.map_map (measurable_legalOriginalDilatedReserveScene _ _ _ _ _)
      (measurable_fst.prodMk measurable_snd.fst), hpair,
      map_original_pair_eq_dilatedReserveLaw]
    rfl
  · change ((M₀.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))).prod
      (J : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker) × TwoMarkedCloudSpace (finrank ℝ S.covector.ker) ℝ ℝ))).map
        (Prod.map (legalMarkedInputSceneDilation (finrank ℝ S.covector.ker) (legalIntensityDilation (finrank ℝ S.covector.ker) (1 - θ))
          (legalIntensityDilation_pos (finrank ℝ S.covector.ker) (sub_pos.mpr hθ1)).ne') Prod.snd) = _
    rw [← Measure.map_prod_map _ _
      (continuous_legalMarkedInputSceneDilation (finrank ℝ S.covector.ker) _ _).measurable measurable_snd, hright]
    rfl
  · have h : ∀ᵐ p ∂(L : Measure (OriginalReserveUnitExperimentSpace (finrank ℝ S.covector.ker))),
        ((legalMarkedInputSceneDilation (finrank ℝ S.covector.ker) (legalIntensityDilation (finrank ℝ S.covector.ker) θ)
          (legalIntensityDilation_pos (finrank ℝ S.covector.ker) hθ).ne' p.2.1).2 :
            Measure (LegalColoredInputPoint (finrank ℝ S.covector.ker))).restrict
          ((Prod.fst ∘ Prod.fst) ⁻¹' originalCenteredPhysicalCubeRegion b (2 * R)) =
          legalInputTwoBlockMeasure _ (originalMappedReserveCloudArrays _
            (originalOrientedRawCubePhysicalMap b R) p.2.2) := ae_snd_of_ae heq
    filter_upwards [h] with p hp
    refine ⟨hp, ?_⟩
    rw [originalReserveUnitInputReadout_window_decomposition, hp]

end OriginalSeedConditionalMoments
end OTSelector.Reconstruction
