import OTSelector.Reconstruction.OriginalReserveUnitInputFullArrays
import OTSelector.Reconstruction.OriginalReserveUnitInputCountLaw

/-! A proved experiment object retains the actual unit input and all original iid array marginals. -/
open Set Function MeasureTheory ProbabilityTheory Filter Topology Module Manifold
open scoped ENNReal NNReal BigOperators Classical ContDiff
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability OTSelector.Geometry ContinuousFinslerNorm
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

/-- A full unit-input experiment keeps the original main/reserve pair, the
literal theta-reserve sampler, and literal full arrays in one probability law.
Only the main/sampler marginal is used for iid conditioning. -/
structure OriginalReserveFullUnitInputExperiment {q : ℕ} {α β : Measure ℝ}
    [IsProbabilityMeasure α] [IsProbabilityMeasure β]
    {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (Main Reserve : LegalWeightedStationaryPoissonMatching q α β kin g)
    (b : OrthonormalBasis (Fin q) ℝ (EuclideanSpace ℝ (Fin q)))
    (θ : ℝ) (hθ : 0 < θ) (hθ1 : θ < 1) (R : ℝ) where
  baseLaw : ProbabilityMeasure (OriginalReserveUnitExperimentSpace q)
  fullLaw : ProbabilityMeasure (OriginalReserveUnitExperimentSpace q × TwoMarkedCloudSpace q ℝ ℝ)
  fullLaw_fst : (fullLaw : Measure (OriginalReserveUnitExperimentSpace q × TwoMarkedCloudSpace q ℝ ℝ)).map
    Prod.fst = (baseLaw : Measure (OriginalReserveUnitExperimentSpace q))
  baseLaw_original_pair : (baseLaw : Measure (OriginalReserveUnitExperimentSpace q)).map
    (fun p ↦ (p.1, p.2.1)) = (Main.law : Measure (LegalMarkedOptimalInputScene q)).prod
      (Reserve.law : Measure (LegalMarkedOptimalInputScene q))
  baseLaw_unit_input : (baseLaw : Measure (OriginalReserveUnitExperimentSpace q)).map
    (originalReserveUnitInputReadout q θ hθ hθ1) =
      (legalOriginalIntensityReserveLaw Main Reserve θ hθ hθ1 : Measure (LegalMarkedOptimalInputScene q))
  baseLaw_main_sampler : (baseLaw : Measure (OriginalReserveUnitExperimentSpace q)).map
    (originalReserveMainSamplerReadout q θ hθ1) =
      (legalMarkedInputDilationLaw q (legalIntensityDilation q (1 - θ))
        (legalIntensityDilation_pos q (sub_pos.mpr hθ1)).ne' Main.law :
          Measure (LegalMarkedOptimalInputScene q)).prod
      (twoMarkedCloudLaw q ℝ ℝ α β
        (Real.toNNReal θ * (volume (originalCenteredPhysicalCubeRegion b (2 * R))).toNNReal))
  fullLaw_snd : (fullLaw : Measure (OriginalReserveUnitExperimentSpace q × TwoMarkedCloudSpace q ℝ ℝ)).map
    Prod.snd = twoMarkedCloudLaw q ℝ ℝ α β
      (volume (originalCenteredPhysicalCubeRegion b (2 * R))).toNNReal
  ae_base_inputs : ∀ᵐ p ∂(baseLaw : Measure (OriginalReserveUnitExperimentSpace q)),
    ((legalMarkedInputSceneDilation q (legalIntensityDilation q θ)
      (legalIntensityDilation_pos q hθ).ne' p.2.1).2 : Measure (LegalColoredInputPoint q)).restrict
      ((Prod.fst ∘ Prod.fst) ⁻¹' originalCenteredPhysicalCubeRegion b (2 * R)) =
      legalInputTwoBlockMeasure q (originalMappedReserveCloudArrays q
        (originalOrientedRawCubePhysicalMap b R) p.2.2) ∧
    ((originalReserveUnitInputReadout q θ hθ hθ1 p).2 : Measure (LegalColoredInputPoint q)).restrict
      ((Prod.fst ∘ Prod.fst) ⁻¹' originalCenteredPhysicalCubeRegion b (2 * R)) =
      (((originalReserveMainSamplerReadout q θ hθ1 p).1).2 : Measure (LegalColoredInputPoint q)).restrict
        ((Prod.fst ∘ Prod.fst) ⁻¹' originalCenteredPhysicalCubeRegion b (2 * R)) +
      legalInputTwoBlockMeasure q (originalMappedReserveCloudArrays q
        (originalOrientedRawCubePhysicalMap b R) p.2.2)
  ae_full_input : ∀ᵐ p ∂(fullLaw : Measure (OriginalReserveUnitExperimentSpace q × TwoMarkedCloudSpace q ℝ ℝ)),
    ((originalReserveUnitInputReadout q θ hθ hθ1 p.1).2 : Measure (LegalColoredInputPoint q)).restrict
      ((Prod.fst ∘ Prod.fst) ⁻¹' originalCenteredPhysicalCubeRegion b (2 * R)) =
      legalInputTwoBlockMeasure q (originalMappedReserveCloudArrays q
        (originalOrientedRawCubePhysicalMap b R) p.2)

namespace OriginalReserveFullUnitInputExperiment
variable {q : ℕ} {α β : Measure ℝ} [IsProbabilityMeasure α] [IsProbabilityMeasure β]
  {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
  {Main Reserve : LegalWeightedStationaryPoissonMatching q α β kin g}
  {b : OrthonormalBasis (Fin q) ℝ (EuclideanSpace ℝ (Fin q))}
  {θ R : ℝ} {hθ : 0 < θ} {hθ1 : θ < 1}
  (X : OriginalReserveFullUnitInputExperiment Main Reserve b θ hθ hθ1 R)

/-- The full-array lift preserves the same iid main/reserve sampler marginal. -/
theorem fullLaw_main_sampler :
    (X.fullLaw : Measure (OriginalReserveUnitExperimentSpace q × TwoMarkedCloudSpace q ℝ ℝ)).map
      (fun p ↦ originalReserveMainSamplerReadout q θ hθ1 p.1) =
      (legalMarkedInputDilationLaw q (legalIntensityDilation q (1 - θ))
        (legalIntensityDilation_pos q (sub_pos.mpr hθ1)).ne' Main.law :
          Measure (LegalMarkedOptimalInputScene q)).prod
      (twoMarkedCloudLaw q ℝ ℝ α β
        (Real.toNNReal θ * (volume (originalCenteredPhysicalCubeRegion b (2 * R))).toNNReal)) := by
  change (X.fullLaw : Measure (OriginalReserveUnitExperimentSpace q × TwoMarkedCloudSpace q ℝ ℝ)).map
    ((originalReserveMainSamplerReadout q θ hθ1) ∘ Prod.fst) = _
  rw [← Measure.map_map (measurable_originalReserveMainSamplerReadout q θ hθ1) measurable_fst,
    X.fullLaw_fst, X.baseLaw_main_sampler]

/-- Both actual total-count identities hold in the full experiment. -/
theorem ae_global_counts :
    ∀ᵐ p ∂(X.fullLaw : Measure (OriginalReserveUnitExperimentSpace q × TwoMarkedCloudSpace q ℝ ℝ)),
      originalScreeningActualCount (originalCenteredPhysicalCubeRegion b (2 * R))
        (originalReserveUnitInputReadout q θ hθ hθ1 p.1) = (p.2.1.1 : ℝ) + (p.2.2.1 : ℝ) ∧
      originalScreeningActualCount (originalCenteredPhysicalCubeRegion b (2 * R))
        (originalReserveUnitInputReadout q θ hθ hθ1 p.1) =
          originalScreeningActualCount (originalCenteredPhysicalCubeRegion b (2 * R))
            (originalReserveMainSamplerReadout q θ hθ1 p.1).1 +
              ((p.1.2.2.1.1 : ℝ) + (p.1.2.2.2.1 : ℝ)) :=
  ae_originalReserveUnitInput_lifted_fullCounts θ hθ hθ1 b R X.baseLaw X.fullLaw
    X.fullLaw_fst (X.ae_base_inputs.mono fun _ hp ↦ hp.2) X.ae_full_input

/-- The global count law is proved for this same full experiment. -/
theorem global_count_law :
    HasLaw (fun p : OriginalReserveUnitExperimentSpace q × TwoMarkedCloudSpace q ℝ ℝ ↦
      originalScreeningActualCount (originalCenteredPhysicalCubeRegion b (2 * R))
        (originalReserveUnitInputReadout q θ hθ hθ1 p.1))
      (((poissonMeasure (volume (originalCenteredPhysicalCubeRegion b (2 * R))).toNNReal).prod
        (poissonMeasure (volume (originalCenteredPhysicalCubeRegion b (2 * R))).toNNReal)).map
          (fun counts ↦ (counts.1 : ℝ) + (counts.2 : ℝ)))
      (X.fullLaw : Measure (OriginalReserveUnitExperimentSpace q × TwoMarkedCloudSpace q ℝ ℝ)) :=
  hasLaw_originalReserveUnitInput_globalCount_of_fullArrays θ hθ hθ1 b R X.fullLaw
    X.fullLaw_snd X.ae_full_input
end OriginalReserveFullUnitInputExperiment

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
namespace OriginalSeedConditionalMoments
variable {S : CalibratedLevelSeedPatch F u} {w : S.covector.ker} {μ ν : Measure ℝ}
  (D : OriginalSeedConditionalMoments S w μ ν)
include D

omit [BorelSpace E] in
/-- Construct the full unit-intensity experiment from the actual original
matching and reserve, preserving their original product law and all prior
correlations. No joining, full-array identity, count law or floor is an input. -/
theorem exists_originalReserve_fullUnitInputExperiment
    {kin : ℝ → ℝ → (Fin (finrank ℝ S.covector.ker) → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (Main Reserve : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν kin g)
    (b : OrthonormalBasis (Fin (finrank ℝ S.covector.ker)) ℝ
      (EuclideanSpace ℝ (Fin (finrank ℝ S.covector.ker))))
    (hq : 0 < finrank ℝ S.covector.ker) {θ R : ℝ}
    (hθ : 0 < θ) (hθ1 : θ < 1) (hR : 0 < R) :
    letI : IsProbabilityMeasure μ := D.support.source.probability
    letI : IsProbabilityMeasure ν := D.support.target.probability
    Nonempty (OriginalReserveFullUnitInputExperiment Main Reserve b θ hθ hθ1 R) := by
  let : IsProbabilityMeasure μ := D.support.source.probability
  let : IsProbabilityMeasure ν := D.support.target.probability
  obtain ⟨L, hpair, hunit, hmain, hinputs⟩ :=
    D.exists_originalReserve_unitInput_orientedExperiment Main Reserve b hq hθ hθ1 hR
  obtain ⟨J, hleft, hright, hfull⟩ :=
    D.exists_originalReserve_unitInput_fullArrays_lift Main Reserve b hq hθ hθ1 hR L hunit
  exact ⟨{
    baseLaw := L
    fullLaw := J
    fullLaw_fst := hleft
    baseLaw_original_pair := hpair
    baseLaw_unit_input := hunit
    baseLaw_main_sampler := hmain
    fullLaw_snd := hright
    ae_base_inputs := hinputs
    ae_full_input := hfull }⟩

end OriginalSeedConditionalMoments
end OTSelector.Reconstruction
