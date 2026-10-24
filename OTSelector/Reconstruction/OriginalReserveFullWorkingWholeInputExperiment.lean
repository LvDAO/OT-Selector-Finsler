import OTSelector.Reconstruction.OriginalReserveFullWorkingInputExperiment
import OTSelector.Reconstruction.OriginalReserveWorkingWholeReserveInput
import OTSelector.Reconstruction.OriginalReserveMainIntensityReadouts

/-! The complete working arrays belong to the same actual globally superposed original inputs. -/
open Set Function MeasureTheory ProbabilityTheory Filter Topology Module Manifold
open scoped ENNReal NNReal BigOperators Classical ContDiff
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability OTSelector.Geometry ContinuousFinslerNorm
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
namespace OriginalReserveFullWorkingInputExperiment
variable {q : ℕ} {α β : Measure ℝ} [IsProbabilityMeasure α] [IsProbabilityMeasure β]
  {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
  {Main Reserve : LegalWeightedStationaryPoissonMatching q α β kin g}
  {b : OrthonormalBasis (Fin q) ℝ (EuclideanSpace ℝ (Fin q))} {ρ R : ℝ}
  (X : OriginalReserveFullWorkingInputExperiment Main Reserve b ρ R)

/-- The actual global main-plus-reserve scene has its literal original
superposition law under this same complete experiment. -/
theorem fullLaw_original_working_input (hρ : 0 < ρ) :
    (X.fullLaw : Measure (OriginalReserveUnitExperimentSpace q × TwoMarkedCloudSpace q ℝ ℝ)).map
      (fun p ↦ originalReserveMainIntensityInputReadout q ρ hρ p.1) =
      (legalMarkedReserveInputLaw q Main.law
        (legalMarkedInputDilationLaw q (legalIntensityDilation q ρ)
          (legalIntensityDilation_pos q hρ).ne' Reserve.law) :
            Measure (LegalMarkedOptimalInputScene q)) := by
  change (X.fullLaw : Measure (OriginalReserveUnitExperimentSpace q ×
    TwoMarkedCloudSpace q ℝ ℝ)).map
      ((originalReserveMainIntensityScene q ρ hρ) ∘ (fun p ↦ (p.1.1, p.1.2.1))) = _
  rw [← Measure.map_map (measurable_originalReserveMainIntensityScene q ρ hρ)
    (measurable_fst.fst.prodMk measurable_fst.snd.fst), X.fullLaw_original_pair,
    map_originalPair_eq_mainIntensityReserveLaw]

end OriginalReserveFullWorkingInputExperiment

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
namespace OriginalSeedConditionalMoments
variable {S : CalibratedLevelSeedPatch F u} {w : S.covector.ker} {μ ν : Measure ℝ}
  (D : OriginalSeedConditionalMoments S w μ ν)
include D

omit [BorelSpace E] in
/-- Construct one genuine complete original working experiment whose actual
whole reserve and actual global superposed input have precisely the same literal
finite reserve and FULL arrays. Every original identity and iid-consumer marginal
is retained; no complete window identity or joining is an input. -/
theorem exists_originalReserve_fullWorkingWholeInputExperiment
    {kin : ℝ → ℝ → (Fin (finrank ℝ S.covector.ker) → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (Main Reserve : LegalWeightedStationaryPoissonMatching
      (finrank ℝ S.covector.ker) μ ν kin g)
    (b : OrthonormalBasis (Fin (finrank ℝ S.covector.ker)) ℝ
      (EuclideanSpace ℝ (Fin (finrank ℝ S.covector.ker))))
    (hq : 0 < finrank ℝ S.covector.ker) {ρ R : ℝ} (hρ : 0 < ρ) (hR : 0 < R) :
    letI : IsProbabilityMeasure μ := D.support.source.probability
    letI : IsProbabilityMeasure ν := D.support.target.probability
    ∃ Y : OriginalReserveFullWorkingInputExperiment Main Reserve b ρ R,
    ∀ᵐ p ∂(Y.fullLaw : Measure (OriginalReserveUnitExperimentSpace (finrank ℝ S.covector.ker) ×
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
  let θ := originalReserveWorkingFraction ρ
  let d := originalReserveWorkingScale (finrank ℝ S.covector.ker) ρ
  have hθ := originalReserveWorkingFraction_bounds hρ
  have hd : 0 < d := legalIntensityDilation_pos _ (sub_pos.mpr hθ.2)
  have hdiv : d*R/d = R := mul_div_cancel_left₀ R hd.ne'
  have hdiv' : d*R / legalIntensityDilation (finrank ℝ S.covector.ker)
      (1-originalReserveWorkingFraction ρ) = R := hdiv
  obtain ⟨X⟩ := D.exists_originalReserve_fullUnitInputExperiment Main Reserve b hq
    hθ.1 hθ.2 (mul_pos hd hR)
  have hrates := originalReserveWorking_intensity_count_rates hq b hρ hR.le
  let Y : OriginalReserveFullWorkingInputExperiment Main Reserve b ρ R := {
    fullLaw := X.fullLaw
    fullLaw_original_pair := by
      change (X.fullLaw : Measure (OriginalReserveUnitExperimentSpace (finrank ℝ S.covector.ker) ×
        TwoMarkedCloudSpace (finrank ℝ S.covector.ker) ℝ ℝ)).map
          ((fun p ↦ (p.1, p.2.1)) ∘ Prod.fst) = _
      rw [← Measure.map_map (measurable_fst.prodMk measurable_snd.fst) measurable_fst,
        X.fullLaw_fst, X.baseLaw_original_pair]
    fullLaw_main_sampler := by
      have h := X.fullLaw_original_main_sampler
      rw [hrates.1] at h
      exact h
    fullLaw_full_sampler := by
      have h := X.fullLaw_snd
      rw [hrates.2] at h
      exact h
    ae_full_arrays := by simpa only [hdiv'] using X.ae_originalWorking_fullArrays }
  have hwhole := X.ae_originalWorking_wholeReserve_input
  have hratio : θ/(1-θ) = ρ := originalReserveWorkingFraction_ratio hρ
  have hwhole' : ∀ᵐ p ∂(Y.fullLaw : Measure
      (OriginalReserveUnitExperimentSpace (finrank ℝ S.covector.ker) ×
        TwoMarkedCloudSpace (finrank ℝ S.covector.ker) ℝ ℝ)),
      ((legalMarkedInputSceneDilation (finrank ℝ S.covector.ker)
        (legalIntensityDilation (finrank ℝ S.covector.ker) ρ)
        (legalIntensityDilation_pos (finrank ℝ S.covector.ker) hρ).ne' p.1.2.1).2 :
          Measure (LegalColoredInputPoint (finrank ℝ S.covector.ker))).restrict
        ((Prod.fst ∘ Prod.fst) ⁻¹' originalCenteredPhysicalCubeRegion b (2*R)) =
        legalInputTwoBlockMeasure _ (originalMappedReserveCloudArrays _
          (originalOrientedRawCubePhysicalMap b R) p.1.2.2) := by
    simpa only [show originalReserveWorkingFraction ρ /
      (1-originalReserveWorkingFraction ρ) = ρ from hratio, hdiv'] using hwhole
  refine ⟨Y, ?_⟩
  filter_upwards [hwhole', Y.ae_full_arrays] with p hp hfull
  refine ⟨hp, ?_⟩
  rw [originalReserveMainIntensityInputReadout_window_decomposition, hp]
  exact hfull

end OriginalSeedConditionalMoments
end OTSelector.Reconstruction
