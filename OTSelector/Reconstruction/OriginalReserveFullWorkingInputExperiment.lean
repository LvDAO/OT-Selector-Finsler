import OTSelector.Reconstruction.OriginalReserveOriginalWorkingFullArrays
import OTSelector.Reconstruction.OriginalReserveWorkingIntensityParameters
import OTSelector.Reconstruction.OriginalStageReserveJoinedExperiment

/-! Complete original finite arrays and iid-consumer marginals at every positive working reserve intensity. -/
open Set Function MeasureTheory ProbabilityTheory Filter Topology Module Manifold
open scoped ENNReal NNReal BigOperators Classical ContDiff
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability OTSelector.Geometry ContinuousFinslerNorm
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

/-- One complete working experiment retains the original independent main and
whole reserve, its genuine iid sampler, and the full finite arrays. FULL is only
an identity witness and never an auxiliary in a selected-position law. -/
structure OriginalReserveFullWorkingInputExperiment {q : ℕ} {α β : Measure ℝ}
    [IsProbabilityMeasure α] [IsProbabilityMeasure β]
    {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (Main Reserve : LegalWeightedStationaryPoissonMatching q α β kin g)
    (b : OrthonormalBasis (Fin q) ℝ (EuclideanSpace ℝ (Fin q))) (ρ R : ℝ) where
  fullLaw : ProbabilityMeasure (OriginalReserveUnitExperimentSpace q × TwoMarkedCloudSpace q ℝ ℝ)
  fullLaw_original_pair :
    (fullLaw : Measure (OriginalReserveUnitExperimentSpace q × TwoMarkedCloudSpace q ℝ ℝ)).map
      (fun p ↦ (p.1.1, p.1.2.1)) =
      (Main.law : Measure (LegalMarkedOptimalInputScene q)).prod (Reserve.law : Measure _)
  fullLaw_main_sampler :
    (fullLaw : Measure (OriginalReserveUnitExperimentSpace q × TwoMarkedCloudSpace q ℝ ℝ)).map
      (fun p ↦ (p.1.1, p.1.2.2)) =
      originalMainReserveExperimentLaw Main
        (Real.toNNReal ρ * (volume (originalCenteredPhysicalCubeRegion b (2*R))).toNNReal)
  fullLaw_full_sampler :
    (fullLaw : Measure (OriginalReserveUnitExperimentSpace q × TwoMarkedCloudSpace q ℝ ℝ)).map
      Prod.snd = twoMarkedCloudLaw q ℝ ℝ α β
        (Real.toNNReal (1+ρ) * (volume (originalCenteredPhysicalCubeRegion b (2*R))).toNNReal)
  ae_full_arrays :
    ∀ᵐ p ∂(fullLaw : Measure (OriginalReserveUnitExperimentSpace q × TwoMarkedCloudSpace q ℝ ℝ)),
      (p.1.1.2 : Measure (LegalColoredInputPoint q)).restrict
        ((Prod.fst ∘ Prod.fst) ⁻¹' originalCenteredPhysicalCubeRegion b (2*R)) +
      legalInputTwoBlockMeasure q (originalMappedReserveCloudArrays q
        (originalOrientedRawCubePhysicalMap b R) p.1.2.2) =
      legalInputTwoBlockMeasure q (originalMappedReserveCloudArrays q
        (originalOrientedRawCubePhysicalMap b R) p.2)

namespace OriginalReserveFullWorkingInputExperiment
variable {q : ℕ} {α β : Measure ℝ} [IsProbabilityMeasure α] [IsProbabilityMeasure β]
  {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
  {Main Reserve : LegalWeightedStationaryPoissonMatching q α β kin g}
  {b : OrthonormalBasis (Fin q) ℝ (EuclideanSpace ℝ (Fin q))} {ρ R : ℝ}
  (X : OriginalReserveFullWorkingInputExperiment Main Reserve b ρ R)

/-- Every proved event on the original main/raw-reserve experiment survives
the full-array lift, without any independence assertion about the witnesses. -/
theorem ae_of_main_sampler {P : LegalMarkedOptimalInputScene q × TwoMarkedCloudSpace q ℝ ℝ → Prop}
    (h : ∀ᵐ p ∂originalMainReserveExperimentLaw Main
      (Real.toNNReal ρ * (volume (originalCenteredPhysicalCubeRegion b (2*R))).toNNReal), P p) :
    ∀ᵐ p ∂(X.fullLaw : Measure (OriginalReserveUnitExperimentSpace q × TwoMarkedCloudSpace q ℝ ℝ)),
      P (p.1.1, p.1.2.2) := by
  have h' : ∀ᵐ p ∂(X.fullLaw : Measure
      (OriginalReserveUnitExperimentSpace q × TwoMarkedCloudSpace q ℝ ℝ)).map
        (fun p ↦ (p.1.1, p.1.2.2)), P p := by
    rw [X.fullLaw_main_sampler]
    exact h
  exact ae_of_ae_map (measurable_fst.fst.prodMk measurable_fst.snd.snd).aemeasurable h'

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
/-- Construct the full working experiment for any positive reserve intensity
from the two genuine original matchings. The full arrays, original indexed
window identity and both raw Poisson rates are outputs, not assumptions. -/
theorem exists_originalReserve_fullWorkingInputExperiment
    {kin : ℝ → ℝ → (Fin (finrank ℝ S.covector.ker) → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (Main Reserve : LegalWeightedStationaryPoissonMatching
      (finrank ℝ S.covector.ker) μ ν kin g)
    (b : OrthonormalBasis (Fin (finrank ℝ S.covector.ker)) ℝ
      (EuclideanSpace ℝ (Fin (finrank ℝ S.covector.ker))))
    (hq : 0 < finrank ℝ S.covector.ker) {ρ R : ℝ} (hρ : 0 < ρ) (hR : 0 < R) :
    letI : IsProbabilityMeasure μ := D.support.source.probability
    letI : IsProbabilityMeasure ν := D.support.target.probability
    Nonempty (OriginalReserveFullWorkingInputExperiment Main Reserve b ρ R) := by
  let : IsProbabilityMeasure μ := D.support.source.probability
  let : IsProbabilityMeasure ν := D.support.target.probability
  let θ := originalReserveWorkingFraction ρ
  let d := originalReserveWorkingScale (finrank ℝ S.covector.ker) ρ
  have hθ := originalReserveWorkingFraction_bounds hρ
  have hd : 0 < d := legalIntensityDilation_pos _ (sub_pos.mpr hθ.2)
  have hdiv : d*R/d = R := mul_div_cancel_left₀ R hd.ne'
  obtain ⟨X⟩ := D.exists_originalReserve_fullUnitInputExperiment Main Reserve b hq
    hθ.1 hθ.2 (mul_pos hd hR)
  have hrates := originalReserveWorking_intensity_count_rates hq b hρ hR.le
  refine ⟨{
    fullLaw := X.fullLaw
    fullLaw_original_pair := ?_
    fullLaw_main_sampler := ?_
    fullLaw_full_sampler := ?_
    ae_full_arrays := ?_ }⟩
  · change (X.fullLaw : Measure (OriginalReserveUnitExperimentSpace (finrank ℝ S.covector.ker) ×
      TwoMarkedCloudSpace (finrank ℝ S.covector.ker) ℝ ℝ)).map ((fun p ↦ (p.1, p.2.1)) ∘ Prod.fst) = _
    rw [← Measure.map_map (measurable_fst.prodMk measurable_snd.fst) measurable_fst,
      X.fullLaw_fst, X.baseLaw_original_pair]
  · have h := X.fullLaw_original_main_sampler
    rw [hrates.1] at h
    exact h
  · have h := X.fullLaw_snd
    rw [hrates.2] at h
    exact h
  · have h := X.ae_originalWorking_fullArrays
    change ∀ᵐ p ∂(X.fullLaw : Measure (OriginalReserveUnitExperimentSpace (finrank ℝ S.covector.ker) ×
      TwoMarkedCloudSpace (finrank ℝ S.covector.ker) ℝ ℝ)),
      (p.1.1.2 : Measure (LegalColoredInputPoint (finrank ℝ S.covector.ker))).restrict
        ((Prod.fst ∘ Prod.fst) ⁻¹' originalCenteredPhysicalCubeRegion b (2*(d*R/d))) +
      legalInputTwoBlockMeasure _ (originalMappedReserveCloudArrays _
        (originalOrientedRawCubePhysicalMap b (d*R/d)) p.1.2.2) =
      legalInputTwoBlockMeasure _ (originalMappedReserveCloudArrays _
        (originalOrientedRawCubePhysicalMap b (d*R/d)) p.2) at h
    simpa only [hdiv] using h

end OriginalSeedConditionalMoments
end OTSelector.Reconstruction
