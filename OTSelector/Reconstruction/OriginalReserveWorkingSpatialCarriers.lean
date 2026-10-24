import OTSelector.Reconstruction.OriginalReserveFullWorkingInputExperiment
import OTSelector.Reconstruction.OriginalReservePhysicalWindowSupport

/-! All actual original FULL and reserve points remain in the same working physical cube. -/
open Set Function MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators Classical
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000

/-- Every original raw sampler coordinate maps into its genuine same-frame
physical cube, at every count rate. Only the actual unit-cube point law is used. -/
theorem ae_all_originalRawReserveCloud_physical_mem {q : ℕ}
    (γ : Measure ℝ) [IsProbabilityMeasure γ] (rate : ℝ≥0)
    (b : OrthonormalBasis (Fin q) ℝ (EuclideanSpace ℝ (Fin q)))
    {R : ℝ} (hR : 0 < R) :
    ∀ᵐ cloud ∂markedPoissonLaw q ℝ γ rate, ∀ i : ℕ,
      originalOrientedRawCubePhysicalMap b R (cloud.2 i).1 ∈
        originalCenteredPhysicalCubeRegion b (2*R) := by
  have hp : ∀ᵐ x ∂(cubeMeasure (Fin q) 1).map (originalOrientedRawCubePhysicalMap b R),
      x ∈ originalCenteredPhysicalCubeRegion b (2*R) := by
    rw [map_originalUnitCube_oriented_eq_normalizedFiniteLaw b hR]
    exact ae_originalPhysicalReservePoint_mem q (measurableSet_originalOrientedTraffic_cube b R)
  have hpoint := ae_of_ae_map (measurable_originalOrientedRawCubePhysicalMap b R).aemeasurable hp
  have hm : ∀ᵐ p ∂(cubeMeasure (Fin q) 1).prod γ,
      originalOrientedRawCubePhysicalMap b R p.1 ∈ originalCenteredPhysicalCubeRegion b (2*R) :=
    ae_fst_of_ae hpoint
  have hs : ∀ᵐ seq ∂markedSeqLaw (q := q) ℝ γ, ∀ i : ℕ,
      originalOrientedRawCubePhysicalMap b R (seq i).1 ∈
        originalCenteredPhysicalCubeRegion b (2*R) := by
    apply ae_all_iff.mpr
    intro i
    have he : ∀ᵐ p ∂(markedSeqLaw (q := q) ℝ γ).map (fun seq ↦ seq i),
        originalOrientedRawCubePhysicalMap b R p.1 ∈
          originalCenteredPhysicalCubeRegion b (2*R) := by
      rw [markedSeqLaw, Measure.infinitePi_map_eval]
      exact hm
    exact ae_of_ae_map (measurable_pi_apply i).aemeasurable he
  exact ae_snd_of_ae hs

/-- Both genuine original marked Poisson samplers remain in the same physical
cube on one event, simultaneously for all original natural indices. -/
theorem ae_all_originalRawTwoReserveCloud_physical_mem {q : ℕ}
    (α β : Measure ℝ) [IsProbabilityMeasure α] [IsProbabilityMeasure β] (rate : ℝ≥0)
    (b : OrthonormalBasis (Fin q) ℝ (EuclideanSpace ℝ (Fin q)))
    {R : ℝ} (hR : 0 < R) :
    ∀ᵐ cloud ∂twoMarkedCloudLaw q ℝ ℝ α β rate,
      (∀ i : ℕ, originalOrientedRawCubePhysicalMap b R (cloud.1.2 i).1 ∈
        originalCenteredPhysicalCubeRegion b (2*R)) ∧
      (∀ j : ℕ, originalOrientedRawCubePhysicalMap b R (cloud.2.2 j).1 ∈
        originalCenteredPhysicalCubeRegion b (2*R)) :=
  (ae_fst_of_ae (ae_all_originalRawReserveCloud_physical_mem α rate b hR)).and
    (ae_snd_of_ae (ae_all_originalRawReserveCloud_physical_mem β rate b hR))

namespace OriginalReserveFullWorkingInputExperiment
variable {q : ℕ} {α β : Measure ℝ} [IsProbabilityMeasure α] [IsProbabilityMeasure β]
  {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
  {Main Reserve : LegalWeightedStationaryPoissonMatching q α β kin g}
  {b : OrthonormalBasis (Fin q) ℝ (EuclideanSpace ℝ (Fin q))} {ρ R : ℝ}
  (X : OriginalReserveFullWorkingInputExperiment Main Reserve b ρ R)

/-- The actual physical FULL and reserve arrays in the same complete working
experiment all lie in its literal cube. No support or diameter conclusion is
assumed and the whole witnesses do not enter any iid conditioning. -/
theorem ae_fullAndReserveArrays_in_workingCube (hR : 0 < R) :
    ∀ᵐ p ∂(X.fullLaw : Measure (OriginalReserveUnitExperimentSpace q × TwoMarkedCloudSpace q ℝ ℝ)),
      let full := originalMappedReserveCloudArrays q (originalOrientedRawCubePhysicalMap b R) p.2
      let reserve := originalMappedReserveCloudArrays q (originalOrientedRawCubePhysicalMap b R) p.1.2.2
      (∀ i, (full.1.2 i).1 ∈ originalCenteredPhysicalCubeRegion b (2*R)) ∧
      (∀ j, (full.2.2 j).1 ∈ originalCenteredPhysicalCubeRegion b (2*R)) ∧
      (∀ i, (reserve.1.2 i).1 ∈ originalCenteredPhysicalCubeRegion b (2*R)) ∧
      (∀ j, (reserve.2.2 j).1 ∈ originalCenteredPhysicalCubeRegion b (2*R)) := by
  have hf : ∀ᵐ cloud ∂(X.fullLaw : Measure
      (OriginalReserveUnitExperimentSpace q × TwoMarkedCloudSpace q ℝ ℝ)).map Prod.snd,
      (∀ i : ℕ, originalOrientedRawCubePhysicalMap b R (cloud.1.2 i).1 ∈
        originalCenteredPhysicalCubeRegion b (2*R)) ∧
      (∀ j : ℕ, originalOrientedRawCubePhysicalMap b R (cloud.2.2 j).1 ∈
        originalCenteredPhysicalCubeRegion b (2*R)) := by
    rw [X.fullLaw_full_sampler]
    exact ae_all_originalRawTwoReserveCloud_physical_mem α β _ b hR
  have hreserve := X.ae_of_main_sampler (ae_snd_of_ae
    (ae_all_originalRawTwoReserveCloud_physical_mem α β
      (Real.toNNReal ρ * (volume (originalCenteredPhysicalCubeRegion b (2*R))).toNNReal) b hR))
  filter_upwards [ae_of_ae_map measurable_snd.aemeasurable hf, hreserve] with p hp hr
  exact ⟨fun i ↦ hp.1 i, fun j ↦ hp.2 j, fun i ↦ hr.1 i, fun j ↦ hr.2 j⟩

end OriginalReserveFullWorkingInputExperiment
end OTSelector.Reconstruction
