import OTSelector.Reconstruction.OriginalReserveFullWorkingInputExperiment
import OTSelector.Reconstruction.OriginalReservePhysicalArraySimplicity
import OTSelector.Finite.AtomicSubmeasureEmbedding
import OTSelector.Reconstruction.MarkedStationaryValueLegalStationaryReserveCore

/-! Genuine reserve indices embed into the same complete original working arrays. -/
open Set Function MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators Classical
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

/-- The literal full working-input identity recovers each entire original
colored finite array, including its genuine reserve-origin summand. -/
theorem originalWorkingInput_fullArray_color_decomposition {q : ℕ}
    {K : Set (Fin q → ℝ)} (hK : MeasurableSet K) (main : LegalMarkedOptimalInputScene q)
    (reserve full : BlockData (LegalMarkedPhysicalPoint q) × BlockData (LegalMarkedPhysicalPoint q))
    (hread : (main.2 : Measure (LegalColoredInputPoint q)).restrict
      ((Prod.fst ∘ Prod.fst) ⁻¹' K) + legalInputTwoBlockMeasure q reserve =
        legalInputTwoBlockMeasure q full) :
    legalInputBlockMeasure full.1 =
      (legalInputColorMeasure q main.2 0).restrict {p | p.1 ∈ K} +
        legalInputBlockMeasure reserve.1 ∧
    legalInputBlockMeasure full.2 =
      (legalInputColorMeasure q main.2 1).restrict {p | p.1 ∈ K} +
        legalInputBlockMeasure reserve.2 := by
  let U : Set (LegalMarkedPhysicalPoint q) := K ×ˢ univ
  have hU : MeasurableSet U := hK.prod MeasurableSet.univ
  have hset : (Prod.fst ∘ Prod.fst) ⁻¹' K = U ×ˢ (univ : Set (Fin 2)) := by
    ext p
    simp [U]
  have hsum : legalLocalFiniteMeasureSum
      (legalInputRestrictionLocal (U ×ˢ univ) main.2, legalInputTwoBlockLocal q reserve) =
        legalInputTwoBlockLocal q full := by
    apply Subtype.ext
    change (main.2 : Measure (LegalColoredInputPoint q)).restrict (U ×ˢ univ) +
      legalInputTwoBlockMeasure q reserve = legalInputTwoBlockMeasure q full
    rw [← hset]
    exact hread
  have hs := congrArg (fun ζ ↦ legalInputColorMeasure q ζ 0) hsum
  have ht := congrArg (fun ζ ↦ legalInputColorMeasure q ζ 1) hsum
  rw [legalInputColorMeasure_localFiniteMeasureSum,
    legalInputColorMeasure_restrict_prod q _ 0 hU,
    legalInputColorMeasure_twoBlock_source, legalInputColorMeasure_twoBlock_source] at hs
  rw [legalInputColorMeasure_localFiniteMeasureSum,
    legalInputColorMeasure_restrict_prod q _ 1 hU,
    legalInputColorMeasure_twoBlock_target, legalInputColorMeasure_twoBlock_target] at ht
  have hUeq : U = {p | p.1 ∈ K} := by ext p; simp [U]
  rw [hUeq] at hs ht
  exact ⟨hs.symm, ht.symm⟩

/-- The original reserve labels inject into these exact full original labels
with literal physical point and clock equality. No relabelled cloud is sampled. -/
theorem exists_originalReserveIndexEmbeddings_of_workingFullArrays {q : ℕ}
    {K : Set (Fin q → ℝ)} (hK : MeasurableSet K) (main : LegalMarkedOptimalInputScene q)
    (reserve full : BlockData (LegalMarkedPhysicalPoint q) × BlockData (LegalMarkedPhysicalPoint q))
    (hr : Injective reserve.1.2 ∧ Injective reserve.2.2)
    (hread : (main.2 : Measure (LegalColoredInputPoint q)).restrict
      ((Prod.fst ∘ Prod.fst) ⁻¹' K) + legalInputTwoBlockMeasure q reserve =
        legalInputTwoBlockMeasure q full) :
    ∃ es : Fin reserve.1.1 ↪ Fin full.1.1,
      ∃ et : Fin reserve.2.1 ↪ Fin full.2.1,
        (∀ i, full.1.2 (es i) = reserve.1.2 i) ∧
        (∀ j, full.2.2 (et j) = reserve.2.2 j) := by
  have hc := originalWorkingInput_fullArray_color_decomposition hK main reserve full hread
  have hs : legalInputBlockMeasure reserve.1 ≤ legalInputBlockMeasure full.1 := by
    rw [hc.1]
    exact Measure.le_add_left le_rfl
  have ht : legalInputBlockMeasure reserve.2 ≤ legalInputBlockMeasure full.2 := by
    rw [hc.2]
    exact Measure.le_add_left le_rfl
  obtain ⟨es, hes⟩ := exists_originalIndexEmbedding_of_sum_dirac_le reserve.1.2 full.1.2 hr.1 hs
  obtain ⟨et, het⟩ := exists_originalIndexEmbedding_of_sum_dirac_le reserve.2.2 full.2.2 hr.2 ht
  exact ⟨es, et, hes, het⟩

namespace OriginalReserveFullWorkingInputExperiment
variable {q : ℕ} {α β : Measure ℝ} [IsProbabilityMeasure α] [IsProbabilityMeasure β]
  {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
  {Main Reserve : LegalWeightedStationaryPoissonMatching q α β kin g}
  {b : OrthonormalBasis (Fin q) ℝ (EuclideanSpace ℝ (Fin q))} {ρ R : ℝ}
  (X : OriginalReserveFullWorkingInputExperiment Main Reserve b ρ R)

/-- In the same genuine complete experiment, FULL arrays are injective and
all observed original reserve indices embed into them preserving the entire
marked point. Positive spatial dimension and radius produce these properties
internally; clocks may have atoms and arrays may be empty. -/
theorem ae_fullArray_injective_and_originalReserve_embeddings (hq : 0 < q) (hR : 0 < R) :
    ∀ᵐ p ∂(X.fullLaw : Measure (OriginalReserveUnitExperimentSpace q × TwoMarkedCloudSpace q ℝ ℝ)),
      let full := originalMappedReserveCloudArrays q (originalOrientedRawCubePhysicalMap b R) p.2
      let reserve := originalMappedReserveCloudArrays q (originalOrientedRawCubePhysicalMap b R) p.1.2.2
      Injective full.1.2 ∧ Injective full.2.2 ∧
      ∃ es : Fin reserve.1.1 ↪ Fin full.1.1,
        ∃ et : Fin reserve.2.1 ↪ Fin full.2.1,
          (∀ i, full.1.2 (es i) = reserve.1.2 i) ∧
          (∀ j, full.2.2 (et j) = reserve.2.2 j) := by
  have hf : ∀ᵐ cloud ∂(X.fullLaw : Measure
      (OriginalReserveUnitExperimentSpace q × TwoMarkedCloudSpace q ℝ ℝ)).map Prod.snd,
      Injective (originalMappedReserveCloudArrays q (originalOrientedRawCubePhysicalMap b R) cloud).1.2 ∧
      Injective (originalMappedReserveCloudArrays q (originalOrientedRawCubePhysicalMap b R) cloud).2.2 := by
    rw [X.fullLaw_full_sampler]
    exact ae_injective_originalMappedReserveCloudArrays hq α β _ b hR.ne'
  have hfull := ae_of_ae_map measurable_snd.aemeasurable hf
  have hreserve := X.ae_of_main_sampler (ae_snd_of_ae
    (ae_injective_originalMappedReserveCloudArrays hq α β
      (Real.toNNReal ρ * (volume (originalCenteredPhysicalCubeRegion b (2*R))).toNNReal) b hR.ne'))
  filter_upwards [hfull, hreserve, X.ae_full_arrays] with p hfi hri hp
  exact ⟨hfi.1, hfi.2, exists_originalReserveIndexEmbeddings_of_workingFullArrays
    (measurableSet_originalOrientedTraffic_cube b R) p.1.1 _ _ hri hp⟩

end OriginalReserveFullWorkingInputExperiment
end OTSelector.Reconstruction
