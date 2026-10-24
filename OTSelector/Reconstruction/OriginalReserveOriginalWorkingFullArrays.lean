import OTSelector.Reconstruction.OriginalLegalScreeningPressureDilationInput
import OTSelector.Reconstruction.OriginalReserveUnitInputClockBlockCounts

/-! The actual full original arrays survive inverse physical dilation in the unchanged working experiment. -/
open Set Function MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators Classical
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
namespace OriginalReserveFullUnitInputExperiment
variable {q : ℕ} {α β : Measure ℝ} [IsProbabilityMeasure α] [IsProbabilityMeasure β]
  {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
  {Main Reserve : LegalWeightedStationaryPoissonMatching q α β kin g}
  {b : OrthonormalBasis (Fin q) ℝ (EuclideanSpace ℝ (Fin q))}
  {θ R : ℝ} {hθ : 0 < θ} {hθ1 : θ < 1}
  (X : OriginalReserveFullUnitInputExperiment Main Reserve b θ hθ hθ1 R)
local notation "d" => legalIntensityDilation q (1-θ)

/-- The complete full-array lift preserves the unchanged original main and
literal reserve sampler marginal. Neither the whole reserve nor FULL witness
is placed in the conditional iid auxiliary coordinates. -/
theorem fullLaw_original_main_sampler :
    (X.fullLaw : Measure (OriginalReserveUnitExperimentSpace q × TwoMarkedCloudSpace q ℝ ℝ)).map
      (fun p ↦ (p.1.1, p.1.2.2)) =
      (Main.law : Measure (LegalMarkedOptimalInputScene q)).prod
        (twoMarkedCloudLaw q ℝ ℝ α β
          (Real.toNNReal θ * (volume (originalCenteredPhysicalCubeRegion b (2*R))).toNNReal)) := by
  change (X.fullLaw : Measure (OriginalReserveUnitExperimentSpace q ×
    TwoMarkedCloudSpace q ℝ ℝ)).map ((fun p ↦ (p.1, p.2.2)) ∘ Prod.fst) = _
  rw [← Measure.map_map (measurable_fst.prodMk measurable_snd.snd) measurable_fst,
    X.fullLaw_fst, X.baseLaw_original_main_sampler]

/-- Inverse dilation identifies the exact full original array with the
unchanged original main window plus its actual reserve array on the working
cube. Full indices, marks, colors and repeated observations remain unchanged. -/
theorem ae_originalWorking_fullArrays :
    ∀ᵐ p ∂(X.fullLaw : Measure (OriginalReserveUnitExperimentSpace q × TwoMarkedCloudSpace q ℝ ℝ)),
      (p.1.1.2 : Measure (LegalColoredInputPoint q)).restrict
        ((Prod.fst ∘ Prod.fst) ⁻¹' originalCenteredPhysicalCubeRegion b (2*(R/d))) +
      legalInputTwoBlockMeasure q (originalMappedReserveCloudArrays q
        (originalOrientedRawCubePhysicalMap b (R/d)) p.1.2.2) =
      legalInputTwoBlockMeasure q (originalMappedReserveCloudArrays q
        (originalOrientedRawCubePhysicalMap b (R/d)) p.2) := by
  have hd : 0 < d := legalIntensityDilation_pos q (sub_pos.mpr hθ1)
  filter_upwards [X.ae_of_base X.ae_unitInput_eq_dilated_original_experiment,
    X.ae_full_input] with p hp hfull
  apply (legalColoredInputDilation q d hd.ne').measurableEmbedding.map_injective
  calc
    _ = ((originalReserveUnitInputReadout q θ hθ hθ1 p.1).2 :
        Measure (LegalColoredInputPoint q)).restrict
          ((Prod.fst ∘ Prod.fst) ⁻¹' originalCenteredPhysicalCubeRegion b (2*R)) := hp.symm
    _ = legalInputTwoBlockMeasure q (originalMappedReserveCloudArrays q
        (originalOrientedRawCubePhysicalMap b R) p.2) := hfull
    _ = _ := (originalMappedReserveCloudArrays_oriented_dilation b hd.ne' R p.2).symm

end OriginalReserveFullUnitInputExperiment
end OTSelector.Reconstruction
