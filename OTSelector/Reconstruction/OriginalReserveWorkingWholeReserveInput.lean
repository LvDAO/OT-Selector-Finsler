import OTSelector.Reconstruction.OriginalReserveOriginalWorkingFullArrays
import OTSelector.Reconstruction.OriginalReserveWorkingIntensityParameters

/-! The same whole original reserve has its genuine working-intensity window in the complete experiment. -/
open Set Function MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators Classical
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000

/-- The canonical positive physical factors compose to exactly the original
reserve factor, with the actual reserve-to-main intensity ratio. -/
theorem originalReserveWorking_intensity_scale_comp {q : ℕ} {θ : ℝ}
    (hθ : 0 < θ) (hθ1 : θ < 1) :
    legalIntensityDilation q (1-θ) * legalIntensityDilation q (θ/(1-θ)) =
      legalIntensityDilation q θ := by
  have hc : 0 < 1-θ := sub_pos.mpr hθ1
  unfold legalIntensityDilation
  rw [← Real.mul_rpow hc.le (div_nonneg hθ.le hc.le), mul_div_cancel₀ θ hc.ne']

/-- Whole input measure dilation composes with exactly those canonical
intensities; marks and immutable colors are unchanged. -/
theorem originalReserveWorking_wholeInput_dilation_comp {q : ℕ} {θ : ℝ}
    (hθ : 0 < θ) (hθ1 : θ < 1) (scene : LegalMarkedOptimalInputScene q) :
    (((legalMarkedInputSceneDilation q (legalIntensityDilation q (θ/(1-θ)))
      (legalIntensityDilation_pos q (div_pos hθ (sub_pos.mpr hθ1))).ne' scene).2 :
        Measure (LegalColoredInputPoint q))).map
          (legalColoredInputDilation q (legalIntensityDilation q (1-θ))
            (legalIntensityDilation_pos q (sub_pos.mpr hθ1)).ne') =
    ((legalMarkedInputSceneDilation q (legalIntensityDilation q θ)
      (legalIntensityDilation_pos q hθ).ne' scene).2 : Measure (LegalColoredInputPoint q)) := by
  change ((scene.2 : Measure (LegalColoredInputPoint q)).map
    (legalColoredInputDilation q (legalIntensityDilation q (θ/(1-θ)))
      (legalIntensityDilation_pos q (div_pos hθ (sub_pos.mpr hθ1))).ne')).map _ = _
  rw [Measure.map_map
    (legalColoredInputDilation q (legalIntensityDilation q (1-θ))
      (legalIntensityDilation_pos q (sub_pos.mpr hθ1)).ne').continuous.measurable
    (legalColoredInputDilation q (legalIntensityDilation q (θ/(1-θ)))
      (legalIntensityDilation_pos q (div_pos hθ (sub_pos.mpr hθ1))).ne').continuous.measurable]
  congr 1
  funext p
  change ((legalIntensityDilation q (1-θ) •
    (legalIntensityDilation q (θ/(1-θ)) • p.1.1), p.1.2), p.2) = _
  rw [smul_smul, originalReserveWorking_intensity_scale_comp hθ hθ1]
  rfl

namespace OriginalReserveFullUnitInputExperiment
variable {q : ℕ} {α β : Measure ℝ} [IsProbabilityMeasure α] [IsProbabilityMeasure β]
  {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
  {Main Reserve : LegalWeightedStationaryPoissonMatching q α β kin g}
  {b : OrthonormalBasis (Fin q) ℝ (EuclideanSpace ℝ (Fin q))}
  {θ R : ℝ} {hθ : 0 < θ} {hθ1 : θ < 1}
  (X : OriginalReserveFullUnitInputExperiment Main Reserve b θ hθ hθ1 R)
local notation "d" => legalIntensityDilation q (1-θ)

/-- The same original whole reserve, at its actual working intensity, equals
the literal original reserve arrays on the working cube. The entire FULL lift
preserves this identity along with all original labels and correlations. -/
theorem ae_originalWorking_wholeReserve_input :
    ∀ᵐ p ∂(X.fullLaw : Measure (OriginalReserveUnitExperimentSpace q × TwoMarkedCloudSpace q ℝ ℝ)),
      ((legalMarkedInputSceneDilation q (legalIntensityDilation q (θ/(1-θ)))
        (legalIntensityDilation_pos q (div_pos hθ (sub_pos.mpr hθ1))).ne' p.1.2.1).2 :
          Measure (LegalColoredInputPoint q)).restrict
        ((Prod.fst ∘ Prod.fst) ⁻¹' originalCenteredPhysicalCubeRegion b (2*(R/d))) =
      legalInputTwoBlockMeasure q (originalMappedReserveCloudArrays q
        (originalOrientedRawCubePhysicalMap b (R/d)) p.1.2.2) := by
  have hd : 0 < d := legalIntensityDilation_pos q (sub_pos.mpr hθ1)
  filter_upwards [X.ae_of_base (X.ae_base_inputs.mono fun _ hp ↦ hp.1)] with p hp
  apply (legalColoredInputDilation q d hd.ne').measurableEmbedding.map_injective
  calc
    _ = (((legalMarkedInputSceneDilation q (legalIntensityDilation q (θ/(1-θ)))
        (legalIntensityDilation_pos q (div_pos hθ (sub_pos.mpr hθ1))).ne' p.1.2.1).2 :
          Measure (LegalColoredInputPoint q)).map
            (legalColoredInputDilation q d hd.ne')).restrict
              ((Prod.fst ∘ Prod.fst) ⁻¹' originalCenteredPhysicalCubeRegion b (2*R)) :=
      (originalColoredInput_orientedWindow_dilation b hd R _).symm
    _ = ((legalMarkedInputSceneDilation q (legalIntensityDilation q θ)
        (legalIntensityDilation_pos q hθ).ne' p.1.2.1).2 :
          Measure (LegalColoredInputPoint q)).restrict
            ((Prod.fst ∘ Prod.fst) ⁻¹' originalCenteredPhysicalCubeRegion b (2*R)) := by
      rw [originalReserveWorking_wholeInput_dilation_comp hθ hθ1]
    _ = legalInputTwoBlockMeasure q (originalMappedReserveCloudArrays q
        (originalOrientedRawCubePhysicalMap b R) p.1.2.2) := hp
    _ = _ := (originalMappedReserveCloudArrays_oriented_dilation b hd.ne' R p.1.2.2).symm

end OriginalReserveFullUnitInputExperiment
end OTSelector.Reconstruction
