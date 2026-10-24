import OTSelector.Reconstruction.OriginalLegalScreeningPressureDilationMean
import OTSelector.Reconstruction.OriginalReserveFullUnitInputExperiment
import OTSelector.Reconstruction.MarkedStationaryValueLegalOriginalJointSceneReroot

/-! The actual unit-input experiment pulls back to the unchanged original main
scene and a raw reserve sampler on the true preimage cube. -/
open Set Function MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
local instance originalPressureDilationInputPolish (q : ℕ) :
    PolishSpace (LocalFiniteMeasure (LegalColoredInputPoint q)) := LocalFiniteMeasure.instPolishSpace
local instance originalPressureDilationPlanPolish (q : ℕ) :
    PolishSpace (LocalFiniteMeasure (LegalMarkedPhysicalEdge q)) := LocalFiniteMeasure.instPolishSpace

private theorem original_localFiniteMapHomeomorph_symm_apply
    {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [T2Space X]
    [LocallyCompactSpace X] [BorelSpace X] (e : X ≃ₜ X) (μ : LocalFiniteMeasure X) :
    localFiniteMapHomeomorph e.symm (localFiniteMapHomeomorph e μ) = μ := by
  rw [localFiniteMapHomeomorph_comp,Homeomorph.self_trans_symm]
  apply Subtype.ext
  exact Measure.map_id

/-- Inverse physical dilation restores the same original scene, with both plans,
the complete colored input and every original clock unchanged. -/
theorem legalMarkedInputSceneDilation_inv_apply (q : ℕ) {c : ℝ} (hc : c ≠ 0)
    (scene : LegalMarkedOptimalInputScene q) :
    legalMarkedInputSceneDilation q c⁻¹ (inv_ne_zero hc)
      (legalMarkedInputSceneDilation q c hc scene) = scene := by
  have he : legalMarkedEdgeDilation q c⁻¹ (inv_ne_zero hc) =
      (legalMarkedEdgeDilation q c hc).symm := by
    apply Homeomorph.ext
    intro e
    rfl
  have hi : legalColoredInputDilation q c⁻¹ (inv_ne_zero hc) =
      (legalColoredInputDilation q c hc).symm := by
    apply Homeomorph.ext
    intro e
    rfl
  simp only [legalMarkedInputSceneDilation,he,hi,
    original_localFiniteMapHomeomorph_symm_apply]

namespace OriginalReserveFullUnitInputExperiment
variable {q : ℕ} {α β : Measure ℝ} [IsProbabilityMeasure α] [IsProbabilityMeasure β]
  {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
  {Main Reserve : LegalWeightedStationaryPoissonMatching q α β kin g}
  {b : OrthonormalBasis (Fin q) ℝ (EuclideanSpace ℝ (Fin q))}
  {θ R : ℝ} {hθ : 0 < θ} {hθ1 : θ < 1}
  (X : OriginalReserveFullUnitInputExperiment Main Reserve b θ hθ hθ1 R)
local notation "d" => legalIntensityDilation q (1-θ)

/-- The same actual base experiment also has the unchanged unit-intensity main
scene independent of the raw reserve sampler. This follows by inverting its proved
main-dilation marginal; the whole reserve scene never enters the iid auxiliary data. -/
theorem baseLaw_original_main_sampler :
    (X.baseLaw : Measure (OriginalReserveUnitExperimentSpace q)).map
      (fun p ↦ (p.1,p.2.2)) =
      (Main.law : Measure (LegalMarkedOptimalInputScene q)).prod
        (twoMarkedCloudLaw q ℝ ℝ α β
          (Real.toNNReal θ * (volume (originalCenteredPhysicalCubeRegion b (2*R))).toNNReal)) := by
  have hd : 0 < d := legalIntensityDilation_pos q (sub_pos.mpr hθ1)
  have hm := (continuous_legalMarkedInputSceneDilation q d⁻¹ (inv_ne_zero hd.ne')).measurable
  have hinv : ((legalMarkedInputDilationLaw q d hd.ne' Main.law :
      Measure (LegalMarkedOptimalInputScene q)).map
        (legalMarkedInputSceneDilation q d⁻¹ (inv_ne_zero hd.ne'))) = Main.law := by
    change ((Main.law : Measure (LegalMarkedOptimalInputScene q)).map
      (legalMarkedInputSceneDilation q d hd.ne')).map _ = _
    rw [Measure.map_map hm (continuous_legalMarkedInputSceneDilation q d hd.ne').measurable]
    have hcomp : legalMarkedInputSceneDilation q d⁻¹ (inv_ne_zero hd.ne') ∘
        legalMarkedInputSceneDilation q d hd.ne' = id := by
      funext scene
      exact legalMarkedInputSceneDilation_inv_apply q hd.ne' scene
    rw [hcomp,Measure.map_id]
  have heq := congrArg (fun μ : Measure (LegalMarkedOptimalInputScene q × TwoMarkedCloudSpace q ℝ ℝ) ↦
    μ.map (Prod.map (legalMarkedInputSceneDilation q d⁻¹ (inv_ne_zero hd.ne')) id))
      X.baseLaw_main_sampler
  rw [Measure.map_map (hm.prodMap measurable_id)
    (measurable_originalReserveMainSamplerReadout q θ hθ1),
    ← Measure.map_prod_map _ _ hm measurable_id,hinv,Measure.map_id] at heq
  simpa only [Function.comp_def,originalReserveMainSamplerReadout,Prod.map_apply,id_eq,
    legalMarkedInputSceneDilation_inv_apply] using heq

/-- The true unit input on the physical cube is the common dilation of the
unchanged original main input plus the raw original reserve on the preimage cube.
All full-array indices, clocks and multiplicities are retained. -/
theorem ae_unitInput_eq_dilated_original_experiment :
    ∀ᵐ p ∂(X.baseLaw : Measure (OriginalReserveUnitExperimentSpace q)),
      ((originalReserveUnitInputReadout q θ hθ hθ1 p).2 : Measure (LegalColoredInputPoint q)).restrict
        ((Prod.fst ∘ Prod.fst) ⁻¹' originalCenteredPhysicalCubeRegion b (2*R)) =
      (((p.1.2 : Measure (LegalColoredInputPoint q)).restrict
        ((Prod.fst ∘ Prod.fst) ⁻¹' originalCenteredPhysicalCubeRegion b (2*(R/d)))) +
        legalInputTwoBlockMeasure q (originalMappedReserveCloudArrays q
          (originalOrientedRawCubePhysicalMap b (R/d)) p.2.2)).map
            (legalColoredInputDilation q d (legalIntensityDilation_pos q (sub_pos.mpr hθ1)).ne') := by
  have hd : 0 < d := legalIntensityDilation_pos q (sub_pos.mpr hθ1)
  filter_upwards [X.ae_base_inputs] with p hp
  calc
    _ = (((originalReserveMainSamplerReadout q θ hθ1 p).1).2 :
        Measure (LegalColoredInputPoint q)).restrict
          ((Prod.fst ∘ Prod.fst) ⁻¹' originalCenteredPhysicalCubeRegion b (2*R)) +
        legalInputTwoBlockMeasure q (originalMappedReserveCloudArrays q
          (originalOrientedRawCubePhysicalMap b R) p.2.2) := hp.2
    _ = ((p.1.2 : Measure (LegalColoredInputPoint q)).restrict
          ((Prod.fst ∘ Prod.fst) ⁻¹' originalCenteredPhysicalCubeRegion b (2*(R/d)))).map
            (legalColoredInputDilation q d hd.ne') +
        (legalInputTwoBlockMeasure q (originalMappedReserveCloudArrays q
          (originalOrientedRawCubePhysicalMap b (R/d)) p.2.2)).map
            (legalColoredInputDilation q d hd.ne') := by
      congr 1
      · exact originalColoredInput_orientedWindow_dilation b hd R _
      · exact (originalMappedReserveCloudArrays_oriented_dilation b hd.ne' R p.2.2).symm
    _ = _ := (Measure.map_add _ _ (legalColoredInputDilation q d hd.ne').continuous.measurable).symm

include hθ hθ1 in
/-- The actual raw reserve rate is lambda times working volume, where
lambda = theta/(1-theta). This is the original count rate under the same experiment. -/
theorem original_working_reserve_count_rate (hq : 0 < q) (hR : 0 ≤ R) :
    Real.toNNReal θ * (volume (originalCenteredPhysicalCubeRegion b (2*R))).toNNReal =
      Real.toNNReal (θ/(1-θ)) *
        (volume (originalCenteredPhysicalCubeRegion b (2*(R/d)))).toNNReal := by
  have hm : 0 < 1-θ := sub_pos.mpr hθ1
  have hv := congrArg (fun x : ℝ≥0 ↦ (x:ℝ))
    (originalOrientedReserveIntensity_count_rate hq b hm hR)
  simp only [NNReal.coe_mul,Real.coe_toNNReal _ hm.le,ENNReal.coe_toNNReal_eq_toReal] at hv
  apply NNReal.coe_injective
  simp only [NNReal.coe_mul,Real.coe_toNNReal _ hθ.le,
    Real.coe_toNNReal _ (div_nonneg hθ.le hm.le),ENNReal.coe_toNNReal_eq_toReal]
  rw [hv]
  field_simp

end OriginalReserveFullUnitInputExperiment
end OTSelector.Reconstruction
