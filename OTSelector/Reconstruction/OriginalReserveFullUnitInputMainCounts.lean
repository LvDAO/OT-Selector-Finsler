import OTSelector.Reconstruction.OriginalReserveFullUnitInputExperiment
import OTSelector.Reconstruction.OriginalReserveDilatedBlockCounts
import OTSelector.Reconstruction.OriginalClasswiseOriginalAtomRepairClockSlabBlocksSets
import OTSelector.Probability.PoissonCountDiscrepancy

/-! The actual main in the full unit-input experiment has complementary-intensity block counts. -/
open Set Function MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators Classical
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
namespace OriginalReserveFullUnitInputExperiment
variable {q : ℕ} {α β : Measure ℝ} [IsProbabilityMeasure α] [IsProbabilityMeasure β]
  {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
  {Main Reserve : LegalWeightedStationaryPoissonMatching q α β kin g}
  {b : OrthonormalBasis (Fin q) ℝ (EuclideanSpace ℝ (Fin q))}
  {θ R : ℝ} {hθ : 0 < θ} {hθ1 : θ < 1}
  (X : OriginalReserveFullUnitInputExperiment Main Reserve b θ hθ hθ1 R)

/-- Projection from the same full joining gives the actual dilated original
main scene law, including all original matching/input correlations. -/
theorem fullLaw_main_scene :
    (X.fullLaw : Measure (OriginalReserveUnitExperimentSpace q × TwoMarkedCloudSpace q ℝ ℝ)).map
      (fun p ↦ (originalReserveMainSamplerReadout q θ hθ1 p.1).1) =
      (legalMarkedInputDilationLaw q (legalIntensityDilation q (1 - θ))
        (legalIntensityDilation_pos q (sub_pos.mpr hθ1)).ne' Main.law : Measure (LegalMarkedOptimalInputScene q)) := by
  have hm : Measurable (fun p : OriginalReserveUnitExperimentSpace q × TwoMarkedCloudSpace q ℝ ℝ ↦
      originalReserveMainSamplerReadout q θ hθ1 p.1) :=
    (measurable_originalReserveMainSamplerReadout q θ hθ1).comp measurable_fst
  change (X.fullLaw : Measure (OriginalReserveUnitExperimentSpace q × TwoMarkedCloudSpace q ℝ ℝ)).map
    (Prod.fst ∘ (fun p ↦ originalReserveMainSamplerReadout q θ hθ1 p.1)) = _
  rw [← Measure.map_map measurable_fst hm, X.fullLaw_main_sampler,
    Measure.map_fst_prod, measure_univ, one_smul]

/-- The actual main block-count pair under the full joining has means
(1-theta)V alpha(S) and (1-theta)V beta(T), with true independence of its two colors. -/
theorem hasLaw_mainBlockCount_pair (hq : 0 < q) (hR : 0 ≤ R)
    {S T : Set ℝ} (hS : MeasurableSet S) (hT : MeasurableSet T) :
    HasLaw (fun p : OriginalReserveUnitExperimentSpace q × TwoMarkedCloudSpace q ℝ ℝ ↦
      (originalMainPhysicalBlockCount (originalCenteredPhysicalCubeRegion b (2 * R)) S 0
          (originalReserveMainSamplerReadout q θ hθ1 p.1).1,
        originalMainPhysicalBlockCount (originalCenteredPhysicalCubeRegion b (2 * R)) T 1
          (originalReserveMainSamplerReadout q θ hθ1 p.1).1))
      ((poissonMeasure ((Real.toNNReal (1 - θ) * (volume (originalCenteredPhysicalCubeRegion b (2 * R))).toNNReal) *
        (α S).toNNReal)).prod
        (poissonMeasure ((Real.toNNReal (1 - θ) * (volume (originalCenteredPhysicalCubeRegion b (2 * R))).toNNReal) *
          (β T).toNNReal)))
      (X.fullLaw : Measure (OriginalReserveUnitExperimentSpace q × TwoMarkedCloudSpace q ℝ ℝ)) := by
  have hm : HasLaw
      (fun p : OriginalReserveUnitExperimentSpace q × TwoMarkedCloudSpace q ℝ ℝ ↦
        (originalReserveMainSamplerReadout q θ hθ1 p.1).1)
      (legalMarkedInputDilationLaw q (legalIntensityDilation q (1 - θ))
        (legalIntensityDilation_pos q (sub_pos.mpr hθ1)).ne' Main.law : Measure (LegalMarkedOptimalInputScene q))
      (X.fullLaw : Measure (OriginalReserveUnitExperimentSpace q × TwoMarkedCloudSpace q ℝ ℝ)) :=
    ⟨(measurable_fst.comp ((measurable_originalReserveMainSamplerReadout q θ hθ1).comp
      measurable_fst)).aemeasurable, X.fullLaw_main_scene⟩
  exact (Main.hasLaw_originalIntensityMainOrientedBlockCount_pair b hq
    (sub_pos.mpr hθ1) hR hS hT).fun_comp hm

/-- Equal actual clock-block masses give the true square-root discrepancy
bound for this same joined main, with its complementary physical intensity. -/
theorem mainBlock_discrepancy (hq : 0 < q) (hR : 0 ≤ R)
    {S T : Set ℝ} (hS : MeasurableSet S) (hT : MeasurableSet T) (hbal : α S = β T) :
    let K := originalCenteredPhysicalCubeRegion b (2 * R)
    Integrable (fun p : OriginalReserveUnitExperimentSpace q × TwoMarkedCloudSpace q ℝ ℝ ↦
      |(originalMainPhysicalBlockCount K S 0 (originalReserveMainSamplerReadout q θ hθ1 p.1).1 : ℝ) -
        (originalMainPhysicalBlockCount K T 1 (originalReserveMainSamplerReadout q θ hθ1 p.1).1 : ℝ)|)
      (X.fullLaw : Measure _) ∧
    (∫ p : OriginalReserveUnitExperimentSpace q × TwoMarkedCloudSpace q ℝ ℝ,
      |(originalMainPhysicalBlockCount K S 0 (originalReserveMainSamplerReadout q θ hθ1 p.1).1 : ℝ) -
        (originalMainPhysicalBlockCount K T 1 (originalReserveMainSamplerReadout q θ hθ1 p.1).1 : ℝ)|
      ∂(X.fullLaw : Measure _)) ≤ Real.sqrt (2 * (1 - θ) * volume.real K * α.real S) := by
  dsimp only
  let a := Real.toNNReal (1 - θ) *
    (volume (originalCenteredPhysicalCubeRegion b (2 * R))).toNNReal * (α S).toNNReal
  have hlaw := X.hasLaw_mainBlockCount_pair hq hR hS hT
  rw [← hbal] at hlaw
  have hm : MeasurePreserving
      (fun p : OriginalReserveUnitExperimentSpace q × TwoMarkedCloudSpace q ℝ ℝ ↦
        (originalMainPhysicalBlockCount (originalCenteredPhysicalCubeRegion b (2 * R)) S 0
            (originalReserveMainSamplerReadout q θ hθ1 p.1).1,
          originalMainPhysicalBlockCount (originalCenteredPhysicalCubeRegion b (2 * R)) T 1
            (originalReserveMainSamplerReadout q θ hθ1 p.1).1))
      (X.fullLaw : Measure _) ((poissonMeasure a).prod (poissonMeasure a)) := by
    refine ⟨?_, hlaw.map_eq⟩
    exact ((measurable_originalMainPhysicalBlockCount (measurableSet_originalOrientedTraffic_cube b R) hS 0).prodMk
      (measurable_originalMainPhysicalBlockCount (measurableSet_originalOrientedTraffic_cube b R) hT 1)).comp
      (measurable_fst.comp ((measurable_originalReserveMainSamplerReadout q θ hθ1).comp measurable_fst))
  have hI : Integrable (fun z : ℕ × ℕ ↦ |(z.1 : ℝ) - (z.2 : ℝ)|)
      ((poissonMeasure a).prod (poissonMeasure a)) :=
    (((integrable_id_poissonMeasure a).comp_fst _).sub
      ((integrable_id_poissonMeasure a).comp_snd _)).abs
  have hf : Measurable (fun z : ℕ × ℕ ↦ |(z.1 : ℝ) - (z.2 : ℝ)|) := by fun_prop
  refine ⟨hm.integrable_comp_of_integrable hI, ?_⟩
  have heq := hlaw.integral_comp hf.aestronglyMeasurable
  change (∫ p : OriginalReserveUnitExperimentSpace q × TwoMarkedCloudSpace q ℝ ℝ,
      |(originalMainPhysicalBlockCount (originalCenteredPhysicalCubeRegion b (2 * R)) S 0
          (originalReserveMainSamplerReadout q θ hθ1 p.1).1 : ℝ) -
        (originalMainPhysicalBlockCount (originalCenteredPhysicalCubeRegion b (2 * R)) T 1
          (originalReserveMainSamplerReadout q θ hθ1 p.1).1 : ℝ)| ∂(X.fullLaw : Measure _)) = _ at heq
  rw [heq]
  convert integral_abs_sub_poissonPair_le a using 1
  simp only [a, NNReal.coe_mul, ENNReal.coe_toNNReal_eq_toReal,
    Real.coe_toNNReal _ (sub_pos.mpr hθ1).le, measureReal_def]
  congr 1
  ring

/-- Actual Hall-block balance is produced by the same clock-slab construction;
zero blocks and zero count fibres do not require extra population assumptions. -/
theorem clockSlabBlock_main_discrepancy (hq : 0 < q) (hR : 0 ≤ R)
    (G : OriginalStageClockGrid) (block : G.ClockSlabBlock α β) :
    let K := originalCenteredPhysicalCubeRegion b (2 * R)
    Integrable (fun p : OriginalReserveUnitExperimentSpace q × TwoMarkedCloudSpace q ℝ ℝ ↦
      |(originalMainPhysicalBlockCount K (G.sourceBlockCell α β block) 0
          (originalReserveMainSamplerReadout q θ hθ1 p.1).1 : ℝ) -
        (originalMainPhysicalBlockCount K (G.targetBlockCell α β block) 1
          (originalReserveMainSamplerReadout q θ hθ1 p.1).1 : ℝ)|) (X.fullLaw : Measure _) ∧
    (∫ p : OriginalReserveUnitExperimentSpace q × TwoMarkedCloudSpace q ℝ ℝ,
      |(originalMainPhysicalBlockCount K (G.sourceBlockCell α β block) 0
          (originalReserveMainSamplerReadout q θ hθ1 p.1).1 : ℝ) -
        (originalMainPhysicalBlockCount K (G.targetBlockCell α β block) 1
          (originalReserveMainSamplerReadout q θ hθ1 p.1).1 : ℝ)| ∂(X.fullLaw : Measure _)) ≤
      Real.sqrt (2 * (1 - θ) * volume.real K * α.real (G.sourceBlockCell α β block)) := by
  exact X.mainBlock_discrepancy hq hR (G.blockCells_measurable block).1
    (G.blockCells_measurable block).2
    ((ENNReal.toReal_eq_toReal_iff' (measure_ne_top α _) (measure_ne_top β _)).mp
      (G.block_mass_balance block))

end OriginalReserveFullUnitInputExperiment
end OTSelector.Reconstruction
