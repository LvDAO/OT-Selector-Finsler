import OTSelector.Reconstruction.OriginalReserveFullUnitInputExperiment
import OTSelector.Reconstruction.OriginalReserveBlockSelectionPullback

/-! True source and target block-selected iid laws in the same full unit-input experiment. -/
open Set Function MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OTSelector.Reconstruction
open OTSelector.Probability

/-- The actual source view omits the whole reserve and full-array witnesses. -/
def originalReserveUnitSourceSamplerView (q : ℕ) (θ : ℝ) (hθ1 : θ < 1)
    (p : OriginalReserveUnitExperimentSpace q × TwoMarkedCloudSpace q ℝ ℝ) :=
  originalSourceReserveExperimentSplice (originalReserveMainSamplerReadout q θ hθ1 p.1)

/-- The target view uses the same original sampler with its two colors reordered. -/
def originalReserveUnitTargetSamplerView (q : ℕ) (θ : ℝ) (hθ1 : θ < 1)
    (p : OriginalReserveUnitExperimentSpace q × TwoMarkedCloudSpace q ℝ ℝ) :=
  originalTargetReserveExperimentSplice (originalReserveMainSamplerReadout q θ hθ1 p.1)

/-- The actual source sampler view is measurable. -/
theorem measurable_originalReserveUnitSourceSamplerView (q : ℕ) (θ : ℝ) (hθ1 : θ < 1) :
    Measurable (originalReserveUnitSourceSamplerView q θ hθ1) := by
  have h : Measurable (originalSourceReserveExperimentSplice (q := q)) := by
    unfold originalSourceReserveExperimentSplice
    fun_prop
  exact h.comp ((measurable_originalReserveMainSamplerReadout q θ hθ1).comp measurable_fst)

/-- The actual target sampler view is measurable. -/
theorem measurable_originalReserveUnitTargetSamplerView (q : ℕ) (θ : ℝ) (hθ1 : θ < 1) :
    Measurable (originalReserveUnitTargetSamplerView q θ hθ1) := by
  have h : Measurable (originalTargetReserveExperimentSplice (q := q)) := by
    unfold originalTargetReserveExperimentSplice
    fun_prop
  exact h.comp ((measurable_originalReserveMainSamplerReadout q θ hθ1).comp measurable_fst)

namespace OriginalReserveFullUnitInputExperiment
variable {q : ℕ} {α β : Measure ℝ} [IsProbabilityMeasure α] [IsProbabilityMeasure β]
  {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
  {Main Reserve : LegalWeightedStationaryPoissonMatching q α β kin g}
  {b : OrthonormalBasis (Fin q) ℝ (EuclideanSpace ℝ (Fin q))}
  {θ R : ℝ} {hθ : 0 < θ} {hθ1 : θ < 1}
  (X : OriginalReserveFullUnitInputExperiment Main Reserve b θ hθ hθ1 R)

/-- The source iid factorization follows from the proved same-experiment marginal. -/
theorem fullLaw_source_sampler :
    (X.fullLaw : Measure (OriginalReserveUnitExperimentSpace q × TwoMarkedCloudSpace q ℝ ℝ)).map
      (originalReserveUnitSourceSamplerView q θ hθ1) =
      (((legalMarkedInputDilationLaw q (legalIntensityDilation q (1 - θ))
        (legalIntensityDilation_pos q (sub_pos.mpr hθ1)).ne' Main.law : Measure (LegalMarkedOptimalInputScene q)).prod
      (markedPoissonLaw q ℝ β (Real.toNNReal θ *
        (volume (originalCenteredPhysicalCubeRegion b (2 * R))).toNNReal))).prod
      (markedPoissonLaw q ℝ α (Real.toNNReal θ *
        (volume (originalCenteredPhysicalCubeRegion b (2 * R))).toNNReal))) := by
  have h : Measurable (originalSourceReserveExperimentSplice (q := q)) := by
    unfold originalSourceReserveExperimentSplice
    fun_prop
  change (X.fullLaw : Measure (OriginalReserveUnitExperimentSpace q × TwoMarkedCloudSpace q ℝ ℝ)).map
    (originalSourceReserveExperimentSplice ∘ (fun p ↦ originalReserveMainSamplerReadout q θ hθ1 p.1)) = _
  have hm : Measurable (fun p : OriginalReserveUnitExperimentSpace q × TwoMarkedCloudSpace q ℝ ℝ ↦
      originalReserveMainSamplerReadout q θ hθ1 p.1) :=
    (measurable_originalReserveMainSamplerReadout q θ hθ1).comp measurable_fst
  rw [← Measure.map_map h hm, X.fullLaw_main_sampler]
  exact map_originalSourceReserveExperimentSplice_product _ α β _

/-- The target factorization retains the same main and original source reserve. -/
theorem fullLaw_target_sampler :
    (X.fullLaw : Measure (OriginalReserveUnitExperimentSpace q × TwoMarkedCloudSpace q ℝ ℝ)).map
      (originalReserveUnitTargetSamplerView q θ hθ1) =
      (((legalMarkedInputDilationLaw q (legalIntensityDilation q (1 - θ))
        (legalIntensityDilation_pos q (sub_pos.mpr hθ1)).ne' Main.law : Measure (LegalMarkedOptimalInputScene q)).prod
      (markedPoissonLaw q ℝ α (Real.toNNReal θ *
        (volume (originalCenteredPhysicalCubeRegion b (2 * R))).toNNReal))).prod
      (markedPoissonLaw q ℝ β (Real.toNNReal θ *
        (volume (originalCenteredPhysicalCubeRegion b (2 * R))).toNNReal))) := by
  have h : Measurable (originalTargetReserveExperimentSplice (q := q)) := by
    unfold originalTargetReserveExperimentSplice
    fun_prop
  change (X.fullLaw : Measure (OriginalReserveUnitExperimentSpace q × TwoMarkedCloudSpace q ℝ ℝ)).map
    (originalTargetReserveExperimentSplice ∘ (fun p ↦ originalReserveMainSamplerReadout q θ hθ1 p.1)) = _
  have hm : Measurable (fun p : OriginalReserveUnitExperimentSpace q × TwoMarkedCloudSpace q ℝ ℝ ↦
      originalReserveMainSamplerReadout q θ hθ1 p.1) :=
    (measurable_originalReserveMainSamplerReadout q θ hθ1).comp measurable_fst
  rw [← Measure.map_map h hm, X.fullLaw_main_sampler]
  exact map_originalTargetReserveExperimentSplice_product _ α β _

/-- The actual source block-kept fibre in the same full experiment has
its exact iid spatial law; the auxiliary excludes own reserve positions. -/
theorem source_blockSelection_jointLaw {K : Set (Fin q → ℝ)} (hK : MeasurableSet K)
    {S T C : Set ℝ} (hS : MeasurableSet S) (hT : MeasurableSet T) (hC : MeasurableSet C) (k : ℕ) :
    let rate := Real.toNNReal θ * (volume (originalCenteredPhysicalCubeRegion b (2 * R))).toNNReal
    let P := (legalMarkedInputDilationLaw q (legalIntensityDilation q (1 - θ))
      (legalIntensityDilation_pos q (sub_pos.mpr hθ1)).ne' Main.law : Measure (LegalMarkedOptimalInputScene q)).prod
        (markedPoissonLaw q ℝ β rate)
    ((X.fullLaw : Measure (OriginalReserveUnitExperimentSpace q × TwoMarkedCloudSpace q ℝ ℝ)).restrict
      {p | (originalReserveBlockKept K 0 1 S T C (originalReserveExcessInputAux
        (originalReserveUnitSourceSamplerView q θ hθ1 p))).card = k}).map
      (originalReserveBlockInputReadout K 0 1 S T C k ∘ originalReserveUnitSourceSamplerView q θ hθ1) =
      ((P.prod (originalReserveCountMarkLaw α rate)).restrict
        {z | (originalReserveBlockKept K 0 1 S T C z).card = k}).prod
          (Measure.pi (fun _ : Fin k ↦ cubeMeasure (Fin q) 1)) := by
  dsimp only
  exact map_originalReserveBlockSelection_pullback _ _ α _
    (originalReserveUnitSourceSamplerView q θ hθ1)
    (measurable_originalReserveUnitSourceSamplerView q θ hθ1) X.fullLaw_source_sampler
    hK 0 1 hS hT hC k

/-- The actual target block-kept fibre in the same full experiment has
its exact iid spatial law; the auxiliary excludes own reserve positions. -/
theorem target_blockSelection_jointLaw {K : Set (Fin q → ℝ)} (hK : MeasurableSet K)
    {S T C : Set ℝ} (hS : MeasurableSet S) (hT : MeasurableSet T) (hC : MeasurableSet C) (k : ℕ) :
    let rate := Real.toNNReal θ * (volume (originalCenteredPhysicalCubeRegion b (2 * R))).toNNReal
    let P := (legalMarkedInputDilationLaw q (legalIntensityDilation q (1 - θ))
      (legalIntensityDilation_pos q (sub_pos.mpr hθ1)).ne' Main.law : Measure (LegalMarkedOptimalInputScene q)).prod
        (markedPoissonLaw q ℝ α rate)
    ((X.fullLaw : Measure (OriginalReserveUnitExperimentSpace q × TwoMarkedCloudSpace q ℝ ℝ)).restrict
      {p | (originalReserveBlockKept K 1 0 S T C (originalReserveExcessInputAux
        (originalReserveUnitTargetSamplerView q θ hθ1 p))).card = k}).map
      (originalReserveBlockInputReadout K 1 0 S T C k ∘ originalReserveUnitTargetSamplerView q θ hθ1) =
      ((P.prod (originalReserveCountMarkLaw β rate)).restrict
        {z | (originalReserveBlockKept K 1 0 S T C z).card = k}).prod
          (Measure.pi (fun _ : Fin k ↦ cubeMeasure (Fin q) 1)) := by
  dsimp only
  exact map_originalReserveBlockSelection_pullback _ _ β _
    (originalReserveUnitTargetSamplerView q θ hθ1)
    (measurable_originalReserveUnitTargetSamplerView q θ hθ1) X.fullLaw_target_sampler
    hK 1 0 hS hT hC k

end OriginalReserveFullUnitInputExperiment
end OTSelector.Reconstruction
