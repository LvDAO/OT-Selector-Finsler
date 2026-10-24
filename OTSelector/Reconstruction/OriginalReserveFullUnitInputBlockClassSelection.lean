import OTSelector.Reconstruction.OriginalReserveFullUnitInputBlockSelection
import OTSelector.Reconstruction.OriginalMarkSelectedPopulationCouplingBlockClassSelection

/-! Fine-stage reserve iid laws after actual block deletion in the same full unit-input joining. -/
open Set Function MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators Classical
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-- Read the actual marks-only block selector at unchanged original iid coordinates. -/
def originalReserveBlockClassInputReadout {q : ℕ} (K : Set (Fin q → ℝ))
    (own other : Fin 2) (S T C D : Set ℝ) (k : ℕ)
    (p : (LegalMarkedOptimalInputScene q × MarkedCloudSpace q ℝ) × MarkedCloudSpace q ℝ) :
    OriginalReserveSceneAux q × (Fin k → (Fin q → ℝ)) :=
  (originalReserveExcessInputAux p, fun j ↦
    (p.2.2 (originalReserveBlockClassSelection K own other S T C D k (originalReserveExcessInputAux p) j)).1)

/-- Measurability is produced from the actual block counts, marks and original indices. -/
theorem measurable_originalReserveBlockClassInputReadout {q : ℕ} {K : Set (Fin q → ℝ)}
    (hK : MeasurableSet K) (own other : Fin 2) {S T C D : Set ℝ}
    (hS : MeasurableSet S) (hT : MeasurableSet T) (hC : MeasurableSet C) (hD : MeasurableSet D) (k : ℕ) :
    Measurable (originalReserveBlockClassInputReadout K own other S T C D k) := by
  have haux : Measurable (originalReserveExcessInputAux (q := q)) := by
    unfold originalReserveExcessInputAux
    fun_prop
  have hpositions : Measurable (fun p :
      (LegalMarkedOptimalInputScene q × MarkedCloudSpace q ℝ) × MarkedCloudSpace q ℝ ↦
      fun i ↦ (p.2.2 i).1) := by fun_prop
  have heval : Measurable (fun p : ℕ × (ℕ → (Fin q → ℝ)) ↦ p.2 p.1) :=
    measurable_from_prod_countable_right (fun i ↦ measurable_pi_apply i)
  exact haux.prodMk (measurable_pi_lambda _ (fun j ↦ heval.comp
    (((measurable_originalReserveBlockClassSelection_apply hK own other hS hT hC hD k j).comp haux).prodMk hpositions)))

/-- The true kept-count event uses no own reserve positions. -/
theorem measurableSet_originalReserveBlockClassKept_card {q : ℕ} {K : Set (Fin q → ℝ)}
    (hK : MeasurableSet K) (own other : Fin 2) {S T C D : Set ℝ}
    (hS : MeasurableSet S) (hT : MeasurableSet T) (hC : MeasurableSet C) (hD : MeasurableSet D) (k : ℕ) :
    MeasurableSet {z : OriginalReserveSceneAux q | (originalReserveBlockClassKept K own other S T C D z).card = k} :=
  (measurableSet_singleton k).preimage ((measurable_of_countable (fun s : Finset ℕ ↦ s.card)).comp
    (measurable_originalReserveBlockClassKept hK own other hS hT hC hD))

/-- An established sampler marginal gives the actual block-kept iid law on the
same original experiment, including the zero-count fibre. No joint law of
whole-input or full-array witnesses with own positions is imposed. -/
theorem map_originalReserveBlockClassSelection_pullback {q : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (J : Measure Ω)
    (P : Measure (LegalMarkedOptimalInputScene q × MarkedCloudSpace q ℝ)) [IsFiniteMeasure P]
    (α : Measure ℝ) [IsProbabilityMeasure α] (rate : ℝ≥0)
    (f : Ω → (LegalMarkedOptimalInputScene q × MarkedCloudSpace q ℝ) × MarkedCloudSpace q ℝ)
    (hf : Measurable f) (hlaw : J.map f = P.prod (markedPoissonLaw q ℝ α rate))
    {K : Set (Fin q → ℝ)} (hK : MeasurableSet K) (own other : Fin 2)
    {S T C D : Set ℝ} (hS : MeasurableSet S) (hT : MeasurableSet T) (hC : MeasurableSet C) (hD : MeasurableSet D) (k : ℕ) :
    (J.restrict {p | (originalReserveBlockClassKept K own other S T C D
      (originalReserveExcessInputAux (f p))).card = k}).map
      (originalReserveBlockClassInputReadout K own other S T C D k ∘ f) =
      ((P.prod (originalReserveCountMarkLaw α rate)).restrict
        {z | (originalReserveBlockClassKept K own other S T C D z).card = k}).prod
          (Measure.pi (fun _ : Fin k ↦ cubeMeasure (Fin q) 1)) := by
  have haux : Measurable (originalReserveExcessInputAux (q := q)) := by
    unfold originalReserveExcessInputAux
    fun_prop
  have hE : MeasurableSet {p : (LegalMarkedOptimalInputScene q × MarkedCloudSpace q ℝ) × MarkedCloudSpace q ℝ |
      (originalReserveBlockClassKept K own other S T C D (originalReserveExcessInputAux p)).card = k} :=
    (measurableSet_originalReserveBlockClassKept_card hK own other hS hT hC hD k).preimage haux
  change (J.restrict (f ⁻¹' {p | (originalReserveBlockClassKept K own other S T C D
    (originalReserveExcessInputAux p)).card = k})).map
      (originalReserveBlockClassInputReadout K own other S T C D k ∘ f) = _
  rw [← Measure.map_map (measurable_originalReserveBlockClassInputReadout hK own other hS hT hC hD k) hf,
    ← Measure.restrict_map hf hE, hlaw]
  exact map_originalReserveBlockClassSelection_actual_jointLaw P α rate hK own other hS hT hC hD k

namespace OriginalReserveFullUnitInputExperiment
variable {q : ℕ} {α β : Measure ℝ} [IsProbabilityMeasure α] [IsProbabilityMeasure β]
  {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
  {Main Reserve : LegalWeightedStationaryPoissonMatching q α β kin g}
  {b : OrthonormalBasis (Fin q) ℝ (EuclideanSpace ℝ (Fin q))}
  {θ R : ℝ} {hθ : 0 < θ} {hθ1 : θ < 1}
  (X : OriginalReserveFullUnitInputExperiment Main Reserve b θ hθ hθ1 R)

/-- The actual source block-kept fibre in the same full experiment has
its exact iid spatial law; the auxiliary excludes own reserve positions. -/
theorem source_blockClassSelection_jointLaw {K : Set (Fin q → ℝ)} (hK : MeasurableSet K)
    {S T C D : Set ℝ} (hS : MeasurableSet S) (hT : MeasurableSet T) (hC : MeasurableSet C) (hD : MeasurableSet D) (k : ℕ) :
    let rate := Real.toNNReal θ * (volume (originalCenteredPhysicalCubeRegion b (2 * R))).toNNReal
    let P := (legalMarkedInputDilationLaw q (legalIntensityDilation q (1 - θ))
      (legalIntensityDilation_pos q (sub_pos.mpr hθ1)).ne' Main.law : Measure (LegalMarkedOptimalInputScene q)).prod
        (markedPoissonLaw q ℝ β rate)
    ((X.fullLaw : Measure (OriginalReserveUnitExperimentSpace q × TwoMarkedCloudSpace q ℝ ℝ)).restrict
      {p | (originalReserveBlockClassKept K 0 1 S T C D (originalReserveExcessInputAux
        (originalReserveUnitSourceSamplerView q θ hθ1 p))).card = k}).map
      (originalReserveBlockClassInputReadout K 0 1 S T C D k ∘ originalReserveUnitSourceSamplerView q θ hθ1) =
      ((P.prod (originalReserveCountMarkLaw α rate)).restrict
        {z | (originalReserveBlockClassKept K 0 1 S T C D z).card = k}).prod
          (Measure.pi (fun _ : Fin k ↦ cubeMeasure (Fin q) 1)) := by
  dsimp only
  exact map_originalReserveBlockClassSelection_pullback _ _ α _
    (originalReserveUnitSourceSamplerView q θ hθ1)
    (measurable_originalReserveUnitSourceSamplerView q θ hθ1) X.fullLaw_source_sampler
    hK 0 1 hS hT hC hD k

/-- The actual target block-kept fibre in the same full experiment has
its exact iid spatial law; the auxiliary excludes own reserve positions. -/
theorem target_blockClassSelection_jointLaw {K : Set (Fin q → ℝ)} (hK : MeasurableSet K)
    {S T C D : Set ℝ} (hS : MeasurableSet S) (hT : MeasurableSet T) (hC : MeasurableSet C) (hD : MeasurableSet D) (k : ℕ) :
    let rate := Real.toNNReal θ * (volume (originalCenteredPhysicalCubeRegion b (2 * R))).toNNReal
    let P := (legalMarkedInputDilationLaw q (legalIntensityDilation q (1 - θ))
      (legalIntensityDilation_pos q (sub_pos.mpr hθ1)).ne' Main.law : Measure (LegalMarkedOptimalInputScene q)).prod
        (markedPoissonLaw q ℝ α rate)
    ((X.fullLaw : Measure (OriginalReserveUnitExperimentSpace q × TwoMarkedCloudSpace q ℝ ℝ)).restrict
      {p | (originalReserveBlockClassKept K 1 0 S T C D (originalReserveExcessInputAux
        (originalReserveUnitTargetSamplerView q θ hθ1 p))).card = k}).map
      (originalReserveBlockClassInputReadout K 1 0 S T C D k ∘ originalReserveUnitTargetSamplerView q θ hθ1) =
      ((P.prod (originalReserveCountMarkLaw β rate)).restrict
        {z | (originalReserveBlockClassKept K 1 0 S T C D z).card = k}).prod
          (Measure.pi (fun _ : Fin k ↦ cubeMeasure (Fin q) 1)) := by
  dsimp only
  exact map_originalReserveBlockClassSelection_pullback _ _ β _
    (originalReserveUnitTargetSamplerView q θ hθ1)
    (measurable_originalReserveUnitTargetSamplerView q θ hθ1) X.fullLaw_target_sampler
    hK 1 0 hS hT hC hD k

end OriginalReserveFullUnitInputExperiment
end OTSelector.Reconstruction
