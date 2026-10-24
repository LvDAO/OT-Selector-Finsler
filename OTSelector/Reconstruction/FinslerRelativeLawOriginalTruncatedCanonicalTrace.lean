import OTSelector.Reconstruction.FinslerRelativeLawOriginalCellOptimizer
import OTSelector.Reconstruction.FinslerRelativeLawOriginalRetainedCompactRestriction
import OTSelector.Reconstruction.FinslerRelativeLawGlobalRetainedCell

/-! Tracing fixed original cells preserves their exact canonical optimizers. -/
open Set Function MeasureTheory ProbabilityTheory
open scoped BigOperators Classical
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false

/-- On a retained original sample whose two endpoint labels lie in `G`, tracing
all fixed cells by `G` leaves every finite graph literally unchanged. -/
theorem originalRetainedCellGraph_trace_eq
    {X Z C T : Type*} {n : ℕ} (a : X → Z) (cell : C → Set Z) (G : Set Z)
    (extra : C → ((Fin n → X × Option (Bool × T)) × (Fin n → X × Option (Bool × T))) →
      Finset (Fin n × Fin n))
    (sample : (Fin n → X × Option (Bool × T)) × (Fin n → X × Option (Bool × T)))
    (hs : ∀ i, subplanRetentionFlag (sample.1 i).2 = false → a (sample.1 i).1 ∈ G)
    (ht : ∀ j, subplanRetentionFlag (sample.2 j).2 = false → a (sample.2 j).1 ∈ G) (c : C) :
    originalRetainedCellGraph a (fun c ↦ cell c ∩ G) extra c sample =
      originalRetainedCellGraph a cell extra c sample := by
  ext e
  simp only [originalRetainedCellGraph, Finset.mem_filter, mem_inter_iff]
  constructor
  · rintro ⟨he,hsf,htf,hsc,htc⟩
    exact ⟨he,hsf,htf,hsc.1,htc.1⟩
  · rintro ⟨he,hsf,htf,hsc,htc⟩
    exact ⟨he,hsf,htf,⟨hsc,hs e.1 hsf⟩,⟨htc,ht e.2 htf⟩⟩

namespace PopulationTypedCostData

/-- The actual original deterministic restriction puts every flag-false endpoint
inside `G`, simultaneously on the unchanged original iid marked arrays. -/
theorem original_truncated_retained_endpoint_labels
    {X Z T : Type*} [MeasurableSpace X] [MeasurableSpace Z] [Fintype T]
    [MeasurableSpace (Option (Bool × T))] [MeasurableSingletonClass (Option (Bool × T))]
    (χ ξ : Measure (X × X)) [IsFiniteMeasure χ] [IsFiniteMeasure ξ]
    {μ ν : Measure X} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {q : ℕ} {cost : X → X → ℝ} (D : PopulationTypedCostData (χ + ξ) μ ν T q cost)
    (a : X → Z) (ha : Measurable a) {G : Set Z} (hG : MeasurableSet G)
    (hlabel : ∀ᵐ p ∂χ, a p.1 = a p.2) (n : ℕ) :
    let η := restrictOriginalRetainedResidual χ ξ a G
    let hη := restrictOriginalRetainedResidual_le χ ξ a ha hG
    ∀ᵐ sample ∂(D.refineSubplan η hη).markedLaw n,
      (∀ i, subplanRetentionFlag (sample.1 i).2 = false → a (sample.1 i).1 ∈ G) ∧
      (∀ j, subplanRetentionFlag (sample.2 j).2 = false → a (sample.2 j).1 ∈ G) := by
  let η := restrictOriginalRetainedResidual χ ξ a G
  let hη := restrictOriginalRetainedResidual_le χ ξ a ha hG
  let R := D.refineSubplan η hη
  have hraw : ∀ᵐ p ∂((χ + ξ) - η), a p.1 ∈ G ∧ a p.2 ∈ G := by
    rw [original_retained_label_restriction_complement χ ξ a ha hG]
    filter_upwards [ae_restrict_mem ((ha.comp measurable_fst) hG),
      ae_mono Measure.restrict_le_self hlabel] with p hp heq
    exact ⟨hp,heq ▸ hp⟩
  have hs : ∀ᵐ p ∂(R.types.sourceMarkedLaw μ).restrict
      {p | subplanRetentionFlag p.2 = false}, a p.1 ∈ G := by
    apply ae_of_ae_map (p := fun x : X ↦ a x ∈ G) measurable_fst.aemeasurable
    rw [(D.refineSubplan_retained_physical_laws η hη).1]
    exact (ae_map_iff measurable_fst.aemeasurable (ha hG)).mpr (hraw.mono fun _ h ↦ h.1)
  have ht : ∀ᵐ p ∂(R.types.targetMarkedLaw ν).restrict
      {p | subplanRetentionFlag p.2 = false}, a p.1 ∈ G := by
    apply ae_of_ae_map (p := fun x : X ↦ a x ∈ G) measurable_fst.aemeasurable
    rw [(D.refineSubplan_retained_physical_laws η hη).2]
    exact (ae_map_iff measurable_snd.aemeasurable (ha hG)).mpr (hraw.mono fun _ h ↦ h.2)
  have hsArray : ∀ᵐ xs ∂Measure.pi (fun _ : Fin n ↦ R.types.sourceMarkedLaw μ),
      ∀ i, subplanRetentionFlag (xs i).2 = false → a (xs i).1 ∈ G :=
    ae_all_iff.mpr fun i ↦ (Measure.quasiMeasurePreserving_eval
      (fun _ : Fin n ↦ R.types.sourceMarkedLaw μ) i).ae (ae_imp_of_ae_restrict hs)
  have htArray : ∀ᵐ ys ∂Measure.pi (fun _ : Fin n ↦ R.types.targetMarkedLaw ν),
      ∀ j, subplanRetentionFlag (ys j).2 = false → a (ys j).1 ∈ G :=
    ae_all_iff.mpr fun j ↦ (Measure.quasiMeasurePreserving_eval
      (fun _ : Fin n ↦ R.types.targetMarkedLaw ν) j).ae (ae_imp_of_ae_restrict ht)
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae hsArray,
    Measure.quasiMeasurePreserving_snd.ae htArray] with sample hsource htarget
  exact ⟨hsource,htarget⟩

/-- The first exact legal optimizer, including its deterministic tie choice, is
unchanged when fixed original cells are intersected with the prescribed labels. -/
theorem original_truncated_canonical_cell_trace
    {X Z C T : Type*} [MeasurableSpace X] [MeasurableSpace Z] [Fintype T]
    [MeasurableSpace (Option (Bool × T))] [MeasurableSingletonClass (Option (Bool × T))]
    (χ ξ : Measure (X × X)) [IsFiniteMeasure χ] [IsFiniteMeasure ξ]
    {μ ν : Measure X} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {q : ℕ} {cost : X → X → ℝ} (D : PopulationTypedCostData (χ + ξ) μ ν T q cost)
    (a : X → Z) (ha : Measurable a) {G : Set Z} (hG : MeasurableSet G)
    (hlabel : ∀ᵐ p ∂χ, a p.1 = a p.2) (n : ℕ) (cell : C → Set Z)
    (extra : C → ((Fin n → X × Option (Bool × T)) × (Fin n → X × Option (Bool × T))) →
      Finset (Fin n × Fin n))
    (model : C → ((Fin n → X × Option (Bool × T)) × (Fin n → X × Option (Bool × T))) →
      Fin n → Fin n → ℝ) :
    let η := restrictOriginalRetainedResidual χ ξ a G
    let hη := restrictOriginalRetainedResidual_le χ ξ a ha hG
    ∀ᵐ sample ∂(D.refineSubplan η hη).markedLaw n, ∀ c,
      originalRetainedCellOptimizer a (fun c ↦ cell c ∩ G) extra model c sample =
        originalRetainedCellOptimizer a cell extra model c sample := by
  filter_upwards [D.original_truncated_retained_endpoint_labels χ ξ a ha hG hlabel n]
    with sample hs
  intro c
  unfold originalRetainedCellOptimizer
  rw [originalRetainedCellGraph_trace_eq a cell G extra sample hs.1 hs.2 c]

/-- Any physical or frozen score of the same canonical optimizers has exactly
the same original iid mean and integrability after tracing the fixed cells. -/
theorem original_truncated_canonical_trace_integral
    {X Z C T : Type*} [MeasurableSpace X] [MeasurableSpace Z] [Fintype C] [Fintype T]
    [MeasurableSpace (Option (Bool × T))] [MeasurableSingletonClass (Option (Bool × T))]
    (χ ξ : Measure (X × X)) [IsFiniteMeasure χ] [IsFiniteMeasure ξ]
    {μ ν : Measure X} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {q : ℕ} {cost : X → X → ℝ} (D : PopulationTypedCostData (χ + ξ) μ ν T q cost)
    (a : X → Z) (ha : Measurable a) {G : Set Z} (hG : MeasurableSet G)
    (hlabel : ∀ᵐ p ∂χ, a p.1 = a p.2) (n : ℕ) (cell : C → Set Z)
    (extra : C → ((Fin n → X × Option (Bool × T)) × (Fin n → X × Option (Bool × T))) →
      Finset (Fin n × Fin n))
    (model score : C → ((Fin n → X × Option (Bool × T)) × (Fin n → X × Option (Bool × T))) →
      Fin n → Fin n → ℝ) :
    let η := restrictOriginalRetainedResidual χ ξ a G
    let hη := restrictOriginalRetainedResidual_le χ ξ a ha hG
    let law := (D.refineSubplan η hη).markedLaw n
    let traced := fun sample ↦ ∑ c,
      (originalRetainedCellOptimizer a (fun c ↦ cell c ∩ G) extra model c sample).cost (score c sample)
    let original := fun sample ↦ ∑ c,
      (originalRetainedCellOptimizer a cell extra model c sample).cost (score c sample)
    (Integrable traced law ↔ Integrable original law) ∧
      (∫ sample, traced sample ∂law) = (∫ sample, original sample ∂law) := by
  have heq : (fun sample ↦ ∑ c,
      (originalRetainedCellOptimizer a (fun c ↦ cell c ∩ G) extra model c sample).cost (score c sample)) =ᵐ[
        (D.refineSubplan (restrictOriginalRetainedResidual χ ξ a G)
          (restrictOriginalRetainedResidual_le χ ξ a ha hG)).markedLaw n]
      (fun sample ↦ ∑ c,
        (originalRetainedCellOptimizer a cell extra model c sample).cost (score c sample)) := by
    filter_upwards [D.original_truncated_canonical_cell_trace χ ξ a ha hG hlabel n cell extra model]
      with sample hs
    exact Finset.sum_congr rfl fun c _ ↦ congrArg (fun σ ↦ σ.cost (score c sample)) (hs c)
  exact ⟨integrable_congr heq, integral_congr_ae heq⟩

end PopulationTypedCostData
end OTSelector.Reconstruction
