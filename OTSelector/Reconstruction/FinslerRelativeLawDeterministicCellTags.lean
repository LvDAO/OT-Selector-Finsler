import OTSelector.Reconstruction.FinslerRelativeLawDeterministicLabelRestriction
import OTSelector.Reconstruction.FinslerRelativeLawRetainedCellLabels

/-! Prescribed microscopic retained labels on the same original marked experiment. -/
open Set Function MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators Classical
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

/-- After prescribed deterministic label truncation, the original finite cell
tags distinguish exactly the true residual. The discarded retained population
is already inside that residual, so no new conditional-kernel or sampled
endpoint-support premise is needed for the full assignment splice. -/
theorem PopulationTypedCostData.original_deterministic_cell_tags_ae
    {X Z C T : Type*} [MetricSpace X] [MeasurableSpace X] [MeasurableSpace Z]
    [Fintype C] [Fintype T] [DecidableEq T]
    [MeasurableSpace (Option (Bool × T))]
    [MeasurableSingletonClass (Option (Bool × T))]
    (χ ξ : Measure (X × X)) [IsFiniteMeasure χ] [IsFiniteMeasure ξ]
    {μ ν : Measure X} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hπ : Vlasov.IsCoupling (χ + ξ) μ ν)
    {q : ℕ} {cost : X → X → ℝ} (D : PopulationTypedCostData (χ + ξ) μ ν T q cost)
    (a : X → Z) (ha : Measurable a) (u : X → ℝ) {A : Set X}
    (horder : ∀ x ∈ A, ∀ y ∈ A, (a x = a y ∧ u x ≤ u y) ↔ u y - u x = dist x y)
    (hμA : ∀ᵐ x ∂μ, x ∈ A) (hνA : ∀ᵐ y ∂ν, y ∈ A)
    (hcal : ∀ᵐ p ∂χ + ξ, u p.2 - u p.1 = dist p.1 p.2)
    (cell : C → Set Z) (hcell : ∀ c, MeasurableSet (cell c)) (n : ℕ) :
    let G := ⋃ c, cell c
    let ξG := restrictOriginalRetainedResidual χ ξ a G
    let hξG : ξG ≤ χ + ξ := restrictOriginalRetainedResidual_le χ ξ a ha (MeasurableSet.iUnion hcell)
    let R := D.refineSubplan ξG hξG
    let selected := PopulationTypedCostData.selectedSubplanTags (T := T)
    ∀ᵐ sample ∂R.markedLaw n,
      (∀ i, originalRetainedCellTag a cell selected (sample.1 i) = none ↔
        (R.sourceSample n i sample).1 ∈ selected) ∧
      (∀ j, originalRetainedCellTag a cell selected (sample.2 j) = none ↔
        (R.targetSample n j sample).1 ∈ selected) := by
  classical
  let G := ⋃ c, cell c
  have hG : MeasurableSet G := MeasurableSet.iUnion hcell
  let ξG := restrictOriginalRetainedResidual χ ξ a G
  let hξG : ξG ≤ χ + ξ := restrictOriginalRetainedResidual_le χ ξ a ha hG
  let R := D.refineSubplan ξG hξG
  let selected := PopulationTypedCostData.selectedSubplanTags (T := T)
  have hlabel : ∀ᵐ p ∂χ, a p.1 = a p.2 :=
    (original_calibrated_coupling_labels μ ν (χ + ξ) χ hπ (Measure.le_add_right le_rfl)
      a u horder hμA hνA hcal).mono fun p hp ↦ hp.1
  have hs : ∀ᵐ x ∂((χ + ξ) - ξG).map Prod.fst, a x ∈ G := by
    apply (ae_map_iff measurable_fst.aemeasurable (ha hG)).mpr
    rw [original_retained_label_restriction_complement χ ξ a ha hG]
    exact ae_restrict_mem ((ha.comp measurable_fst) hG)
  have ht : ∀ᵐ y ∂((χ + ξ) - ξG).map Prod.snd, a y ∈ G := by
    apply (ae_map_iff measurable_snd.aemeasurable (ha hG)).mpr
    rw [original_retained_label_restriction_complement χ ξ a ha hG]
    filter_upwards [ae_restrict_mem ((ha.comp measurable_fst) hG), ae_restrict_of_ae hlabel] with p hp hl
    change a p.1 ∈ G at hp
    exact hl ▸ hp
  have hsFalse : ∀ᵐ p ∂(R.types.sourceMarkedLaw μ).restrict
      {p | subplanRetentionFlag p.2 = false}, a p.1 ∈ G := by
    apply ae_of_ae_map (p := fun x : X ↦ a x ∈ G) measurable_fst.aemeasurable
    rw [(D.refineSubplan_retained_physical_laws ξG hξG).1]
    exact hs
  have htFalse : ∀ᵐ p ∂(R.types.targetMarkedLaw ν).restrict
      {p | subplanRetentionFlag p.2 = false}, a p.1 ∈ G := by
    apply ae_of_ae_map (p := fun x : X ↦ a x ∈ G) measurable_fst.aemeasurable
    rw [(D.refineSubplan_retained_physical_laws ξG hξG).2]
    exact ht
  have hproper := R.types.marked_ae_some_of_sum_eq hπ R.sum_eq
  have hsTag : ∀ᵐ p ∂R.types.sourceMarkedLaw μ,
      originalRetainedCellTag a cell selected p = none ↔ p.2 ∈ selected := by
    filter_upwards [hproper.1, ae_imp_of_ae_restrict hsFalse] with p hp hf
    apply originalRetainedCellTag_none_iff
    intro hn
    obtain ⟨⟨flag, t⟩, hmark⟩ := hp
    cases flag
    · exact hf (by rw [hmark]; rfl)
    · exact False.elim (hn (by simp [selected, selectedSubplanTags, hmark]))
  have htTag : ∀ᵐ p ∂R.types.targetMarkedLaw ν,
      originalRetainedCellTag a cell selected p = none ↔ p.2 ∈ selected := by
    filter_upwards [hproper.2, ae_imp_of_ae_restrict htFalse] with p hp hf
    apply originalRetainedCellTag_none_iff
    intro hn
    obtain ⟨⟨flag, t⟩, hmark⟩ := hp
    cases flag
    · exact hf (by rw [hmark]; rfl)
    · exact False.elim (hn (by simp [selected, selectedSubplanTags, hmark]))
  have hsArray : ∀ᵐ x ∂Measure.pi (fun _ : Fin n ↦ R.types.sourceMarkedLaw μ),
      ∀ i, originalRetainedCellTag a cell selected (x i) = none ↔ (x i).2 ∈ selected :=
    ae_all_iff.mpr fun i ↦ (Measure.quasiMeasurePreserving_eval
      (fun _ : Fin n ↦ R.types.sourceMarkedLaw μ) i).ae hsTag
  have htArray : ∀ᵐ y ∂Measure.pi (fun _ : Fin n ↦ R.types.targetMarkedLaw ν),
      ∀ j, originalRetainedCellTag a cell selected (y j) = none ↔ (y j).2 ∈ selected :=
    ae_all_iff.mpr fun j ↦ (Measure.quasiMeasurePreserving_eval
      (fun _ : Fin n ↦ R.types.targetMarkedLaw ν) j).ae htTag
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae hsArray,
    Measure.quasiMeasurePreserving_snd.ae htArray] with sample hs ht
  exact ⟨hs, ht⟩

end OTSelector.Reconstruction
