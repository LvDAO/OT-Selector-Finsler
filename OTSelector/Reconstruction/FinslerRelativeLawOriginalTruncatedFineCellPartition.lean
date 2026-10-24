import OTSelector.Reconstruction.FinslerRelativeLawOriginalFineRetainedProperties
import OTSelector.Reconstruction.FinslerRelativeLawOriginalFineFullRetention
import OTSelector.Reconstruction.FinslerRelativeLawOriginalFineDeterministicCellTags

/-! Every deterministic truncation keeps the fixed original macrocells as its fine retained partition. -/
open Set Function MeasureTheory
open scoped BigOperators Classical
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

/-- Complete original marks and retained physical coverage give the exact fine
residual/cell partition, without replacing the original cell family. -/
theorem fineOriginalRetainedCellTag_none_iff_of_cover
    {X Z C T : Type*} [Fintype T] [DecidableEq T]
    (a : X → Z) (cell : C → Set Z) (p : X × Option (CellRefinedType C T))
    (hproper : ∃ tag, p.2 = some tag)
    (hcover : subplanRetentionFlag (p.2.map cellRefinedSubplanType) = false →
      a p.1 ∈ ⋃ c, cell c) :
    fineOriginalRetainedCellTag a cell p = none ↔ cellRefinedResidualTag p.2 := by
  unfold fineOriginalRetainedCellTag
  rw [originalRetainedCellTag_none_iff a cell
    (PopulationTypedCostData.selectedSubplanTags (T := T)) _ ?_]
  · exact cellRefinedSubplanType_mem_selected_iff p.2
  · intro hn
    apply hcover
    obtain ⟨tag, hp⟩ := hproper
    rcases tag with ⟨flag,t⟩ | ⟨c,t⟩
    · cases flag <;> simp [hp, cellRefinedSubplanType, subplanRetentionFlag,
        PopulationTypedCostData.selectedSubplanTags] at *
    · simp [hp, cellRefinedSubplanType, subplanRetentionFlag]

/-- Actual RN truncations inherit the fixed original physical partition on all
fine indices. This uses the original common label and base retained cover,
with the same good/bad/old-type marks supplied by the compact producer. -/
theorem PopulationTypedCostData.original_truncated_fine_cell_partition
    {X Z C T : Type*} [MeasurableSpace X] [MeasurableSpace Z]
    [Fintype C] [Fintype T] [DecidableEq T]
    [MeasurableSpace (Option (CellRefinedType C T))]
    [MeasurableSingletonClass (Option (CellRefinedType C T))]
    (χ ξ : Measure (X × X)) [IsFiniteMeasure χ] [IsFiniteMeasure ξ]
    {μ ν : Measure X} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {q : ℕ} {cost : X → X → ℝ} (D : PopulationTypedCostData (χ + ξ) μ ν T q cost)
    (hπ : Vlasov.IsCoupling (χ + ξ) μ ν)
    (a : X → Z) (ha : Measurable a) {G : Set Z} (hG : MeasurableSet G)
    (cell : C → Set Z) (hcell : ∀ c, MeasurableSet (cell c))
    (hcover : ∀ᵐ p ∂χ, a p.1 ∈ ⋃ c, cell c)
    (hlabel : ∀ᵐ p ∂χ + ξ, a p.1 = a p.2)
    (good : T → Measure (X × X)) (bad : C → T → Measure (X × X))
    (hsplit : ∀ t, good t + ∑ c, bad c t =
      (D.types.rnSubplanTypes (restrictOriginalRetainedResidual χ ξ a G)
        (restrictOriginalRetainedResidual_le χ ξ a ha hG)).component (false, t)) (n : ℕ) :
    let η := restrictOriginalRetainedResidual χ ξ a G
    let hη := restrictOriginalRetainedResidual_le χ ξ a ha hG
    let R := D.types.rnCellRefinedTypes η hη good bad hsplit
    let P := (Measure.pi (fun _ : Fin n ↦ R.sourceMarkedLaw μ)).prod
      (Measure.pi (fun _ : Fin n ↦ R.targetMarkedLaw ν))
    ∀ᵐ sample ∂P,
      (∀ i, fineOriginalRetainedCellTag a cell (sample.1 i) = none ↔
        cellRefinedResidualTag (sample.1 i).2) ∧
      (∀ j, fineOriginalRetainedCellTag a cell (sample.2 j) = none ↔
        cellRefinedResidualTag (sample.2 j).2) := by
  have hs : ∀ᵐ x ∂χ.map Prod.fst, a x ∈ ⋃ c, cell c :=
    (ae_map_iff measurable_fst.aemeasurable (ha (MeasurableSet.iUnion hcell))).mpr hcover
  have ht : ∀ᵐ y ∂χ.map Prod.snd, a y ∈ ⋃ c, cell c := by
    apply (ae_map_iff measurable_snd.aemeasurable (ha (MeasurableSet.iUnion hcell))).mpr
    filter_upwards [hcover, ae_mono (Measure.le_add_right le_rfl) hlabel] with p hp hl
    exact hl ▸ hp
  have hret := D.original_truncated_fine_retained_endpoint_properties χ ξ a ha hG
    good bad hsplit (fun x ↦ a x ∈ ⋃ c, cell c) (fun y ↦ a y ∈ ⋃ c, cell c) hs ht
    (I := Fin n) (J := Fin n)
  have hproper := D.rnCellRefinedTypes_iid_some _ _ good bad hsplit hπ (I := Fin n) (J := Fin n)
  filter_upwards [hret, hproper] with sample hr hp
  exact ⟨fun i ↦ fineOriginalRetainedCellTag_none_iff_of_cover a cell (sample.1 i) (hp.1 i) (hr.1 i),
    fun j ↦ fineOriginalRetainedCellTag_none_iff_of_cover a cell (sample.2 j) (hp.2 j) (hr.2 j)⟩

end OTSelector.Reconstruction
