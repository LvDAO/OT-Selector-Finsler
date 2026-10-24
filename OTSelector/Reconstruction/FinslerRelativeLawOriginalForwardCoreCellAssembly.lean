import OTSelector.Reconstruction.FinslerRelativeLawOriginalFineCoreAssembly

/-! Good/bad core assembly retains the original edge ancestry needed for clock legality. -/
open Set Function
open scoped BigOperators Classical
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false

/-- The actual cell family inherits every property of the original good/bad
core edges, while preserving exact total cost and exact source deficiency. -/
theorem exists_original_good_bad_cell_family_with_ancestry
    {X Y Z C T : Type*} [Fintype C] [Fintype T] [DecidableEq T] {m n : ℕ}
    (left : X → Z) (right : Y → Z) (cell : C → Set Z)
    (source : Fin m → X × Option (CellRefinedType C T))
    (target : Fin n → Y × Option (CellRefinedType C T))
    (good bad : OTSelector.PartialMatching m n)
    (hg : ∀ e ∈ good.edges, ∃ t,
      (source e.1).2.bind cellRefinedGoodType = some t ∧
      (target e.2).2.bind cellRefinedGoodType = some t ∧
      ∃ c, cellRefinedGoodCell left cell (source e.1) = some c ∧
        cellRefinedGoodCell right cell (target e.2) = some c)
    (hb : ∀ e ∈ bad.edges, ∃ p : C × T,
      (source e.1).2.bind cellRefinedBadType = some p ∧
        (target e.2).2.bind cellRefinedBadType = some p)
    (hbadSource : ∀ i c t, (source i).2.bind cellRefinedBadType = some (c,t) →
      fineOriginalRetainedCellTag left cell (source i) = some c)
    (hbadTarget : ∀ j c t, (target j).2.bind cellRefinedBadType = some (c,t) →
      fineOriginalRetainedCellTag right cell (target j) = some c)
    (hproper : ∀ i, ∃ tag, (source i).2 = some tag)
    (hpartition : ∀ i, fineOriginalRetainedCellTag left cell (source i) = none ↔
      cellRefinedResidualTag (source i).2) :
    ∃ family : C → OTSelector.PartialMatching m n,
      (∀ c e, e ∈ (family c).edges →
        fineOriginalRetainedCellTag left cell (source e.1) = some c ∧
        fineOriginalRetainedCellTag right cell (target e.2) = some c ∧
        (e ∈ good.edges ∨ e ∈ bad.edges)) ∧
      (∀ cost : Fin m → Fin n → ℝ,
        (∑ c, (family c).cost cost) = good.cost cost + bad.cost cost) ∧
      (∑ c, (partitionCount (fun i ↦ fineOriginalRetainedCellTag left cell (source i))
        (some c) - ((family c).card : ℝ))) =
      ((∑ t ∈ presentTypeTags T,
        partitionCount (fun i ↦ (source i).2.bind cellRefinedGoodType) t) - good.card) +
      ((∑ t ∈ presentTypeTags (C × T),
        partitionCount (fun i ↦ (source i).2.bind cellRefinedBadType) t) - bad.card) := by
  obtain ⟨merged, hedges, hcard, hcost, hcells⟩ :=
    exists_original_good_bad_same_cell_union_with_edges left right cell source target good bad
      hg hb hbadSource hbadTarget
  let sourceCell := fun i ↦ fineOriginalRetainedCellTag left cell (source i)
  have hsource : ∀ e ∈ merged.edges, ∃ c, sourceCell e.1 = some c :=
    fun e he ↦ (hcells e he).imp fun _ h ↦ h.1
  refine ⟨fun c ↦ originalMatchingCell merged sourceCell c, ?_, ?_, ?_⟩
  · intro c e he
    obtain ⟨hem, hc⟩ := (mem_originalMatchingCell merged sourceCell c e).mp he
    obtain ⟨d, hds, hdt⟩ := hcells e hem
    have hdc : d = c := Option.some.inj (hds.symm.trans hc)
    refine ⟨hc, hdc ▸ hdt, ?_⟩
    rw [hedges] at hem
    exact Finset.mem_union.mp hem
  · intro cost
    rw [sum_originalMatchingCell_cost merged sourceCell hsource, hcost]
  · rw [sum_originalMatchingCell_source_defect merged sourceCell hsource,
      sum_fine_retained_cell_source_count (fun i ↦ (source i).2) sourceCell hproper hpartition,
      hcard, Nat.cast_add]
    ring

end OTSelector.Reconstruction
