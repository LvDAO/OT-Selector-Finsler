import OTSelector.Reconstruction.FinslerRelativeLawOriginalFineSourceCounts
import OTSelector.Reconstruction.FinslerRelativeLawOriginalFineDeterministicCellTags

/-! Actual good and bad observed cores form one physical retained-cell family on original indices. -/
open Set Function
open scoped BigOperators Classical
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false

/-- Every present literal original cell contributes exactly one source vertex. -/
theorem sum_partitionCount_some {C : Type*} [Fintype C] {n : ℕ}
    (tag : Fin n → Option C) :
    (∑ c, partitionCount tag (some c)) = ∑ i, if (tag i).isSome then (1 : ℝ) else 0 := by
  classical
  unfold partitionCount
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  cases tag i <;> simp [partitionIndicator]

/-- On every full original fine sample the physical retained cells count exactly
the good and bad observed vertices, including arbitrary adaptive later selections. -/
theorem sum_fine_retained_cell_source_count {C T : Type*} [Fintype C] [Fintype T]
    {n : ℕ} (tag : Fin n → Option (CellRefinedType C T)) (sourceCell : Fin n → Option C)
    (hproper : ∀ i, ∃ p, tag i = some p)
    (hcell : ∀ i, sourceCell i = none ↔ cellRefinedResidualTag (tag i)) :
    (∑ c, partitionCount sourceCell (some c)) =
      (∑ t ∈ presentTypeTags T, partitionCount (fun i ↦ (tag i).bind cellRefinedGoodType) t) +
      (∑ t ∈ presentTypeTags (C × T),
        partitionCount (fun i ↦ (tag i).bind cellRefinedBadType) t) := by
  rw [← cellRefined_retained_source_count_eq_good_add_bad, sum_partitionCount_some]
  unfold partitionCount
  apply Finset.sum_congr rfl
  intro i _
  dsimp only
  obtain ⟨p, hp⟩ := hproper i
  have hc := hcell i
  rw [hp] at hc ⊢
  cases p with
  | inl p =>
    rcases p with ⟨b, t⟩
    cases b <;> cases h : sourceCell i <;>
      simp_all [cellRefinedResidualTag, cellRefinedSubplanType, subplanRetentionFlag,
        partitionIndicator]
  | inr p =>
    cases h : sourceCell i <;>
      simp_all [cellRefinedResidualTag, cellRefinedSubplanType, subplanRetentionFlag,
        partitionIndicator]

section CoreAssembly

variable {X Y Z C T : Type*} [Fintype C] [Fintype T] [DecidableEq T] {m n : ℕ}
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
    (hbadSource : ∀ i c t, (source i).2.bind cellRefinedBadType = some (c, t) →
      fineOriginalRetainedCellTag left cell (source i) = some c)
    (hbadTarget : ∀ j c t, (target j).2.bind cellRefinedBadType = some (c, t) →
      fineOriginalRetainedCellTag right cell (target j) = some c)

include hg hb hbadSource hbadTarget

omit [Fintype C] in
/-- The two actual cores merge on unchanged original indices and remain in their
literal physical retained cells. Signed costs and cardinalities add exactly. -/
theorem exists_original_good_bad_same_cell_union_with_edges :
    ∃ core : OTSelector.PartialMatching m n,
      core.edges = good.edges ∪ bad.edges ∧ core.card = good.card + bad.card ∧
      (∀ cost : Fin m → Fin n → ℝ, core.cost cost = good.cost cost + bad.cost cost) ∧
      ∀ e ∈ core.edges, ∃ c,
        fineOriginalRetainedCellTag left cell (source e.1) = some c ∧
          fineOriginalRetainedCellTag right cell (target e.2) = some c := by
  obtain ⟨core, hedges, hcard, hcost⟩ := exists_fine_good_bad_matching_union
    (fun i ↦ (source i).2) (fun j ↦ (target j).2) good bad
    (fun e he ↦ by
      obtain ⟨t, hs, ht, _⟩ := hg e he
      exact ⟨⟨t, (cellRefinedGoodType_bind_some_iff _ t).mp hs⟩,
        ⟨t, (cellRefinedGoodType_bind_some_iff _ t).mp ht⟩⟩)
    (fun e he ↦ by
      obtain ⟨p, hs, ht⟩ := hb e he
      exact ⟨⟨p, (cellRefinedBadType_bind_some_iff _ p).mp hs⟩,
        ⟨p, (cellRefinedBadType_bind_some_iff _ p).mp ht⟩⟩)
  refine ⟨core, hedges, hcard, hcost, ?_⟩
  intro e he
  rw [hedges] at he
  rcases Finset.mem_union.mp he with he | he
  · obtain ⟨t, hs, ht, c, hsc, htc⟩ := hg e he
    exact ⟨c, (fineOriginalRetainedCellTag_eq_goodCell left cell _ hs).trans hsc,
      (fineOriginalRetainedCellTag_eq_goodCell right cell _ ht).trans htc⟩
  · obtain ⟨p, hs, ht⟩ := hb e he
    exact ⟨p.1, hbadSource e.1 p.1 p.2 hs, hbadTarget e.2 p.1 p.2 ht⟩

omit [Fintype C] in
/-- The merged actual core keeps one physical cell per edge and exactly adds both budgets. -/
theorem exists_original_good_bad_same_cell_union :
    ∃ core : OTSelector.PartialMatching m n,
      core.card = good.card + bad.card ∧
      (∀ cost : Fin m → Fin n → ℝ, core.cost cost = good.cost cost + bad.cost cost) ∧
      ∀ e ∈ core.edges, ∃ c,
        fineOriginalRetainedCellTag left cell (source e.1) = some c ∧
          fineOriginalRetainedCellTag right cell (target e.2) = some c := by
  obtain ⟨core, _, hcard, hcost, hcell⟩ := exists_original_good_bad_same_cell_union_with_edges
    left right cell source target good bad hg hb hbadSource hbadTarget
  exact ⟨core, hcard, hcost, hcell⟩

/-- The actual merged cores supply the retained family required by the full
assignment splice. Its energy is counted once and its source defect is exactly
the sum of the good and bad hierarchy defects. -/
theorem exists_original_good_bad_retained_cell_family
    (hproper : ∀ i, ∃ p, (source i).2 = some p)
    (hpartition : ∀ i, fineOriginalRetainedCellTag left cell (source i) = none ↔
      cellRefinedResidualTag (source i).2) :
    ∃ retained : C → OTSelector.PartialMatching m n,
      (∀ c e, e ∈ (retained c).edges →
        fineOriginalRetainedCellTag left cell (source e.1) = some c ∧
          fineOriginalRetainedCellTag right cell (target e.2) = some c) ∧
      (∀ cost : Fin m → Fin n → ℝ,
        (∑ c, (retained c).cost cost) = good.cost cost + bad.cost cost) ∧
      (∑ c, (partitionCount (fun i ↦ fineOriginalRetainedCellTag left cell (source i))
        (some c) - ((retained c).card : ℝ))) =
          ((∑ t ∈ presentTypeTags T,
            partitionCount (fun i ↦ (source i).2.bind cellRefinedGoodType) t) - good.card) +
          ((∑ t ∈ presentTypeTags (C × T),
            partitionCount (fun i ↦ (source i).2.bind cellRefinedBadType) t) - bad.card) := by
  obtain ⟨core, hcard, hcost, hcells⟩ := exists_original_good_bad_same_cell_union
    left right cell source target good bad hg hb hbadSource hbadTarget
  let sourceCell := fun i ↦ fineOriginalRetainedCellTag left cell (source i)
  have hsource : ∀ e ∈ core.edges, ∃ c, sourceCell e.1 = some c :=
    fun e he ↦ (hcells e he).imp fun _ h ↦ h.1
  refine ⟨fun c ↦ originalMatchingCell core sourceCell c, ?_, ?_, ?_⟩
  · intro c e he
    obtain ⟨hecore, hc⟩ := (mem_originalMatchingCell core sourceCell c e).mp he
    obtain ⟨d, hd, ht⟩ := hcells e hecore
    have hdc : d = c := Option.some.inj (hd.symm.trans hc)
    exact ⟨hc, hdc ▸ ht⟩
  · intro cost
    rw [sum_originalMatchingCell_cost core sourceCell hsource, hcost]
  · rw [sum_originalMatchingCell_source_defect core sourceCell hsource,
      sum_fine_retained_cell_source_count (fun i ↦ (source i).2) sourceCell hproper hpartition,
      hcard, Nat.cast_add]
    ring

end CoreAssembly
end OTSelector.Reconstruction
