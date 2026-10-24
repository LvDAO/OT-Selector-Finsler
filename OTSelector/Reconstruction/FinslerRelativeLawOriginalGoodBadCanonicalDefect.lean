import OTSelector.Reconstruction.FinslerRelativeLawOriginalFineCoreAssembly
import OTSelector.Reconstruction.FinslerRelativeLawOriginalCanonicalCellDefect

/-! Actual canonical legal cell optimizers inherit the good/bad hierarchy source-defect budget. -/
open Set Function
open scoped BigOperators Classical
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false

/-- Legal canonical competitors use the actual full retained cells and original
indices. Their total missing source count is bounded by the two genuine good/bad
core defects, without a separate canonical-cardinality or retained-family oracle. -/
theorem original_good_bad_canonical_cell_source_defect_le
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
    (hbadSource : ∀ i c t, (source i).2.bind cellRefinedBadType = some (c, t) →
      fineOriginalRetainedCellTag left cell (source i) = some c)
    (hbadTarget : ∀ j c t, (target j).2.bind cellRefinedBadType = some (c, t) →
      fineOriginalRetainedCellTag right cell (target j) = some c)
    (hproper : ∀ i, ∃ p, (source i).2 = some p)
    (hpartition : ∀ i, fineOriginalRetainedCellTag left cell (source i) = none ↔
      cellRefinedResidualTag (source i).2)
    (allowed : C → Finset (Fin m × Fin n)) (score : C → Fin m → Fin n → ℝ)
    (hgoodLegal : ∀ c e, e ∈ good.edges →
      fineOriginalRetainedCellTag left cell (source e.1) = some c → e ∈ allowed c)
    (hbadLegal : ∀ c e, e ∈ bad.edges →
      fineOriginalRetainedCellTag left cell (source e.1) = some c → e ∈ allowed c) :
    let sourceCell := fun i ↦ fineOriginalRetainedCellTag left cell (source i)
    let targetCell := fun j ↦ fineOriginalRetainedCellTag right cell (target j)
    (∑ c, (partitionCount sourceCell (some c) -
      ((PartialMatching.firstLegalOptimalMatching
        (originalAmbientCellLegalGraph sourceCell targetCell allowed c) (score c)).card : ℝ))) ≤
      ((∑ t ∈ presentTypeTags T,
        partitionCount (fun i ↦ (source i).2.bind cellRefinedGoodType) t) - good.card) +
      ((∑ t ∈ presentTypeTags (C × T),
        partitionCount (fun i ↦ (source i).2.bind cellRefinedBadType) t) - bad.card) := by
  obtain ⟨core, hedges, hcard, _, hcells⟩ := exists_original_good_bad_same_cell_union_with_edges
    left right cell source target good bad hg hb hbadSource hbadTarget
  let sourceCell := fun i ↦ fineOriginalRetainedCellTag left cell (source i)
  let targetCell := fun j ↦ fineOriginalRetainedCellTag right cell (target j)
  let pieces := fun c ↦ originalMatchingCell core sourceCell c
  have hsource : ∀ e ∈ core.edges, ∃ c, sourceCell e.1 = some c :=
    fun e he ↦ (hcells e he).imp fun _ h ↦ h.1
  have hpiece : ∀ c e, e ∈ (pieces c).edges →
      sourceCell e.1 = some c ∧ targetCell e.2 = some c := by
    intro c e he
    obtain ⟨hecore, hc⟩ := (mem_originalMatchingCell core sourceCell c e).mp he
    obtain ⟨d, hd, ht⟩ := hcells e hecore
    have hdc : d = c := Option.some.inj (hd.symm.trans hc)
    exact ⟨hc, hdc ▸ ht⟩
  have hlegal : ∀ c, PartialMatching.IsLegal (allowed c) (pieces c) := by
    intro c e he
    obtain ⟨hecore, hc⟩ := (mem_originalMatchingCell core sourceCell c e).mp he
    rw [hedges] at hecore
    rcases Finset.mem_union.mp hecore with hegood | hebad
    · exact hgoodLegal c e hegood hc
    · exact hbadLegal c e hebad hc
  have hdefect :
      (∑ c, (partitionCount sourceCell (some c) - ((pieces c).card : ℝ))) ≤
        ((∑ t ∈ presentTypeTags T,
          partitionCount (fun i ↦ (source i).2.bind cellRefinedGoodType) t) - good.card) +
        ((∑ t ∈ presentTypeTags (C × T),
          partitionCount (fun i ↦ (source i).2.bind cellRefinedBadType) t) - bad.card) := by
    change (∑ c, (partitionCount sourceCell (some c) -
      ((originalMatchingCell core sourceCell c).card : ℝ))) ≤ _
    rw [sum_originalMatchingCell_source_defect core sourceCell hsource,
      sum_fine_retained_cell_source_count (fun i ↦ (source i).2) sourceCell hproper hpartition,
      hcard, Nat.cast_add]
    exact le_of_eq (by ring)
  dsimp only
  exact sum_original_cell_firstLegalOptimalMatching_defect_le sourceCell targetCell
    allowed score pieces hpiece hlegal hdefect

end OTSelector.Reconstruction
