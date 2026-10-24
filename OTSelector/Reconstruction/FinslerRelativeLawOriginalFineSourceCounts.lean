import OTSelector.Finite.MatchingCellAssembly
import OTSelector.Reconstruction.FinslerRelativeLawOriginalSelectedCoordinateMass
import OTSelector.Reconstruction.FinslerRelativeLawRetainedFlagSampling

/-! Original retained source counts split exactly into good and bad observed type counts. -/
open Set Function
open scoped BigOperators Classical
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false

/-- Summing all present type histograms counts the original marked vertices once. -/
theorem sum_partitionCount_presentTypeTags {T : Type*} [Fintype T] {n : ℕ}
    (tag : Fin n → Option T) :
    (∑ t ∈ presentTypeTags T, partitionCount tag t) =
      ∑ i, if (tag i).isSome then (1 : ℝ) else 0 := by
  classical
  rw [presentTypeTags, Finset.sum_image]
  · unfold partitionCount
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    cases tag i <;> simp [partitionIndicator]
  · intro s _ t _ h
    exact Option.some.inj h

/-- The literal false retained flag counts exactly the good and bad fine marks,
including zero-mass and unmarked cases without any probabilistic premise. -/
theorem cellRefined_retained_source_count_eq_good_add_bad
    {C T : Type*} [Fintype C] [Fintype T] {n : ℕ}
    (tag : Fin n → Option (CellRefinedType C T)) :
    partitionCount (fun i ↦ subplanRetentionFlag ((tag i).map cellRefinedSubplanType)) false =
      (∑ t ∈ presentTypeTags T, partitionCount (fun i ↦ (tag i).bind cellRefinedGoodType) t) +
      (∑ t ∈ presentTypeTags (C × T), partitionCount (fun i ↦ (tag i).bind cellRefinedBadType) t) := by
  classical
  rw [sum_partitionCount_presentTypeTags, sum_partitionCount_presentTypeTags]
  unfold partitionCount
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  cases h : tag i with
  | none => simp [partitionIndicator, h, subplanRetentionFlag]
  | some p =>
    cases p with
    | inl p =>
      rcases p with ⟨b, t⟩
      cases b <;> simp [partitionIndicator, h, subplanRetentionFlag,
        cellRefinedSubplanType, cellRefinedGoodType, cellRefinedBadType]
    | inr p => simp [partitionIndicator, h, subplanRetentionFlag,
        cellRefinedSubplanType, cellRefinedGoodType, cellRefinedBadType]

/-- After merging disjoint good and bad cores, their genuine source deficiencies add exactly. -/
theorem cellRefined_retained_source_defect_eq_good_add_bad
    {C T : Type*} [Fintype C] [Fintype T] {m n : ℕ}
    (tag : Fin m → Option (CellRefinedType C T))
    (good bad : OTSelector.PartialMatching m n) :
    partitionCount (fun i ↦ subplanRetentionFlag ((tag i).map cellRefinedSubplanType)) false -
        ((good.card + bad.card : ℕ) : ℝ) =
      ((∑ t ∈ presentTypeTags T,
        partitionCount (fun i ↦ (tag i).bind cellRefinedGoodType) t) - (good.card : ℝ)) +
      ((∑ t ∈ presentTypeTags (C × T),
        partitionCount (fun i ↦ (tag i).bind cellRefinedBadType) t) - (bad.card : ℝ)) := by
  rw [cellRefined_retained_source_count_eq_good_add_bad, Nat.cast_add]
  ring

/-- Partitioning a retained matching over cells preserves its total genuine source deficiency. -/
theorem sum_originalMatchingCell_source_defect {Cell : Type*} [Fintype Cell]
    {m n : ℕ} (σ : OTSelector.PartialMatching m n) (sourceCell : Fin m → Option Cell)
    (hcell : ∀ e ∈ σ.edges, ∃ c, sourceCell e.1 = some c) :
    (∑ c, (partitionCount sourceCell (some c) -
      ((originalMatchingCell σ sourceCell c).card : ℝ))) =
        (∑ c, partitionCount sourceCell (some c)) - (σ.card : ℝ) := by
  rw [Finset.sum_sub_distrib, ← Nat.cast_sum, sum_originalMatchingCell_card σ sourceCell hcell]

end OTSelector.Reconstruction
