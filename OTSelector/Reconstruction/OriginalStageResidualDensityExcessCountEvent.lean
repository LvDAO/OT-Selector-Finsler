import OTSelector.Reconstruction.OriginalStageResidualDensityExcessIndices

/-! The literal original count event supplies removal capacity and protected reserve slack. -/
open Set Function MeasureTheory
open scoped ENNReal BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OTSelector.Reconstruction
open OTSelector.Probability
namespace OriginalStageExcessRemovalData
variable (A : OriginalStageExcessRemovalData q)

/-- The actual full color excess of the original main-plus-reserve arrays. -/
def delta : ℝ := (A.sourceCount : ℝ) - A.targetCount

/-- The original pre-removal signed reserve prefix, with all original reserve indices. -/
def initialReservePrefix (c : ℝ) : ℝ :=
  originalStageRemainingReservePrefix A.sourceReserve A.targetReserve Finset.univ Finset.univ c

/-- The signed reserve prefix of exactly the kept original indices. -/
def keptReservePrefix (c : ℝ) : ℝ :=
  originalStageRemainingReservePrefix A.sourceReserve A.targetReserve A.sourceKept A.targetKept c

/-- The actual count event before deletion. The threshold is r times the actual cube volume;
all clauses concern original array counts, original mark classes and original prefixes. -/
def countGood (a : ℝ) (properCuts : Set ℝ) : Prop :=
  0 ≤ a ∧ |A.delta| ≤ a ∧
  5 * a ≤ (originalStageRemainingReserveClassCount A.sourceReserve Finset.univ A.firstClass : ℝ) ∧
  5 * a ≤ (originalStageRemainingReserveClassCount A.targetReserve Finset.univ A.lastClass : ℝ) ∧
  ∀ c ∈ properCuts, 5 * a ≤ A.initialReservePrefix c

/-- The positive full excess is bounded by the absolute actual full excess. -/
theorem sourceExcess_le_abs_delta : (A.sourceExcess : ℝ) ≤ |A.delta| := by
  by_cases h : A.targetCount ≤ A.sourceCount
  · rw [sourceExcess, Nat.cast_sub h]
    exact le_abs_self _
  · have hz : A.sourceExcess = 0 := Nat.sub_eq_zero_of_le (le_of_not_ge h)
    rw [hz, Nat.cast_zero]
    exact abs_nonneg _

/-- The negative full excess is bounded by the same actual absolute excess. -/
theorem targetExcess_le_abs_delta : (A.targetExcess : ℝ) ≤ |A.delta| := by
  by_cases h : A.sourceCount ≤ A.targetCount
  · rw [targetExcess, Nat.cast_sub h]
    have hn := neg_le_abs A.delta
    dsimp [delta] at hn ⊢
    linarith
  · have hz : A.targetExcess = 0 := Nat.sub_eq_zero_of_le (le_of_not_ge h)
    rw [hz, Nat.cast_zero]
    exact abs_nonneg _

/-- The pre-removal count event itself supplies capacity in both actual extreme classes. -/
theorem hasCapacity_of_countGood {a : ℝ} {properCuts : Set ℝ}
    (hg : A.countGood a properCuts) : A.hasCapacity := by
  constructor
  · apply Nat.cast_le (α := ℝ).mp
    linarith [A.sourceExcess_le_abs_delta, hg.2.1, hg.2.2.1, hg.1]
  · apply Nat.cast_le (α := ℝ).mp
    linarith [A.targetExcess_le_abs_delta, hg.2.1, hg.2.2.2.1, hg.1]

/-- Actual source removal costs at most its actual number in every reserve prefix; target
removal can only increase the signed prefix. This statement makes no spatial-law assertion. -/
theorem keptReservePrefix_lower_bound (hcap : A.hasCapacity) (c : ℝ) :
    A.initialReservePrefix c - |A.delta| ≤ A.keptReservePrefix c := by
  have hs := originalStageMarkRemoval_count_bounds
    (fun i : Fin A.sourceReserve.1 ↦ (A.sourceReserve.2 i).2) A.firstClass (Iio c) A.sourceExcess
  have ht := originalStageMarkRemoval_count_bounds
    (fun i : Fin A.targetReserve.1 ↦ (A.targetReserve.2 i).2) A.lastClass (Iic c) A.targetExcess
  have hsource :
      (Finset.univ.filter (fun i : Fin A.sourceReserve.1 ↦ (A.sourceReserve.2 i).2 ∈ Iio c)).card ≤
      (A.sourceKept.filter (fun i : Fin A.sourceReserve.1 ↦ (A.sourceReserve.2 i).2 ∈ Iio c)).card + A.sourceExcess := by
    have hd := (A.removal_counts_and_balance hcap).1
    change A.sourceDeleted.card = A.sourceExcess at hd
    have hs := hs.1
    change (Finset.univ.filter (fun i : Fin A.sourceReserve.1 ↦ (A.sourceReserve.2 i).2 ∈ Iio c)).card -
      A.sourceDeleted.card ≤ (A.sourceKept.filter (fun i : Fin A.sourceReserve.1 ↦ (A.sourceReserve.2 i).2 ∈ Iio c)).card at hs
    omega
  have htarget : (A.targetKept.filter (fun i : Fin A.targetReserve.1 ↦ (A.targetReserve.2 i).2 ∈ Iic c)).card ≤
      (Finset.univ.filter (fun i : Fin A.targetReserve.1 ↦ (A.targetReserve.2 i).2 ∈ Iic c)).card := ht.2
  have hsR := Nat.cast_le (α := ℝ).mpr hsource
  have htR := Nat.cast_le (α := ℝ).mpr htarget
  simp only [Nat.cast_add] at hsR
  dsimp [initialReservePrefix, keptReservePrefix, originalStageRemainingReservePrefix,
    originalStageRemainingReserveClassCount]
  linarith [A.sourceExcess_le_abs_delta]

/-- The original count event gives exact color balance, protects both actual extreme classes
by 4a, and protects every proper remaining reserve prefix by 4a after actual deletion. -/
theorem countGood_removal_protection {a : ℝ} {properCuts : Set ℝ}
    (hg : A.countGood a properCuts) :
    A.sourceDeleted.card = A.sourceExcess ∧ A.targetDeleted.card = A.targetExcess ∧
    A.sourceMain.1 + A.sourceKept.card = A.targetMain.1 + A.targetKept.card ∧
    4 * a ≤ (originalStageRemainingReserveClassCount A.sourceReserve A.sourceKept A.firstClass : ℝ) ∧
    4 * a ≤ (originalStageRemainingReserveClassCount A.targetReserve A.targetKept A.lastClass : ℝ) ∧
    ∀ c ∈ properCuts, 4 * a ≤ A.keptReservePrefix c := by
  have hcap := A.hasCapacity_of_countGood hg
  have hcounts := A.removal_counts_and_balance hcap
  have hs := originalStageMarkRemoval_own_class_count
    (fun i : Fin A.sourceReserve.1 ↦ (A.sourceReserve.2 i).2) A.firstClass A.sourceExcess
  have ht := originalStageMarkRemoval_own_class_count
    (fun i : Fin A.targetReserve.1 ↦ (A.targetReserve.2 i).2) A.lastClass A.targetExcess
  change originalStageRemainingReserveClassCount A.sourceReserve A.sourceKept A.firstClass =
    originalStageRemainingReserveClassCount A.sourceReserve Finset.univ A.firstClass - A.sourceDeleted.card at hs
  change originalStageRemainingReserveClassCount A.targetReserve A.targetKept A.lastClass =
    originalStageRemainingReserveClassCount A.targetReserve Finset.univ A.lastClass - A.targetDeleted.card at ht
  rw [hcounts.1] at hs
  rw [hcounts.2.1] at ht
  have hsr : (originalStageRemainingReserveClassCount A.sourceReserve A.sourceKept A.firstClass : ℝ) =
      (originalStageRemainingReserveClassCount A.sourceReserve Finset.univ A.firstClass : ℝ) - A.sourceExcess := by
    rw [hs, Nat.cast_sub hcap.1]
  have htr : (originalStageRemainingReserveClassCount A.targetReserve A.targetKept A.lastClass : ℝ) =
      (originalStageRemainingReserveClassCount A.targetReserve Finset.univ A.lastClass : ℝ) - A.targetExcess := by
    rw [ht, Nat.cast_sub hcap.2]
  refine ⟨hcounts.1, hcounts.2.1, hcounts.2.2, ?_, ?_, ?_⟩
  · rw [hsr]
    linarith [A.sourceExcess_le_abs_delta, hg.2.1, hg.2.2.1]
  · rw [htr]
    linarith [A.targetExcess_le_abs_delta, hg.2.1, hg.2.2.2.1]
  · intro c hc
    linarith [A.keptReservePrefix_lower_bound hcap c, hg.2.2.2.2 c hc, hg.2.1]

end OriginalStageExcessRemovalData
end OTSelector.Reconstruction
