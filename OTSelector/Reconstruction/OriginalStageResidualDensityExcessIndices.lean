import OTSelector.Reconstruction.OriginalStageResidualDensityReserveCounts
import Mathlib.Data.Finset.Sort

/-! Deterministic extreme-class removal using only actual marks and original Fin indices. -/
open Set Function MeasureTheory
open scoped ENNReal BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OTSelector.Reconstruction
open OTSelector.Probability

/-- The first k original indices in a mark class, in the original Fin order.
No spatial coordinate is inspected and every selected index remains an original index. -/
def originalStageMarkInitialIndices {n : ℕ} (marks : Fin n → ℝ) (C : Set ℝ) (k : ℕ) :
    Finset (Fin n) := by
  classical
  exact (((Finset.univ.filter (fun i ↦ marks i ∈ C)).sort (· ≤ ·)).take k).toFinset

/-- Every selected original index has its actual mark in the selected class. -/
theorem originalStageMarkInitialIndices_subset {n : ℕ} (marks : Fin n → ℝ)
    (C : Set ℝ) (k : ℕ) :
    originalStageMarkInitialIndices marks C k ⊆ Finset.univ.filter (fun i ↦ marks i ∈ C) := by
  classical
  intro i hi
  have hmem : i ∈ ((Finset.univ.filter (fun i ↦ marks i ∈ C)).sort (· ≤ ·)).take k :=
    List.mem_toFinset.mp hi
  exact (Finset.mem_sort (· ≤ ·)).mp (List.mem_of_mem_take hmem)

/-- The actual number removed is exactly k, up to the actual class capacity. -/
theorem card_originalStageMarkInitialIndices {n : ℕ} (marks : Fin n → ℝ)
    (C : Set ℝ) (k : ℕ) :
    (originalStageMarkInitialIndices marks C k).card =
      min k (Finset.univ.filter (fun i ↦ marks i ∈ C)).card := by
  classical
  unfold originalStageMarkInitialIndices
  rw [List.toFinset_card_of_nodup ((Finset.sort_nodup _ _).take),
    List.length_take, Finset.length_sort]

/-- The original reserve indices remain after deleting exactly the selected mark indices. -/
def originalStageKeptAfterMarkRemoval {n : ℕ} (marks : Fin n → ℝ) (C : Set ℝ) (k : ℕ) :
    Finset (Fin n) := Finset.univ \ originalStageMarkInitialIndices marks C k

/-- The kept set retains exactly the original n minus the number selected. -/
theorem card_originalStageKeptAfterMarkRemoval {n : ℕ} (marks : Fin n → ℝ)
    (C : Set ℝ) (k : ℕ) :
    (originalStageKeptAfterMarkRemoval marks C k).card =
      n - min k (Finset.univ.filter (fun i ↦ marks i ∈ C)).card := by
  classical
  rw [originalStageKeptAfterMarkRemoval, Finset.card_sdiff_of_subset (Finset.subset_univ _),
    Finset.card_univ, Fintype.card_fin, card_originalStageMarkInitialIndices]

/-- Actual selected-class capacity makes the removed count exactly k. -/
theorem card_originalStageMarkInitialIndices_of_le {n : ℕ} (marks : Fin n → ℝ)
    (C : Set ℝ) {k : ℕ}
    (hk : k ≤ (Finset.univ.filter (fun i ↦ marks i ∈ C)).card) :
    (originalStageMarkInitialIndices marks C k).card = k := by
  rw [card_originalStageMarkInitialIndices, Nat.min_eq_left hk]

/-- Removing selected indices decreases any actual prefix count by at most the removal count. -/
theorem originalStageMarkRemoval_count_bounds {n : ℕ} (marks : Fin n → ℝ)
    (C B : Set ℝ) (k : ℕ) :
    (Finset.univ.filter (fun i ↦ marks i ∈ B)).card -
        (originalStageMarkInitialIndices marks C k).card ≤
      ((originalStageKeptAfterMarkRemoval marks C k).filter (fun i ↦ marks i ∈ B)).card ∧
    ((originalStageKeptAfterMarkRemoval marks C k).filter (fun i ↦ marks i ∈ B)).card ≤
      (Finset.univ.filter (fun i ↦ marks i ∈ B)).card := by
  classical
  let deleted := originalStageMarkInitialIndices marks C k
  let kept := originalStageKeptAfterMarkRemoval marks C k
  have hs : (Finset.univ.filter (fun i ↦ marks i ∈ B)) ⊆
      (kept.filter (fun i ↦ marks i ∈ B)) ∪ deleted := by
    intro i hi
    by_cases hd : i ∈ deleted
    · exact Finset.mem_union_right _ hd
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr
        ⟨Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hd⟩, (Finset.mem_filter.mp hi).2⟩)
  have hc := (Finset.card_le_card hs).trans (Finset.card_union_le _ _)
  dsimp [kept, deleted] at hc
  constructor
  · omega
  · apply Finset.card_le_card
    intro i hi
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hi).2⟩

/-- In the deletion class, the actual surviving count is its original count minus removals. -/
theorem originalStageMarkRemoval_own_class_count {n : ℕ} (marks : Fin n → ℝ)
    (C : Set ℝ) (k : ℕ) :
    ((originalStageKeptAfterMarkRemoval marks C k).filter (fun i ↦ marks i ∈ C)).card =
      (Finset.univ.filter (fun i ↦ marks i ∈ C)).card -
        (originalStageMarkInitialIndices marks C k).card := by
  classical
  have heq : (originalStageKeptAfterMarkRemoval marks C k).filter (fun i ↦ marks i ∈ C) =
      (Finset.univ.filter (fun i ↦ marks i ∈ C)) \ originalStageMarkInitialIndices marks C k := by
    ext i
    simp only [originalStageKeptAfterMarkRemoval, Finset.mem_filter, Finset.mem_sdiff,
      Finset.mem_univ, true_and]
    tauto
  rw [heq, Finset.card_sdiff_of_subset (originalStageMarkInitialIndices_subset marks C k)]

/-- The actual original four arrays, with unchanged spatial coordinates and clock marks. -/
structure OriginalStageExcessRemovalData (q : ℕ) where
  sourceMain : MarkedCloudSpace q ℝ
  targetMain : MarkedCloudSpace q ℝ
  sourceReserve : MarkedCloudSpace q ℝ
  targetReserve : MarkedCloudSpace q ℝ
  firstClass : Set ℝ
  lastClass : Set ℝ

namespace OriginalStageExcessRemovalData
variable (A : OriginalStageExcessRemovalData q)

/-- The literal full source and target counts before removal. -/
def sourceCount : ℕ := A.sourceMain.1 + A.sourceReserve.1

def targetCount : ℕ := A.targetMain.1 + A.targetReserve.1

/-- Positive and negative parts of the actual full color excess, computed as natural differences. -/
def sourceExcess : ℕ := A.sourceCount - A.targetCount

def targetExcess : ℕ := A.targetCount - A.sourceCount

/-- Delete source excess in the first class using only its actual marks and Fin order. -/
def sourceDeleted : Finset (Fin A.sourceReserve.1) :=
  originalStageMarkInitialIndices (fun i ↦ (A.sourceReserve.2 i).2) A.firstClass A.sourceExcess

/-- Delete target excess in the last class by the same original-index rule. -/
def targetDeleted : Finset (Fin A.targetReserve.1) :=
  originalStageMarkInitialIndices (fun i ↦ (A.targetReserve.2 i).2) A.lastClass A.targetExcess

def sourceKept : Finset (Fin A.sourceReserve.1) := Finset.univ \ A.sourceDeleted

def targetKept : Finset (Fin A.targetReserve.1) := Finset.univ \ A.targetDeleted

/-- Capacity is stated using the literal original extreme-class counts. -/
def hasCapacity : Prop :=
  A.sourceExcess ≤ originalStageRemainingReserveClassCount A.sourceReserve Finset.univ A.firstClass ∧
  A.targetExcess ≤ originalStageRemainingReserveClassCount A.targetReserve Finset.univ A.lastClass

/-- At most one color has nonzero excess. -/
theorem sourceExcess_eq_zero_or_targetExcess_eq_zero :
    A.sourceExcess = 0 ∨ A.targetExcess = 0 := by
  unfold sourceExcess targetExcess
  omega

/-- Actual extreme-class capacity deletes exactly the actual signed excess and balances the
full source and target totals, preserving all main indices and the original surviving reserve indices. -/
theorem removal_counts_and_balance (hcap : A.hasCapacity) :
    A.sourceDeleted.card = A.sourceExcess ∧ A.targetDeleted.card = A.targetExcess ∧
    A.sourceMain.1 + A.sourceKept.card = A.targetMain.1 + A.targetKept.card := by
  classical
  have hs : A.sourceDeleted.card = A.sourceExcess :=
    card_originalStageMarkInitialIndices_of_le _ _ hcap.1
  have ht : A.targetDeleted.card = A.targetExcess :=
    card_originalStageMarkInitialIndices_of_le _ _ hcap.2
  refine ⟨hs, ht, ?_⟩
  have hsc : A.sourceKept.card = A.sourceReserve.1 - A.sourceExcess := by
    rw [sourceKept, Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ,
      Fintype.card_fin, hs]
  have htc : A.targetKept.card = A.targetReserve.1 - A.targetExcess := by
    rw [targetKept, Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ,
      Fintype.card_fin, ht]
  have hsr : A.sourceExcess ≤ A.sourceReserve.1 := by
    rw [← hs]
    simpa only [Fintype.card_fin] using Finset.card_le_univ A.sourceDeleted
  have htr : A.targetExcess ≤ A.targetReserve.1 := by
    rw [← ht]
    simpa only [Fintype.card_fin] using Finset.card_le_univ A.targetDeleted
  rw [hsc, htc]
  dsimp [sourceExcess, targetExcess, sourceCount, targetCount] at *
  omega

end OriginalStageExcessRemovalData
end OTSelector.Reconstruction
