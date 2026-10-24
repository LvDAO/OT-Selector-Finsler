import OTSelector.Reconstruction.OriginalMarkSelectedPopulationCouplingBlockKeptBalance
import OTSelector.Finite.AtomicIndexEquivalence
import OTSelector.Reconstruction.OriginalMarkSelectedPopulationCouplingBlockOrientedPopulationNormalized

/-! Exact original-index partition of the global kept reserve into fine classes. -/
open Set Function MeasureTheory
open scoped BigOperators ENNReal Classical
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability

/-- The actual block deletion data and its disjoint fine clock partition.
Both colors instantiate this separately with their own half-open cells. -/
structure OriginalReserveFineBlockPartition (B I : Type*) [Fintype B] [Fintype I] where
  blockCell : B → Set ℝ
  oppositeCell : B → Set ℝ
  deletionCell : B → Set ℝ
  fineCell : I → Set ℝ
  blockFor : I → B
  block_disjoint : Pairwise (Disjoint on blockCell)
  fine_disjoint : Pairwise (Disjoint on fineCell)
  fine_subset_block : ∀ i, fineCell i ⊆ blockCell (blockFor i)
  block_covered : ∀ b, blockCell b ⊆ ⋃ i, fineCell i
  measurable_block : ∀ b, MeasurableSet (blockCell b)
  measurable_opposite : ∀ b, MeasurableSet (oppositeCell b)
  measurable_deletion : ∀ b, MeasurableSet (deletionCell b)
  measurable_fine : ∀ i, MeasurableSet (fineCell i)

namespace OriginalReserveFineBlockPartition
variable {q : ℕ} {B I : Type*} [Fintype B] [Fintype I]
  (H : OriginalReserveFineBlockPartition B I)

def fineCount (K : Set (Fin q → ℝ)) (own other : Fin 2) (z : OriginalReserveSceneAux q) (i : I) : ℕ :=
  (originalReserveBlockClassKept K own other (H.blockCell (H.blockFor i))
    (H.oppositeCell (H.blockFor i)) (H.deletionCell (H.blockFor i)) (H.fineCell i) z).card

def selectedIndex (K : Set (Fin q → ℝ)) (own other : Fin 2) (z : OriginalReserveSceneAux q)
    (a : Σ i, Fin (H.fineCount K own other z i)) : ℕ :=
  originalReserveBlockClassSelection K own other (H.blockCell (H.blockFor a.1))
    (H.oppositeCell (H.blockFor a.1)) (H.deletionCell (H.blockFor a.1)) (H.fineCell a.1)
    (H.fineCount K own other z a.1) z a.2

theorem selectedIndex_mark (K : Set (Fin q → ℝ)) (own other : Fin 2) (z : OriginalReserveSceneAux q)
    (a : Σ i, Fin (H.fineCount K own other z i)) :
    H.selectedIndex K own other z a < z.2.1 ∧ z.2.2 (H.selectedIndex K own other z a) ∈ H.fineCell a.1 :=
  originalReserveBlockClassSelection_observed_mark _ _ _ _ _ _ _ _ _ rfl _

private theorem sum_fine_filters {A M : Type*} [DecidableEq A] [AddCommMonoid M]
    (U : Finset A) (marks : A → ℝ) (f : A → M)
    (hcover : ∀ a ∈ U, marks a ∈ ⋃ i, H.fineCell i) :
    (∑ i, ∑ a ∈ U.filter (fun a ↦ marks a ∈ H.fineCell i), f a) = ∑ a ∈ U, f a := by
  simp only [Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a ha
  obtain ⟨i, hi⟩ := mem_iUnion.mp (hcover a ha)
  rw [Finset.sum_eq_single i]
  · simp [hi]
  · intro j _ hji
    simp [show marks a ∉ H.fineCell j from fun hj ↦ disjoint_left.mp (H.fine_disjoint hji) hj hi]
  · simp

/-- The disjoint fine arrays count exactly the same original Nat indices as
the literal global kept Fin labels; no distinct-point premise is used. -/
theorem countingMeasure_eq (K : Set (Fin q → ℝ)) (own other : Fin 2) (z : OriginalReserveSceneAux q) :
    (∑ a : originalReserveBlocksKeptFin K own other H.blockCell H.oppositeCell H.deletionCell z,
      Measure.dirac (a.val.val)) =
    ∑ a : Σ i, Fin (H.fineCount K own other z i), Measure.dirac (H.selectedIndex K own other z a) := by
  let U := originalReserveBlocksKept K own other H.blockCell H.oppositeCell H.deletionCell z
  have hcover : ∀ a ∈ U, z.2.2 a ∈ ⋃ i, H.fineCell i := by
    intro a ha
    obtain ⟨b, _, hb⟩ := Finset.mem_biUnion.mp ha
    exact H.block_covered b (Finset.mem_filter.mp (Finset.mem_sdiff.mp hb).1).2
  calc
    _ = ∑ a ∈ U, Measure.dirac a := by
      rw [Finset.sum_coe_sort _ (fun a : Fin z.2.1 ↦ Measure.dirac a.val)]
      dsimp only [U]
      rw [originalReserveBlocksKept_eq_map_fin K own other
        H.blockCell H.oppositeCell H.deletionCell z, Finset.sum_map]
      rfl
    _ = ∑ i, ∑ a ∈ U.filter (fun a ↦ z.2.2 a ∈ H.fineCell i), Measure.dirac a :=
      (H.sum_fine_filters U z.2.2 Measure.dirac hcover).symm
    _ = _ := by
      rw [Fintype.sum_sigma]
      apply Finset.sum_congr rfl
      intro i _
      rw [originalReserveBlocksKept_filter_class K own other H.blockCell H.oppositeCell
        H.deletionCell H.block_disjoint z (H.blockFor i) (H.fine_subset_block i),
        ← originalReserveBlockClassSelection_range K own other (H.blockCell (H.blockFor i))
          (H.oppositeCell (H.blockFor i)) (H.deletionCell (H.blockFor i)) (H.fineCell i)
          (H.fineCount K own other z i) z rfl, Finset.sum_map]
      rfl

/-- A true equivalence preserves every unchanged original observed index. -/
def indexEquiv (K : Set (Fin q → ℝ)) (own other : Fin 2) (z : OriginalReserveSceneAux q) :
    originalReserveBlocksKeptFin K own other H.blockCell H.oppositeCell H.deletionCell z ≃
      Σ i, Fin (H.fineCount K own other z i) :=
  Classical.choose (exists_originalIndexEquiv_of_sum_dirac_eq
    (fun a : originalReserveBlocksKeptFin K own other H.blockCell H.oppositeCell H.deletionCell z ↦ a.val.val)
    (H.selectedIndex K own other z) (H.countingMeasure_eq K own other z))

theorem indexEquiv_apply (K : Set (Fin q → ℝ)) (own other : Fin 2) (z : OriginalReserveSceneAux q)
    (a : originalReserveBlocksKeptFin K own other H.blockCell H.oppositeCell H.deletionCell z) :
    a.val.val = H.selectedIndex K own other z (H.indexEquiv K own other z a) :=
  Classical.choose_spec (exists_originalIndexEquiv_of_sum_dirac_eq
    (fun a : originalReserveBlocksKeptFin K own other H.blockCell H.oppositeCell H.deletionCell z ↦ a.val.val)
    (H.selectedIndex K own other z) (H.countingMeasure_eq K own other z)) a

end OriginalReserveFineBlockPartition
end OTSelector.Reconstruction
