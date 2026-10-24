import OTSelector.Finite.LegalMatchingValue

/-!
# Flipping an actual legal alternating chain

The certificate consists of original indices, a free initial source, a free
terminal target, and actual old matching edges between successive new edges.
Flipping it adds exactly one legal edge in cardinality. The cost identities
charge every inserted and removed edge, including signed probe terms.
-/

open Set Function MeasureTheory
open scoped BigOperators
noncomputable section
namespace OTSelector.Reconstruction.PartialMatching
set_option backward.isDefEq.respectTransparency false

variable {m n k : ℕ}

/-- A simple alternating chain with `k+1` new edges and `k` old edges. -/
structure LegalAugmentingChain (allowed : Finset (Fin m × Fin n))
    (σ : OTSelector.PartialMatching m n) (k : ℕ) where
  row : Fin (k + 1) → Fin m
  col : Fin (k + 1) → Fin n
  row_inj : Injective row
  col_inj : Injective col
  first_free : row 0 ∉ σ.rows
  last_free : col (Fin.last k) ∉ σ.cols
  old_mem : ∀ i : Fin k, (row i.succ, col i.castSucc) ∈ σ.edges
  new_legal : ∀ i, (row i, col i) ∈ allowed

namespace LegalAugmentingChain
variable {allowed : Finset (Fin m × Fin n)} {σ : OTSelector.PartialMatching m n}
  (P : LegalAugmentingChain allowed σ k)

def oldEdges : Finset (Fin m × Fin n) :=
  Finset.univ.image (fun i : Fin k ↦ (P.row i.succ, P.col i.castSucc))

def newEdges : Finset (Fin m × Fin n) :=
  Finset.univ.image (fun i : Fin (k + 1) ↦ (P.row i, P.col i))

theorem oldEdges_subset : P.oldEdges ⊆ σ.edges := by
  intro e he
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp he
  exact P.old_mem i

theorem oldEdges_card : P.oldEdges.card = k := by
  rw [oldEdges, Finset.card_image_of_injective _]
  · simp
  · intro i j h
    exact Fin.succ_injective _ (P.row_inj (congrArg Prod.fst h))

theorem newEdges_card : P.newEdges.card = k + 1 := by
  rw [newEdges, Finset.card_image_of_injective _]
  · simp
  · intro i j h
    exact P.row_inj (congrArg Prod.fst h)

theorem retained_row_ne {e : Fin m × Fin n} (he : e ∈ σ.edges \ P.oldEdges)
    (i : Fin (k + 1)) : e.1 ≠ P.row i := by
  refine Fin.cases ?_ (fun j ↦ ?_) i
  · intro h
    exact P.first_free (Finset.mem_image.mpr ⟨e, (Finset.mem_sdiff.mp he).1, h⟩)
  · intro h
    have heq := σ.row_inj e (Finset.mem_sdiff.mp he).1
      (P.row j.succ, P.col j.castSucc) (P.old_mem j) h
    exact (Finset.mem_sdiff.mp he).2
      (heq ▸ Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩)

theorem retained_col_ne {e : Fin m × Fin n} (he : e ∈ σ.edges \ P.oldEdges)
    (i : Fin (k + 1)) : e.2 ≠ P.col i := by
  refine Fin.lastCases ?_ (fun j ↦ ?_) i
  · intro h
    exact P.last_free (Finset.mem_image.mpr ⟨e, (Finset.mem_sdiff.mp he).1, h⟩)
  · intro h
    have heq := σ.col_inj e (Finset.mem_sdiff.mp he).1
      (P.row j.succ, P.col j.castSucc) (P.old_mem j) h
    exact (Finset.mem_sdiff.mp he).2
      (heq ▸ Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩)

theorem disjoint_retained_new : Disjoint (σ.edges \ P.oldEdges) P.newEdges := by
  apply Finset.disjoint_left.mpr
  intro e he hn
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hn
  exact P.retained_row_ne he i rfl

/-- Remove precisely the old chain edges and insert the new chain edges. -/
def flip : OTSelector.PartialMatching m n where
  edges := (σ.edges \ P.oldEdges) ∪ P.newEdges
  row_inj := by
    intro e he f hf h
    rcases Finset.mem_union.mp he with he | he <;>
      rcases Finset.mem_union.mp hf with hf | hf
    · exact σ.row_inj e (Finset.mem_sdiff.mp he).1 f (Finset.mem_sdiff.mp hf).1 h
    · obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hf
      exact (P.retained_row_ne he i h).elim
    · obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp he
      exact (P.retained_row_ne hf i h.symm).elim
    · obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp he
      obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hf
      rw [P.row_inj h]
  col_inj := by
    intro e he f hf h
    rcases Finset.mem_union.mp he with he | he <;>
      rcases Finset.mem_union.mp hf with hf | hf
    · exact σ.col_inj e (Finset.mem_sdiff.mp he).1 f (Finset.mem_sdiff.mp hf).1 h
    · obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hf
      exact (P.retained_col_ne he i h).elim
    · obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp he
      exact (P.retained_col_ne hf i h.symm).elim
    · obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp he
      obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hf
      rw [P.col_inj h]

theorem flip_isLegal (hσ : IsLegal allowed σ) : IsLegal allowed P.flip := by
  intro e he
  rcases Finset.mem_union.mp he with he | he
  · exact hσ (Finset.mem_sdiff.mp he).1
  · obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp he
    exact P.new_legal i

theorem flip_card : P.flip.card = σ.card + 1 := by
  have hk : k ≤ σ.card := by
    rw [← P.oldEdges_card]
    exact Finset.card_le_card P.oldEdges_subset
  change ((σ.edges \ P.oldEdges) ∪ P.newEdges).card = _
  rw [Finset.card_union_of_disjoint P.disjoint_retained_new,
    Finset.card_sdiff_of_subset P.oldEdges_subset, P.oldEdges_card, P.newEdges_card]
  change σ.card - k + (k + 1) = σ.card + 1
  omega

/-- The exact objective changes by inserted costs minus removed costs. -/
theorem flip_cost (c : Fin m → Fin n → ℝ) :
    P.flip.cost c = σ.cost c - (∑ i : Fin k, c (P.row i.succ) (P.col i.castSucc)) +
      ∑ i : Fin (k + 1), c (P.row i) (P.col i) := by
  have ho : (∑ e ∈ P.oldEdges, c e.1 e.2) =
      ∑ i : Fin k, c (P.row i.succ) (P.col i.castSucc) := by
    rw [oldEdges, Finset.sum_image]
    intro i hi j hj h
    exact Fin.succ_injective _ (P.row_inj (congrArg Prod.fst h))
  have hn : (∑ e ∈ P.newEdges, c e.1 e.2) =
      ∑ i : Fin (k + 1), c (P.row i) (P.col i) := by
    rw [newEdges, Finset.sum_image]
    intro i hi j hj h
    exact P.row_inj (congrArg Prod.fst h)
  change (∑ e ∈ (σ.edges \ P.oldEdges) ∪ P.newEdges, c e.1 e.2) = _
  have hsplit := Finset.sum_sdiff (f := fun e : Fin m × Fin n ↦ c e.1 e.2)
    P.oldEdges_subset
  rw [ho] at hsplit
  rw [Finset.sum_union P.disjoint_retained_new, hn]
  change _ = (∑ e ∈ σ.edges, c e.1 e.2) - _ + _
  linarith

/-- Signed tilted costs pay for all inserted and removed terms. -/
theorem flip_cost_le_add_signed (c : Fin m → Fin n → ℝ) {B : ℝ}
    (hB : ∀ i j, |c i j| ≤ B) :
    P.flip.cost c ≤ σ.cost c + (2 * (k : ℝ) + 1) * B := by
  have ho : -(∑ i : Fin k, c (P.row i.succ) (P.col i.castSucc)) ≤ (k : ℝ) * B := by
    rw [← Finset.sum_neg_distrib]
    calc
      _ ≤ ∑ _i : Fin k, B := Finset.sum_le_sum fun i _ ↦
        (neg_le_abs _).trans (hB _ _)
      _ = _ := by simp
  have hn : (∑ i : Fin (k + 1), c (P.row i) (P.col i)) ≤ ((k : ℝ) + 1) * B := by
    calc
      _ ≤ ∑ _i : Fin (k + 1), B := Finset.sum_le_sum fun i _ ↦
        (le_abs_self _).trans (hB _ _)
      _ = _ := by simp [Nat.cast_add, Nat.cast_one]
  rw [P.flip_cost]
  linarith

/-- Nonnegative old kinetic costs require paying only for new kinetic edges. -/
theorem flip_cost_le_add_kinetic (c : Fin m → Fin n → ℝ) {B : ℝ}
    (hc : ∀ i : Fin k, 0 ≤ c (P.row i.succ) (P.col i.castSucc))
    (hB : ∀ i : Fin (k + 1), c (P.row i) (P.col i) ≤ B) :
    P.flip.cost c ≤ σ.cost c + ((k : ℝ) + 1) * B := by
  have ho : 0 ≤ ∑ i : Fin k, c (P.row i.succ) (P.col i.castSucc) :=
    Finset.sum_nonneg fun i _ ↦ hc i
  have hn : (∑ i : Fin (k + 1), c (P.row i) (P.col i)) ≤ ((k : ℝ) + 1) * B := by
    calc
      _ ≤ ∑ _i : Fin (k + 1), B := Finset.sum_le_sum fun i _ ↦ hB i
      _ = _ := by simp [Nat.cast_add, Nat.cast_one]
  rw [P.flip_cost]
  linarith

end LegalAugmentingChain
end OTSelector.Reconstruction.PartialMatching
