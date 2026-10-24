import Mathlib.Data.Nat.Dist
import OTSelector.Finite.BlockRepair
import OTSelector.Finite.PartialMatching
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Reconstruction.OriginalLegalScreeningComparatorBlockCompletionCounts.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Reconstruction.OriginalLegalScreeningComparatorBlockCompletionCounts`; the selected original proof blocks follow. -/
section

/-!
# Reconstruction.OriginalLegalScreeningComparatorBlockCompletionCounts

**Conditions:** A retained original-index matching stays within common blocks and saturates at least one side in each block.

**Objects:** Exact unused endpoint count as the sum of absolute block-count discrepancies.

**Proof detail:** Transfer used endpoint counts to the same within-block edge filter, subtract them from full block fibers and use saturation to replace the sum of free counts by natural distance; sum over the finite partition.

**Sources:** [Reinhard Diestel, Graph Theory, 4th electronic edition (2010), corrected reprint 2012](https://diestel-graph-theory.com/Sample.pdf#page=2), Chapter 2 opening matching definition and Section 2.1, first three chapter pages; [Terence Tao, Analysis I](https://github.com/teorth/analysis/blob/main/Analysis/Section_7_1.lean), Sections 4.3 (absolute value) and 7.1 (finite series), in particular Proposition 7.1.11; [OTSelector project, Original strict-screen residual slack and repair](main.tex#strict-screen-residual-slack), main.tex label strict-screen-residual-slack, line 6749.

Source relation (corollary): The cited sections provide the stated mathematical foundations; the exact finite construction and quantitative bound in this module are local consequences, not a claim that the book states the Lean theorem verbatim.
-/

/-! The literal unused endpoint count equals the sum of actual block count discrepancies. -/
open scoped BigOperators
noncomputable section
namespace OTSelector.Reconstruction.PartialMatching
variable {m n : ℕ} {β : Type*} [Fintype β] [DecidableEq β]

omit [Fintype β] in
/-- Same-block actual pairs use exactly the same number of indices of each colour
in each original block. -/
theorem same_block_used_counts_eq
    (c : Fin m → β) (d : Fin n → β) (σ : OTSelector.PartialMatching m n)
    (hsame : ∀ e ∈ σ.edges, c e.1 = d e.2) (b : β) :
    (σ.rows.filter (fun i ↦ c i = b)).card = (σ.cols.filter (fun j ↦ d j = b)).card := by
  classical
  rw [σ.card_rows_filter,σ.card_cols_filter]
  congr 1
  apply Finset.filter_congr
  intro e he
  rw [hsame e he]

omit [Fintype β] in
/-- The two unused counts in a saturated block add to the absolute difference of
its original colour counts. Here `Nat.dist` is the natural absolute difference. -/
theorem free_block_count_eq_discrepancy
    (c : Fin m → β) (d : Fin n → β) (σ : OTSelector.PartialMatching m n)
    (hsame : ∀ e ∈ σ.edges, c e.1 = d e.2)
    (hsat : ∀ b, (∀ i, c i = b → i ∈ σ.rows) ∨ (∀ j, d j = b → j ∈ σ.cols)) (b : β) :
    (σ.freeRows.filter (fun i ↦ c i = b)).card +
      (σ.freeCols.filter (fun j ↦ d j = b)).card =
      Nat.dist (Finset.univ.filter (fun i ↦ c i = b)).card
        (Finset.univ.filter (fun j ↦ d j = b)).card := by
  classical
  have heq := same_block_used_counts_eq c d σ hsame b
  rw [σ.card_freeRows_filter,σ.card_freeCols_filter]
  have hsle : (σ.rows.filter (fun i ↦ c i = b)).card ≤
      (Finset.univ.filter (fun i ↦ c i = b)).card :=
    Finset.card_le_card (Finset.filter_subset_filter _ (Finset.subset_univ _))
  have htle : (σ.cols.filter (fun j ↦ d j = b)).card ≤
      (Finset.univ.filter (fun j ↦ d j = b)).card :=
    Finset.card_le_card (Finset.filter_subset_filter _ (Finset.subset_univ _))
  rcases hsat b with hs | ht
  · have hset : σ.rows.filter (fun i ↦ c i = b) = Finset.univ.filter (fun i ↦ c i = b) := by
      ext i
      simp only [Finset.mem_filter,Finset.mem_univ,true_and]
      exact ⟨And.right,fun hi ↦ ⟨hs i hi,hi⟩⟩
    have hh := congrArg Finset.card hset
    unfold Nat.dist
    omega
  · have hset : σ.cols.filter (fun j ↦ d j = b) = Finset.univ.filter (fun j ↦ d j = b) := by
      ext j
      simp only [Finset.mem_filter,Finset.mem_univ,true_and]
      exact ⟨And.right,fun hj ↦ ⟨ht j hj,hj⟩⟩
    have hh := congrArg Finset.card hset
    unfold Nat.dist
    omega

/-- Every unused original index is accounted for by its actual block discrepancy. -/
theorem free_endpoints_eq_sum_block_discrepancy
    (c : Fin m → β) (d : Fin n → β) (σ : OTSelector.PartialMatching m n)
    (hsame : ∀ e ∈ σ.edges, c e.1 = d e.2)
    (hsat : ∀ b, (∀ i, c i = b → i ∈ σ.rows) ∨ (∀ j, d j = b → j ∈ σ.cols)) :
    σ.freeRows.card + σ.freeCols.card =
      ∑ b, Nat.dist (Finset.univ.filter (fun i ↦ c i = b)).card
        (Finset.univ.filter (fun j ↦ d j = b)).card := by
  classical
  have hs : σ.freeRows.card = ∑ b, (σ.freeRows.filter (fun i ↦ c i = b)).card :=
    Finset.card_eq_sum_card_fiberwise (fun _ _ ↦ Finset.mem_univ _)
  have ht : σ.freeCols.card = ∑ b, (σ.freeCols.filter (fun j ↦ d j = b)).card :=
    Finset.card_eq_sum_card_fiberwise (fun _ _ ↦ Finset.mem_univ _)
  rw [hs,ht,← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun b _ ↦ free_block_count_eq_discrepancy c d σ hsame hsat b)

end OTSelector.Reconstruction.PartialMatching

end
end
