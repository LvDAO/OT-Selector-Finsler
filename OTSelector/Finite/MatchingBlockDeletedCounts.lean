import OTSelector.Finite.BlockRepair
import OTSelector.Finite.PartialMatching
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Reconstruction.OriginalLegalScreeningComparatorBlockDeletedCounts.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Reconstruction.OriginalLegalScreeningComparatorBlockDeletedCounts`; the selected original proof blocks follow. -/
section

/-!
# Reconstruction.OriginalLegalScreeningComparatorBlockDeletedCounts

**Conditions:** Actual block source/target deletion subsets are free and have exactly the two opposite excess counts.

**Objects:** The local unused sets after deletion, their equal size and exact block completion count.

**Proof detail:** Use finite subset subtraction and within-block edge-to-endpoint cardinalities; subtracting the prescribed excess changes each unused count to the deficit from min(sourceBlock,targetBlock).

**Sources:** [Reinhard Diestel, Graph Theory, 4th electronic edition (2010), corrected reprint 2012](https://diestel-graph-theory.com/Sample.pdf#page=2), Chapter 2 opening matching definition and Section 2.1, first three chapter pages; [Terence Tao, Analysis I](https://github.com/teorth/analysis/blob/main/Analysis/Section_7_1.lean), Sections 4.3 (absolute value) and 7.1 (finite series), in particular Proposition 7.1.11; [OTSelector project, Original strict-screen residual slack and repair](main.tex#strict-screen-residual-slack), main.tex label strict-screen-residual-slack, line 6749.

Source relation (corollary): The cited sections provide the stated mathematical foundations; the exact finite construction and quantitative bound in this module are local consequences, not a claim that the book states the Lean theorem verbatim.
-/

/-! Actual blockwise excess deletion gives the precise local completion count. -/
open Set Function
open scoped BigOperators Classical
noncomputable section
namespace OTSelector.Reconstruction.PartialMatching
variable {m n : ℕ} {B : Type*} [DecidableEq B]

/-- Removing each block's actual signed excess from its unused original
indices gives the local minimum count and equal remaining colors. This is a
local statement; the complete original graph may have smaller global rank. -/
theorem originalBlockDeletedUnused_count_spec
    (σ : OTSelector.PartialMatching m n) (c : Fin m → B) (d : Fin n → B)
    (hsame : ∀ e ∈ σ.edges, c e.1 = d e.2) (b : B)
    (Ds : Finset (Fin m)) (Dt : Finset (Fin n))
    (hDs : Ds ⊆ σ.freeRows.filter (fun i ↦ c i = b))
    (hDt : Dt ⊆ σ.freeCols.filter (fun j ↦ d j = b))
    (hDscard : Ds.card = (Finset.univ.filter (fun i ↦ c i = b)).card -
      (Finset.univ.filter (fun j ↦ d j = b)).card)
    (hDtcard : Dt.card = (Finset.univ.filter (fun j ↦ d j = b)).card -
      (Finset.univ.filter (fun i ↦ c i = b)).card) :
    let U := (σ.freeRows.filter (fun i ↦ c i = b)) \ Ds
    let V := (σ.freeCols.filter (fun j ↦ d j = b)) \ Dt
    U ⊆ σ.freeRows ∧ V ⊆ σ.freeCols ∧
      (∀ i ∈ U, c i = b) ∧ (∀ j ∈ V, d j = b) ∧
      (σ.edges.filter (fun e ↦ c e.1 = b)).card + U.card =
        min (Finset.univ.filter (fun i ↦ c i = b)).card
          (Finset.univ.filter (fun j ↦ d j = b)).card ∧ U.card = V.card := by
  have heq : σ.edges.filter (fun e ↦ c e.1 = b) = σ.edges.filter (fun e ↦ d e.2 = b) := by
    apply Finset.filter_congr
    intro e he
    rw [hsame e he]
  have hsle : (σ.edges.filter (fun e ↦ c e.1 = b)).card ≤
      (Finset.univ.filter (fun i ↦ c i = b)).card := by
    rw [← σ.card_rows_filter (fun i ↦ c i = b)]
    exact Finset.card_le_card (Finset.filter_subset_filter _ (Finset.subset_univ _))
  have htle : (σ.edges.filter (fun e ↦ c e.1 = b)).card ≤
      (Finset.univ.filter (fun j ↦ d j = b)).card := by
    rw [heq, ← σ.card_cols_filter (fun j ↦ d j = b)]
    exact Finset.card_le_card (Finset.filter_subset_filter _ (Finset.subset_univ _))
  have hucard : ((σ.freeRows.filter (fun i ↦ c i = b)) \ Ds).card =
      (Finset.univ.filter (fun i ↦ c i = b)).card -
        (σ.edges.filter (fun e ↦ c e.1 = b)).card - Ds.card := by
    rw [Finset.card_sdiff_of_subset hDs, σ.card_freeRows_filter, σ.card_rows_filter]
  have hvcard : ((σ.freeCols.filter (fun j ↦ d j = b)) \ Dt).card =
      (Finset.univ.filter (fun j ↦ d j = b)).card -
        (σ.edges.filter (fun e ↦ c e.1 = b)).card - Dt.card := by
    rw [Finset.card_sdiff_of_subset hDt, σ.card_freeCols_filter, σ.card_cols_filter, ← heq]
  have hscap := Finset.card_le_card hDs
  have htcap := Finset.card_le_card hDt
  rw [σ.card_freeRows_filter, σ.card_rows_filter] at hscap
  rw [σ.card_freeCols_filter, σ.card_cols_filter, ← heq] at htcap
  refine ⟨Finset.sdiff_subset.trans (Finset.filter_subset _ _),
    Finset.sdiff_subset.trans (Finset.filter_subset _ _),
    (fun i hi ↦ (Finset.mem_filter.mp (Finset.mem_sdiff.mp hi).1).2),
    (fun j hj ↦ (Finset.mem_filter.mp (Finset.mem_sdiff.mp hj).1).2), ?_, ?_⟩
  · omega
  · omega

end OTSelector.Reconstruction.PartialMatching

end
end
