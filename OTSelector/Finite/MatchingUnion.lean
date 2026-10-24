import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import OTSelector.Finite.BlockMatchingComparison
import OTSelector.Finite.PartialMatching

/-!
# Finite.MatchingUnion

**Conditions:** Two partial matchings have disjoint used source sets and disjoint used target sets; the balanced saturation corollary has the stated residual count.

**Objects:** Their edge union, free endpoints, additive edge count and additive signed cost.

**Proof detail:** Endpoint disjointness rules out mixed collisions, then disjoint-union cardinality and sum formulas give the identities; natural subtraction restores the balanced maximum cardinality.

**Sources:** [Reinhard Diestel, Graph Theory, 4th electronic edition (2010), corrected reprint 2012](https://diestel-graph-theory.com/Sample.pdf#page=2), Chapter 2 opening matching definition and Section 2.1, first three chapter pages; [Terence Tao, Analysis I](https://github.com/teorth/analysis/blob/main/Analysis/Section_7_1.lean), Sections 4.3 (absolute value) and 7.1 (finite series), in particular Proposition 7.1.11.

Source relation (corollary): The cited sections provide the stated mathematical foundations; the exact finite construction and quantitative bound in this module are local consequences, not a claim that the book states the Lean theorem verbatim.
-/



/-!
## Lemma skeleton

* **Conditions:** sigma and tau are partial matchings in the same finite a by b rectangle. Their used row sets are disjoint and their used column sets are disjoint. The full-cardinality corollary is for balanced N by N clouds, with the block part of cardinality sum_t min(blockSource_t,blockTarget_t) and the repair part of cardinality min(N-sigma.card,N-sigma.card).
* **Objects:** PartialMatching.union: union of the two finite edge sets under endpoint-disjointness certificates; rows,cols: used endpoint finite sets; freeRows,freeCols: the complements of used endpoint sets; blockS,blockT: finite block labels used only in the balanced saturation corollary
* **Proof detail:** Analyze membership in the edge union; mixed source/target pieces cannot share an endpoint by the disjointness assumptions. Prove the two edge sets disjoint and use finite-set cardinality and finite-sum union formulas. Convert free-set membership into endpoint disjointness. Use sigma.card <= N and natural subtraction arithmetic to show sigma.card + (N-sigma.card) = N.

## Mathematical sources

* Reinhard Diestel, *Graph Theory, 4th electronic edition (2010), corrected reprint 2012*, Chapter 2 opening matching definition and Section 2.1, first three chapter pages.
  https://diestel-graph-theory.com/Sample.pdf#page=2
* Terence Tao, *Analysis I*, Sections 4.3 (absolute value) and 7.1 (finite series), in particular Proposition 7.1.11.
  https://github.com/teorth/analysis/blob/main/Analysis/Section_7_1.lean

**Relationship to the sources:** Endpoint-disjoint edge union and free-endpoint saturation are direct finite matching/cardinality consequences. No augmenting-path or arbitrary-graph existence theorem is used.
-/

/-!
# Union of a block matching with a residual matching

A matching between two tagged clouds can be assembled from two independent
pieces: a matching that stays inside common blocks, and a matching of the
remaining (free) rows and columns.  The union is again a partial matching, with
additive cardinality and cost.  When the block part saturates every block and
the residual part is maximum on the free rows and columns, the union has maximum
global cardinality.

This is the combinatorial step of the self-similar finite-volume comparison:
the block part is the optimal matching at reduced intensity, and the residual
part is the hierarchical repair of the unmatched points and the reserves.
-/

open scoped BigOperators

noncomputable section
namespace OTSelector

section Union

variable {a b : ℕ}

/-- The union of two matchings with disjoint used rows and disjoint used columns
is a partial matching with additive cardinality and cost. -/
def PartialMatching.union (σ τ : PartialMatching a b)
    (hrow : Disjoint σ.rows τ.rows) (hcol : Disjoint σ.cols τ.cols) :
    PartialMatching a b where
  edges := σ.edges ∪ τ.edges
  row_inj := by
    intro e he e' he' h
    rcases Finset.mem_union.mp he with heS | heT <;>
      rcases Finset.mem_union.mp he' with he'S | he'T
    · exact σ.row_inj e heS e' he'S h
    · exfalso
      have hr1 : e.1 ∈ σ.rows := Finset.mem_image.mpr ⟨e, heS, rfl⟩
      have hr2 : e.1 ∈ τ.rows := by
        rw [h]
        exact Finset.mem_image.mpr ⟨e', he'T, rfl⟩
      exact (Finset.disjoint_left.mp hrow) hr1 hr2
    · exfalso
      have hr1 : e.1 ∈ τ.rows := Finset.mem_image.mpr ⟨e, heT, rfl⟩
      have hr2 : e.1 ∈ σ.rows := by
        rw [h]
        exact Finset.mem_image.mpr ⟨e', he'S, rfl⟩
      exact (Finset.disjoint_left.mp hrow) hr2 hr1
    · exact τ.row_inj e heT e' he'T h
  col_inj := by
    intro e he e' he' h
    rcases Finset.mem_union.mp he with heS | heT <;>
      rcases Finset.mem_union.mp he' with he'S | he'T
    · exact σ.col_inj e heS e' he'S h
    · exfalso
      have hc1 : e.2 ∈ σ.cols := Finset.mem_image.mpr ⟨e, heS, rfl⟩
      have hc2 : e.2 ∈ τ.cols := by
        rw [h]
        exact Finset.mem_image.mpr ⟨e', he'T, rfl⟩
      exact (Finset.disjoint_left.mp hcol) hc1 hc2
    · exfalso
      have hc1 : e.2 ∈ τ.cols := Finset.mem_image.mpr ⟨e, heT, rfl⟩
      have hc2 : e.2 ∈ σ.cols := by
        rw [h]
        exact Finset.mem_image.mpr ⟨e', he'S, rfl⟩
      exact (Finset.disjoint_left.mp hcol) hc2 hc1
    · exact τ.col_inj e heT e' he'T h

@[simp] theorem PartialMatching.union_edges (σ τ : PartialMatching a b)
    (hrow : Disjoint σ.rows τ.rows) (hcol : Disjoint σ.cols τ.cols) :
    (σ.union τ hrow hcol).edges = σ.edges ∪ τ.edges := rfl

theorem PartialMatching.card_union (σ τ : PartialMatching a b)
    (hrow : Disjoint σ.rows τ.rows) (hcol : Disjoint σ.cols τ.cols) :
    (σ.union τ hrow hcol).card = σ.card + τ.card := by
  classical
  unfold PartialMatching.card
  rw [PartialMatching.union_edges]
  rw [Finset.card_union_of_disjoint (s := σ.edges) (t := τ.edges)]
  · rw [Finset.disjoint_left]
    intro e heS heT
    have hr1 : e.1 ∈ σ.rows := Finset.mem_image.mpr ⟨e, heS, rfl⟩
    have hr2 : e.1 ∈ τ.rows := Finset.mem_image.mpr ⟨e, heT, rfl⟩
    exact (Finset.disjoint_left.mp hrow) hr1 hr2

theorem PartialMatching.cost_union (c : Fin a → Fin b → ℝ) (σ τ : PartialMatching a b)
    (hrow : Disjoint σ.rows τ.rows) (hcol : Disjoint σ.cols τ.cols) :
    (σ.union τ hrow hcol).cost c = σ.cost c + τ.cost c := by
  classical
  unfold PartialMatching.cost
  rw [PartialMatching.union_edges, Finset.sum_union]
  · rw [Finset.disjoint_left]
    intro e heS heT
    have hr1 : e.1 ∈ σ.rows := Finset.mem_image.mpr ⟨e, heS, rfl⟩
    have hr2 : e.1 ∈ τ.rows := Finset.mem_image.mpr ⟨e, heT, rfl⟩
    exact (Finset.disjoint_left.mp hrow) hr1 hr2

end Union


section Cardinality

variable {N : ℕ} {β : Type*} [Fintype β] [DecidableEq β]
  (blockS : Fin N → β) (blockT : Fin N → β)

/-- A matching supported on the free rows and columns is row- and column-disjoint
from the block matching. -/
theorem disjoint_rows_of_free (σ τ : PartialMatching N N)
    (h : τ.rows ⊆ Finset.univ \ σ.rows) : Disjoint σ.rows τ.rows := by
  rw [Finset.disjoint_left]
  intro x hx hx'
  exact (Finset.mem_sdiff.mp (h hx')).2 hx

theorem disjoint_cols_of_free (σ τ : PartialMatching N N)
    (h : τ.cols ⊆ Finset.univ \ σ.cols) : Disjoint σ.cols τ.cols := by
  rw [Finset.disjoint_left]
  intro x hx hx'
  exact (Finset.mem_sdiff.mp (h hx')).2 hx

/-- When the block part saturates every common block and the residual part is
maximum on the free rows and columns, the union has global maximum cardinality. -/
theorem PartialMatching.card_union_eq_min (σ τ : PartialMatching N N)
    (hrow : Disjoint σ.rows τ.rows) (hcol : Disjoint σ.cols τ.cols)
    (hσ : σ.card = ∑ t, min (blockSizeS blockS t) (blockSizeT blockT t))
    (hτ : τ.card = min (N - σ.card) (N - σ.card)) :
    (σ.union τ hrow hcol).card = min N N := by
  classical
  have hSsum : (∑ t, blockSizeS blockS t) = N := sum_card_blockFinset blockS
  have hTsum : (∑ t, blockSizeT blockT t) = N := sum_card_blockFinset blockT
  have hle1 : (∑ t, min (blockSizeS blockS t) (blockSizeT blockT t)) ≤ N :=
    (Finset.sum_le_sum fun t _ => min_le_left (blockSizeS blockS t) (blockSizeT blockT t)).trans_eq hSsum
  have hle2 : (∑ t, min (blockSizeS blockS t) (blockSizeT blockT t)) ≤ N :=
    (Finset.sum_le_sum fun t _ => min_le_right (blockSizeS blockS t) (blockSizeT blockT t)).trans_eq hTsum
  rw [PartialMatching.card_union σ τ hrow hcol, hτ, hσ]
  omega

end Cardinality

end OTSelector
