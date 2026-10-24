import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Real.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.MeasurableSpace.Basic
import Mathlib.Tactic
import OTSelector.Finite.PartialMatching

/-!
# Finite.MatchingFamily

**Conditions:** A finite family of matchings has pairwise disjoint source and target endpoint sets.

**Objects:** The ambient matching formed by the union of all family edge sets.

**Proof detail:** Use endpoint disjointness to prove pairwise edge disjointness and row/column injectivity; apply biUnion cardinality and finite-sum formulas.

**Sources:** [Reinhard Diestel, Graph Theory, 4th electronic edition (2010), corrected reprint 2012](https://diestel-graph-theory.com/Sample.pdf#page=2), Chapter 2 opening matching definition and Section 2.1, first three chapter pages; [Terence Tao, Analysis I](https://github.com/teorth/analysis/blob/main/Analysis/Section_7_1.lean), Sections 4.3 (absolute value) and 7.1 (finite series), in particular Proposition 7.1.11.

Source relation (corollary): The cited sections provide the stated mathematical foundations; the exact finite construction and quantitative bound in this module are local consequences, not a claim that the book states the Lean theorem verbatim.
-/

/-! Finite families of matchings on disjoint original row and column sets.
Cardinality and signed cost add exactly. -/

open Set Function
open scoped BigOperators
noncomputable section
namespace OTSelector.PartialMatching
set_option backward.isDefEq.respectTransparency false

variable {m n : ℕ} {β : Type*} [Fintype β]
  (σ : β → PartialMatching m n)
  (hrows : Pairwise (fun b b' ↦ Disjoint (σ b).rows (σ b').rows))
  (hcols : Pairwise (fun b b' ↦ Disjoint (σ b).cols (σ b').cols))

include hrows in
theorem edges_pairwiseDisjoint :
    Set.PairwiseDisjoint ((Finset.univ : Finset β) : Set β) (fun b ↦ (σ b).edges) := by
  intro b hb b' hb' hbb'
  apply Finset.disjoint_left.mpr
  intro e he he'
  exact Finset.disjoint_left.mp (hrows hbb')
    (Finset.mem_image.mpr ⟨e, he, rfl⟩) (Finset.mem_image.mpr ⟨e, he', rfl⟩)

/-- Disjoint finite matching blocks, on their unchanged original indices. -/
def disjointFamily : PartialMatching m n where
  edges := Finset.univ.biUnion fun b ↦ (σ b).edges
  row_inj := by
    intro e he f hf h
    obtain ⟨b, _, heb⟩ := Finset.mem_biUnion.mp he
    obtain ⟨b', _, hfb⟩ := Finset.mem_biUnion.mp hf
    by_cases hbb' : b = b'
    · subst b'
      exact (σ b).row_inj _ heb _ hfb h
    · have hmem : e.1 ∈ (σ b').rows := by
        rw [h]
        exact Finset.mem_image.mpr ⟨f, hfb, rfl⟩
      exact (Finset.disjoint_left.mp (hrows hbb')
        (Finset.mem_image.mpr ⟨e, heb, rfl⟩) hmem).elim
  col_inj := by
    intro e he f hf h
    obtain ⟨b, _, heb⟩ := Finset.mem_biUnion.mp he
    obtain ⟨b', _, hfb⟩ := Finset.mem_biUnion.mp hf
    by_cases hbb' : b = b'
    · subst b'
      exact (σ b).col_inj _ heb _ hfb h
    · have hmem : e.2 ∈ (σ b').cols := by
        rw [h]
        exact Finset.mem_image.mpr ⟨f, hfb, rfl⟩
      exact (Finset.disjoint_left.mp (hcols hbb')
        (Finset.mem_image.mpr ⟨e, heb, rfl⟩) hmem).elim

@[simp]
theorem disjointFamily_edges :
    (disjointFamily σ hrows hcols).edges = Finset.univ.biUnion (fun b ↦ (σ b).edges) := rfl

theorem disjointFamily_card :
    (disjointFamily σ hrows hcols).card = ∑ b, (σ b).card := by
  unfold card
  rw [disjointFamily_edges, Finset.card_biUnion (edges_pairwiseDisjoint σ hrows)]

theorem disjointFamily_cost (c : Fin m → Fin n → ℝ) :
    (disjointFamily σ hrows hcols).cost c = ∑ b, (σ b).cost c := by
  unfold cost
  rw [disjointFamily_edges, Finset.sum_biUnion (edges_pairwiseDisjoint σ hrows)]

end OTSelector.PartialMatching
