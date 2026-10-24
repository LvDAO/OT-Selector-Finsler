import OTSelector.Finite.MatchingFamily
import OTSelector.Finite.PartialMatching
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Reconstruction.OriginalLegalScreeningComparatorBlockUnionCore.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Reconstruction.OriginalLegalScreeningComparatorBlockUnionCore`; the selected original proof blocks follow. -/
section

/-!
# Reconstruction.OriginalLegalScreeningComparatorBlockUnionCore

**Conditions:** A finite family of original-index matchings has its source and target endpoints in the same prescribed block label.

**Objects:** One ambient disjoint matching union, additive costs/counts and saturation in every block.

**Proof detail:** Different labels force disjoint endpoint sets, so the common disjoint-family construction applies; a block matching of minimum block cardinality saturates at least one of its two sides.

**Sources:** [Reinhard Diestel, Graph Theory, 4th electronic edition (2010), corrected reprint 2012](https://diestel-graph-theory.com/Sample.pdf#page=2), Chapter 2 opening matching definition and Section 2.1, first three chapter pages; [Terence Tao, Analysis I](https://github.com/teorth/analysis/blob/main/Analysis/Section_7_1.lean), Sections 4.3 (absolute value) and 7.1 (finite series), in particular Proposition 7.1.11; [OTSelector project, Original strict-screen residual slack and repair](main.tex#strict-screen-residual-slack), main.tex label strict-screen-residual-slack, line 6749.

Source relation (adapter): The cited sections provide the stated mathematical foundations; the exact finite construction and quantitative bound in this module are local consequences, not a claim that the book states the Lean theorem verbatim.
-/

/-! Assemble actual finite matching blocks on their unchanged original indices. -/
open Set Function
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OTSelector.Reconstruction.PartialMatching
variable {m n : ℕ} {β : Type*} [Fintype β]

omit [Fintype β] in
/-- Distinct source blocks have disjoint used original rows. -/
theorem matchingFamily_rows_disjoint_of_labels (c : Fin m → β)
    (ζ : β → OTSelector.PartialMatching m n)
    (h : ∀ b e, e ∈ (ζ b).edges → c e.1 = b) :
    Pairwise (fun b b' ↦ Disjoint (ζ b).rows (ζ b').rows) := by
  intro b b' hbb
  apply Finset.disjoint_left.mpr
  intro i hi hi'
  obtain ⟨e,he,heq⟩ := Finset.mem_image.mp hi
  obtain ⟨e',he',heq'⟩ := Finset.mem_image.mp hi'
  exact hbb ((h b e he).symm.trans ((congrArg c (heq.trans heq'.symm)).trans (h b' e' he')))

omit [Fintype β] in
/-- Distinct target blocks have disjoint used original columns. -/
theorem matchingFamily_cols_disjoint_of_labels (d : Fin n → β)
    (ζ : β → OTSelector.PartialMatching m n)
    (h : ∀ b e, e ∈ (ζ b).edges → d e.2 = b) :
    Pairwise (fun b b' ↦ Disjoint (ζ b).cols (ζ b').cols) := by
  intro b b' hbb
  apply Finset.disjoint_left.mpr
  intro j hj hj'
  obtain ⟨e,he,heq⟩ := Finset.mem_image.mp hj
  obtain ⟨e',he',heq'⟩ := Finset.mem_image.mp hj'
  exact hbb ((h b e he).symm.trans ((congrArg d (heq.trans heq'.symm)).trans (h b' e' he')))

/-- The literal union of local block matchings, with capacities inferred from labels. -/
def orderedBlockMatchingUnion (c : Fin m → β) (d : Fin n → β)
    (ζ : β → OTSelector.PartialMatching m n)
    (h : ∀ b e, e ∈ (ζ b).edges → c e.1 = b ∧ d e.2 = b) : OTSelector.PartialMatching m n :=
  OTSelector.PartialMatching.disjointFamily ζ
    (matchingFamily_rows_disjoint_of_labels c ζ (fun b e he ↦ (h b e he).1))
    (matchingFamily_cols_disjoint_of_labels d ζ (fun b e he ↦ (h b e he).2))

/-- Each local pair occurs in the actual union on the same original indices. -/
theorem edges_subset_orderedBlockMatchingUnion (c : Fin m → β) (d : Fin n → β)
    (ζ : β → OTSelector.PartialMatching m n)
    (h : ∀ b e, e ∈ (ζ b).edges → c e.1 = b ∧ d e.2 = b) (b : β) :
    (ζ b).edges ⊆ (orderedBlockMatchingUnion c d ζ h).edges := by
  classical
  intro e he
  exact Finset.mem_biUnion.mpr ⟨b,Finset.mem_univ _,he⟩

/-- Local cardinalities and every signed cost add exactly; all union pairs stay in a block. -/
theorem orderedBlockMatchingUnion_spec (c : Fin m → β) (d : Fin n → β)
    (ζ : β → OTSelector.PartialMatching m n)
    (h : ∀ b e, e ∈ (ζ b).edges → c e.1 = b ∧ d e.2 = b) :
    (orderedBlockMatchingUnion c d ζ h).card = ∑ b, (ζ b).card ∧
    (∀ cost : Fin m → Fin n → ℝ,
      (orderedBlockMatchingUnion c d ζ h).cost cost = ∑ b, (ζ b).cost cost) ∧
    ∀ e ∈ (orderedBlockMatchingUnion c d ζ h).edges, c e.1 = d e.2 := by
  classical
  refine ⟨OTSelector.PartialMatching.disjointFamily_card _ _ _,
    fun cost ↦ OTSelector.PartialMatching.disjointFamily_cost _ _ _ cost,?_⟩
  intro e he
  obtain ⟨b,_,hb⟩ := Finset.mem_biUnion.mp he
  exact (h b e hb).1.trans (h b e hb).2.symm

/-- A local minimum-colour cardinality forces actual saturation of one colour in every
original block. The larger-colour indices need not all be matched. -/
theorem orderedBlockMatchingUnion_saturates
    [DecidableEq β] (c : Fin m → β) (d : Fin n → β)
    (ζ : β → OTSelector.PartialMatching m n)
    (h : ∀ b e, e ∈ (ζ b).edges → c e.1 = b ∧ d e.2 = b)
    (hcard : ∀ b, (ζ b).card = min (Finset.univ.filter (fun i ↦ c i = b)).card
      (Finset.univ.filter (fun j ↦ d j = b)).card) :
    ∀ b, (∀ i, c i = b → i ∈ (orderedBlockMatchingUnion c d ζ h).rows) ∨
      (∀ j, d j = b → j ∈ (orderedBlockMatchingUnion c d ζ h).cols) := by
  classical
  intro b
  have hrows : (ζ b).rows ⊆ Finset.univ.filter (fun i ↦ c i = b) := by
    intro i hi
    obtain ⟨e,he,rfl⟩ := Finset.mem_image.mp hi
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(h b e he).1⟩
  have hcols : (ζ b).cols ⊆ Finset.univ.filter (fun j ↦ d j = b) := by
    intro j hj
    obtain ⟨e,he,rfl⟩ := Finset.mem_image.mp hj
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(h b e he).2⟩
  rcases le_total (Finset.univ.filter (fun i ↦ c i = b)).card
      (Finset.univ.filter (fun j ↦ d j = b)).card with hs | ht
  · left
    have heq := Finset.eq_of_subset_of_card_le hrows (by
      rw [(ζ b).card_rows,hcard b,min_eq_left hs])
    intro i hi
    have hh : i ∈ (ζ b).rows := heq.symm ▸ Finset.mem_filter.mpr ⟨Finset.mem_univ _,hi⟩
    obtain ⟨e,he,rfl⟩ := Finset.mem_image.mp hh
    exact Finset.mem_image.mpr ⟨e,edges_subset_orderedBlockMatchingUnion c d ζ h b he,rfl⟩
  · right
    have heq := Finset.eq_of_subset_of_card_le hcols (by
      rw [(ζ b).card_cols,hcard b,min_eq_right ht])
    intro j hj
    have hh : j ∈ (ζ b).cols := heq.symm ▸ Finset.mem_filter.mpr ⟨Finset.mem_univ _,hj⟩
    obtain ⟨e,he,rfl⟩ := Finset.mem_image.mp hh
    exact Finset.mem_image.mpr ⟨e,edges_subset_orderedBlockMatchingUnion c d ζ h b he,rfl⟩

end OTSelector.Reconstruction.PartialMatching

end
end
