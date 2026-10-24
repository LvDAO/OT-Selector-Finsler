import OTSelector.Finite.MatchingUnion
import OTSelector.Finite.PartialMatching
import OTSelector.Probability.CellRefinedMarkComponents
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Reconstruction.FinslerRelativeLawOriginalFineMatchingAssembly.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Reconstruction.FinslerRelativeLawOriginalFineMatchingAssembly`; the selected original proof blocks follow. -/
section

/-!
# Reconstruction.FinslerRelativeLawOriginalFineMatchingAssembly

**Conditions:** Good/bad matchings use different sum-type tags on the same original row/column indices; cell decomposition assumes each retained edge has a cell tag.

**Objects:** Collision-free matching union and exact finite cellwise cardinality/cost decomposition.

**Proof detail:** Distinct constructors make both endpoint sets disjoint, so MatchingUnion applies; filter the same original edge set by cell tags and sum the mutually exclusive finite indicators.

**Sources:** [Reinhard Diestel, Graph Theory, 4th electronic edition (2010), corrected reprint 2012](https://diestel-graph-theory.com/Sample.pdf#page=2), Chapter 2 opening matching definition and Section 2.1, first three chapter pages; [Terence Tao, Analysis I](https://github.com/teorth/analysis/blob/main/Analysis/Section_7_1.lean), Sections 4.3 (absolute value) and 7.1 (finite series), in particular Proposition 7.1.11.

Source relation (adapter): The cited sections provide the stated mathematical foundations; the exact finite construction and quantitative bound in this module are local consequences, not a claim that the book states the Lean theorem verbatim.
-/

/-! Good and bad retained cores on the same original fine indices assemble without any collisions. -/
open Set Function
open scoped BigOperators Classical
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false

variable {C T : Type*} {m n : ℕ}

/-- The disjoint fine constructors certify disjoint original source indices. -/
theorem fine_good_bad_matching_rows_disjoint
    (sourceTag : Fin m → Option (CellRefinedType C T))
    (good bad : OTSelector.PartialMatching m n)
    (hg : ∀ e ∈ good.edges, ∃ t, sourceTag e.1 = some (.inl (true, t)))
    (hb : ∀ e ∈ bad.edges, ∃ p : C × T, sourceTag e.1 = some (.inr p)) :
    Disjoint good.rows bad.rows := by
  classical
  apply Finset.disjoint_left.mpr
  intro i hi hj
  obtain ⟨e, he, hei⟩ := Finset.mem_image.mp hi
  obtain ⟨f, hf, hfi⟩ := Finset.mem_image.mp hj
  obtain ⟨t, ht⟩ := hg e he
  obtain ⟨p, hp⟩ := hb f hf
  rw [hei] at ht
  rw [hfi] at hp
  cases Option.some.inj (ht.symm.trans hp)

/-- The same disjoint fine constructors certify disjoint original target indices. -/
theorem fine_good_bad_matching_cols_disjoint
    (targetTag : Fin n → Option (CellRefinedType C T))
    (good bad : OTSelector.PartialMatching m n)
    (hg : ∀ e ∈ good.edges, ∃ t, targetTag e.2 = some (.inl (true, t)))
    (hb : ∀ e ∈ bad.edges, ∃ p : C × T, targetTag e.2 = some (.inr p)) :
    Disjoint good.cols bad.cols := by
  classical
  apply Finset.disjoint_left.mpr
  intro j hi hj
  obtain ⟨e, he, hei⟩ := Finset.mem_image.mp hi
  obtain ⟨f, hf, hfi⟩ := Finset.mem_image.mp hj
  obtain ⟨t, ht⟩ := hg e he
  obtain ⟨p, hp⟩ := hb f hf
  rw [hei] at ht
  rw [hfi] at hp
  cases Option.some.inj (ht.symm.trans hp)

/-- The actual good and bad retained cores have a union on their unchanged original indices. -/
theorem exists_fine_good_bad_matching_union
    (sourceTag : Fin m → Option (CellRefinedType C T))
    (targetTag : Fin n → Option (CellRefinedType C T))
    (good bad : OTSelector.PartialMatching m n)
    (hg : ∀ e ∈ good.edges,
      (∃ t, sourceTag e.1 = some (.inl (true, t))) ∧
        (∃ t, targetTag e.2 = some (.inl (true, t))))
    (hb : ∀ e ∈ bad.edges,
      (∃ p : C × T, sourceTag e.1 = some (.inr p)) ∧
        (∃ p : C × T, targetTag e.2 = some (.inr p))) :
    ∃ merged : OTSelector.PartialMatching m n,
      merged.edges = good.edges ∪ bad.edges ∧ merged.card = good.card + bad.card ∧
      ∀ cost : Fin m → Fin n → ℝ, merged.cost cost = good.cost cost + bad.cost cost := by
  have hr := fine_good_bad_matching_rows_disjoint sourceTag good bad
    (fun e he ↦ (hg e he).1) (fun e he ↦ (hb e he).1)
  have hc := fine_good_bad_matching_cols_disjoint targetTag good bad
    (fun e he ↦ (hg e he).2) (fun e he ↦ (hb e he).2)
  exact ⟨good.union bad hr hc, rfl, OTSelector.PartialMatching.card_union good bad hr hc,
    fun cost ↦ OTSelector.PartialMatching.cost_union cost good bad hr hc⟩

/-- The original edges in one retained source cell, with no change of enumeration. -/
def originalMatchingCell {Cell : Type*} (σ : OTSelector.PartialMatching m n)
    (sourceCell : Fin m → Option Cell) (c : Cell) : OTSelector.PartialMatching m n :=
  σ.subMatching (σ.edges.filter (fun e ↦ sourceCell e.1 = some c)) (Finset.filter_subset _ _)

@[simp]
theorem mem_originalMatchingCell {Cell : Type*} (σ : OTSelector.PartialMatching m n)
    (sourceCell : Fin m → Option Cell) (c : Cell) (e : Fin m × Fin n) :
    e ∈ (originalMatchingCell σ sourceCell c).edges ↔ e ∈ σ.edges ∧ sourceCell e.1 = some c :=
  Finset.mem_filter

/-- Splitting a same-cell core does not multiply its physical cost. -/
theorem sum_originalMatchingCell_cost {Cell : Type*} [Fintype Cell]
    (σ : OTSelector.PartialMatching m n) (sourceCell : Fin m → Option Cell)
    (hcell : ∀ e ∈ σ.edges, ∃ c, sourceCell e.1 = some c)
    (cost : Fin m → Fin n → ℝ) :
    (∑ c, (originalMatchingCell σ sourceCell c).cost cost) = σ.cost cost := by
  classical
  have hnone : (σ.edges.filter (fun e ↦ sourceCell e.1 = none)) = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro e he
    obtain ⟨heσ, he0⟩ := Finset.mem_filter.mp he
    obtain ⟨c, hc⟩ := hcell e heσ
    rw [hc] at he0
    cases he0
  have h := Finset.sum_fiberwise σ.edges (fun e ↦ sourceCell e.1) (fun e ↦ cost e.1 e.2)
  rw [Fintype.sum_option, hnone, Finset.sum_empty, zero_add] at h
  exact h

/-- The matched cardinality also partitions exactly over the retained cells. -/
theorem sum_originalMatchingCell_card {Cell : Type*} [Fintype Cell]
    (σ : OTSelector.PartialMatching m n) (sourceCell : Fin m → Option Cell)
    (hcell : ∀ e ∈ σ.edges, ∃ c, sourceCell e.1 = some c) :
    (∑ c, (originalMatchingCell σ sourceCell c).card) = σ.card := by
  have h := sum_originalMatchingCell_cost σ sourceCell hcell (fun _ _ ↦ (1 : ℝ))
  have he (τ : OTSelector.PartialMatching m n) : τ.cost (fun _ _ ↦ (1 : ℝ)) = τ.card := by
    simp [OTSelector.PartialMatching.cost, OTSelector.PartialMatching.card]
  simp_rw [he] at h
  exact_mod_cast h

end OTSelector.Reconstruction

end
end
