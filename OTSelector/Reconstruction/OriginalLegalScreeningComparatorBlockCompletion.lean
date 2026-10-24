import OTSelector.Reconstruction.OriginalLegalScreeningComparatorBlockCompletionCore
import OTSelector.Finite.MatchingBlockCompletionCounts

/-! Actual forward-block repair retains every core pair and reaches the true legal rank. -/
open Set Function
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OTSelector.Reconstruction.PartialMatching
variable {m n : ℕ} {β : Type*} [Fintype β] [LinearOrder β]

/-- A genuine residual matching on the unused original indices completes a locally
saturated same-block core to the original graph's true maximum. Every new pair crosses
strictly forward; all old pairs are retained. The literal new-edge count is bounded by
the sum of the original blocks' colour-count absolute differences, with additive actual
cost for every signed cost function. Empty blocks and empty arrays are included. -/
theorem exists_legalMaximum_completion_of_ordered_saturated_blocks
    (G : Finset (Fin m × Fin n)) (c : Fin m → β) (d : Fin n → β)
    (σ : OTSelector.PartialMatching m n) (hσ : IsLegal G σ)
    (hsame : ∀ e ∈ σ.edges, c e.1 = d e.2)
    (hforward : ∀ i j, (i,j) ∈ G → c i ≤ d j)
    (hcomplete : ∀ i j, c i < d j → (i,j) ∈ G)
    (hsat : ∀ b, (∀ i, c i = b → i ∈ σ.rows) ∨ (∀ j, d j = b → j ∈ σ.cols)) :
    ∃ τ κ : OTSelector.PartialMatching m n,
      IsLegal (residualAllowed G σ) τ ∧
      (∀ e ∈ τ.edges, c e.1 < d e.2) ∧
      τ.rows ⊆ σ.freeRows ∧ τ.cols ⊆ σ.freeCols ∧
      IsLegal G κ ∧ κ.card = legalMaximumCard G ∧
      κ.edges = σ.edges ∪ τ.edges ∧ σ.edges ⊆ κ.edges ∧
      κ.card = σ.card + τ.card ∧ (κ.edges \ σ.edges).card = τ.card ∧
      τ.card ≤ ∑ b, Nat.dist (Finset.univ.filter (fun i ↦ c i = b)).card
        (Finset.univ.filter (fun j ↦ d j = b)).card ∧
      ∀ cost : Fin m → Fin n → ℝ, κ.cost cost = σ.cost cost + τ.cost cost := by
  classical
  obtain ⟨τ,hτ,hτmax⟩ := exists_legalMaximumCard (residualAllowed G σ)
  obtain ⟨hr,hc⟩ := residualAllowed_disjoint σ τ hτ
  let κ := σ.union τ hr hc
  have hrows : τ.rows ⊆ σ.freeRows := by
    intro i hi
    obtain ⟨e,he,rfl⟩ := Finset.mem_image.mp hi
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp (hτ he)).2.1⟩
  have hcols : τ.cols ⊆ σ.freeCols := by
    intro j hj
    obtain ⟨e,he,rfl⟩ := Finset.mem_image.mp hj
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp (hτ he)).2.2⟩
  have hstrict : ∀ e ∈ τ.edges, c e.1 < d e.2 := by
    intro e he
    have hh := Finset.mem_filter.mp (hτ he)
    exact lt_of_le_of_ne (hforward _ _ hh.1)
      (free_block_labels_ne_of_saturation c d σ hsat
        (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,hh.2.1⟩)
        (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,hh.2.2⟩))
  have hcard : κ.card = σ.card + τ.card := OTSelector.PartialMatching.card_union σ τ hr hc
  have hmax : κ.card = legalMaximumCard G := by
    rw [hcard,hτmax]
    exact legal_residual_capacity_of_ordered_saturated_blocks G c d σ hσ hsame hforward hcomplete hsat
  have hdis : Disjoint σ.edges τ.edges := by
    apply Finset.disjoint_left.mpr
    intro e he he'
    exact Finset.disjoint_left.mp hr
      (Finset.mem_image.mpr ⟨e,he,rfl⟩) (Finset.mem_image.mpr ⟨e,he',rfl⟩)
  have hnew : κ.edges \ σ.edges = τ.edges := Finset.union_sdiff_cancel_left hdis
  have hbound : τ.card ≤ ∑ b, Nat.dist (Finset.univ.filter (fun i ↦ c i = b)).card
      (Finset.univ.filter (fun j ↦ d j = b)).card := by
    rw [← free_endpoints_eq_sum_block_discrepancy c d σ hsame hsat]
    exact ((τ.card_rows.symm.le).trans (Finset.card_le_card hrows)).trans (Nat.le_add_right _ _)
  exact ⟨τ,κ,hτ,hstrict,hrows,hcols,isLegal_union_residual σ τ hσ hτ,hmax,rfl,
    Finset.subset_union_left,hcard,congrArg Finset.card hnew,hbound,
    fun cost ↦ OTSelector.PartialMatching.cost_union cost σ τ hr hc⟩

end OTSelector.Reconstruction.PartialMatching
