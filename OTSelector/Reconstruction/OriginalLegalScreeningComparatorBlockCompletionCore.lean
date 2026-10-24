import OTSelector.Reconstruction.OriginalLegalScreeningComparatorBlockCompletionReachability
import OTSelector.Reconstruction.FinslerRelativeLawLegalRepair

/-! A locally saturated diagonal block core preserves the true original legal rank. -/
open Set Function
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OTSelector.Reconstruction.PartialMatching
variable {m n : ℕ} {β : Type*} [LinearOrder β]

omit [LinearOrder β] in
/-- Saturating one colour in each original block excludes free opposite-colour labels
in the same block. Neither global balance nor a strict Hall premise is needed. -/
theorem free_block_labels_ne_of_saturation
    (c : Fin m → β) (d : Fin n → β) (σ : OTSelector.PartialMatching m n)
    (hsat : ∀ b, (∀ i, c i = b → i ∈ σ.rows) ∨ (∀ j, d j = b → j ∈ σ.cols))
    {i : Fin m} (hi : i ∈ σ.freeRows) {j : Fin n} (hj : j ∈ σ.freeCols) : c i ≠ d j := by
  intro heq
  rcases hsat (c i) with hs | ht
  · exact (Finset.mem_sdiff.mp hi).2 (hs i rfl)
  · exact (Finset.mem_sdiff.mp hj).2 (ht j heq.symm)

/-- The actual legal residual graph supplies precisely the missing global cardinality.
All core pairs stay inside a block, all legal pairs move weakly forward, and every
strictly forward block rectangle is legal. A colour is saturated in each block. -/
theorem legal_residual_capacity_of_ordered_saturated_blocks
    (G : Finset (Fin m × Fin n)) (c : Fin m → β) (d : Fin n → β)
    (σ : OTSelector.PartialMatching m n) (hσ : IsLegal G σ)
    (hsame : ∀ e ∈ σ.edges, c e.1 = d e.2)
    (hforward : ∀ i j, (i,j) ∈ G → c i ≤ d j)
    (hcomplete : ∀ i j, c i < d j → (i,j) ∈ G)
    (hsat : ∀ b, (∀ i, c i = b → i ∈ σ.rows) ∨ (∀ j, d j = b → j ∈ σ.cols)) :
    σ.card + legalMaximumCard (residualAllowed G σ) = legalMaximumCard G := by
  classical
  obtain ⟨τ,hτ,hτmax⟩ := exists_legalMaximumCard (residualAllowed G σ)
  obtain ⟨hr,hc⟩ := residualAllowed_disjoint σ τ hτ
  let U := σ.union τ hr hc
  have hfreeRows {i : Fin m} (hi : i ∈ U.freeRows) : i ∈ σ.freeRows ∧ i ∈ τ.freeRows := by
    simpa only [U,OTSelector.PartialMatching.freeRows,OTSelector.PartialMatching.rows,
      OTSelector.PartialMatching.union_edges,Finset.image_union,Finset.mem_sdiff,Finset.mem_univ,
      true_and,Finset.mem_union,not_or] using hi
  have hfreeCols {j : Fin n} (hj : j ∈ U.freeCols) : j ∈ σ.freeCols ∧ j ∈ τ.freeCols := by
    simpa only [U,OTSelector.PartialMatching.freeCols,OTSelector.PartialMatching.cols,
      OTSelector.PartialMatching.union_edges,Finset.image_union,Finset.mem_sdiff,Finset.mem_univ,
      true_and,Finset.mem_union,not_or] using hj
  have hreach : ∀ i, alternatingReachable G U i →
      ∃ r, r ∈ σ.freeRows ∧ alternatingReachable (residualAllowed G σ) τ r ∧ c r ≤ c i := by
    rintro i ⟨i₀,hi₀,hpath⟩
    obtain ⟨hσfree,hτfree⟩ := hfreeRows hi₀
    induction hpath with
    | refl => exact ⟨i₀,hσfree,alternatingReachable_of_free hτfree,le_rfl⟩
    | @tail a b hpath hstep ih =>
      obtain ⟨r,hrfree,hrreach,hrle⟩ := ih
      obtain ⟨j,hij,hold⟩ := hstep
      rcases Finset.mem_union.mp hold with hcore | hres
      · refine ⟨r,hrfree,hrreach,?_⟩
        exact hrle.trans ((hforward a j hij).trans_eq (hsame _ hcore).symm)
      · have hh := Finset.mem_filter.mp (hτ hres)
        have hjfree : j ∈ σ.freeCols := Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,hh.2.2⟩
        have hlt : c r < d j := lt_of_le_of_ne (hrle.trans (hforward a j hij))
          (free_block_labels_ne_of_saturation c d σ hsat hrfree hjfree)
        have hrj : (r,j) ∈ residualAllowed G σ :=
          Finset.mem_filter.mpr ⟨hcomplete r j hlt,(Finset.mem_sdiff.mp hrfree).2,hh.2.2⟩
        exact ⟨b,Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,hh.2.1⟩,
          alternatingReachable_step hrreach ⟨j,hrj,hres⟩,le_rfl⟩
  have hno : ∀ i, alternatingReachable G U i → ∀ j ∈ U.freeCols, (i,j) ∉ G := by
    intro i hi j hj hij
    obtain ⟨r,hrfree,hrreach,hrle⟩ := hreach i hi
    obtain ⟨hjσ,hjτ⟩ := hfreeCols hj
    have hlt : c r < d j := lt_of_le_of_ne (hrle.trans (hforward i j hij))
      (free_block_labels_ne_of_saturation c d σ hsat hrfree hjσ)
    have hrj : (r,j) ∈ residualAllowed G σ :=
      Finset.mem_filter.mpr ⟨hcomplete r j hlt,(Finset.mem_sdiff.mp hrfree).2,
        (Finset.mem_sdiff.mp hjσ).2⟩
    exact no_reachable_free_target_of_card_eq_legalMaximum τ hτ hτmax r hrreach j hjτ hrj
  apply le_antisymm (core_add_residualCapacity_le σ hσ)
  obtain ⟨M,hM,hMmax⟩ := exists_legalMaximumCard G
  have hcard := card_le_of_no_reachable_free_target U M hM hno
  rw [hMmax,OTSelector.PartialMatching.card_union,hτmax] at hcard
  exact hcard

end OTSelector.Reconstruction.PartialMatching
