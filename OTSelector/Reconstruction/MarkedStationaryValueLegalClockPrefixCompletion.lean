import OTSelector.Reconstruction.FinslerRelativeLawUniversalReserve
import OTSelector.Reconstruction.MarkedStationaryValueLegalTypes

/-!
# Actual strict-clock prefix counts complete a retained legal core

Nested neighborhoods of the scalar clock order reduce all finite Hall subset
conditions to suffix counts at the actual remaining source clocks. The legal
extension is constructed on the original unused source and target indices,
retaining every edge of the original core and allowing interleaved clocks.
-/
open Set Function
open scoped BigOperators Classical
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000

/-- Counting a predicate on the original selected indices agrees with counting
it on the finite subtype, without changing any original observation. -/
theorem card_univ_filter_finset_subtype {α : Type*} [DecidableEq α]
    (s : Finset α) (p : α → Prop) [DecidablePred p] :
    (Finset.univ.filter (fun x : s ↦ p x.val)).card = (s.filter p).card := by
  calc
    _ = (s.attach.filter (fun x : s ↦ p x.val)).card := rfl
    _ = _ := by rw [Finset.filter_attach, Finset.card_map, Finset.card_attach]

/-- For an actual finite strict-clock graph, the suffix counts at source
clocks imply every Hall condition and construct a legal injection. -/
theorem exists_injective_forward_of_clock_prefix_counts
    {S T : Type*} [Fintype S] [Fintype T]
    (source : S → ℝ) (target : T → ℝ)
    (hprefix : ∀ i : S,
      (Finset.univ.filter (fun i' : S ↦ source i ≤ source i')).card ≤
        (Finset.univ.filter (fun j : T ↦ source i < target j)).card) :
    ∃ f : S → T, Injective f ∧ ∀ i, source i < target (f i) := by
  classical
  let rel : S → T → Prop := fun i j ↦ source i < target j
  apply (Fintype.all_card_le_filter_rel_iff_exists_injective rel).mp
  intro A
  by_cases hA : A.Nonempty
  · obtain ⟨i, hi, hmin⟩ := Finset.exists_min_image A source hA
    have hsource : A ⊆ Finset.univ.filter (fun i' : S ↦ source i ≤ source i') := by
      intro i' hi'
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hmin i' hi'⟩
    have htarget : (Finset.univ.filter (fun j : T ↦ source i < target j)) ⊆
        Finset.univ.filter (fun j : T ↦ ∃ i' ∈ A, rel i' j) := by
      intro j hj
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, i, hi, (Finset.mem_filter.mp hj).2⟩
    exact (Finset.card_le_card hsource).trans ((hprefix i).trans (Finset.card_le_card htarget))
  · simp [Finset.not_nonempty_iff_eq_empty.mp hA]

/-- The scalar suffix counts are also necessary for a full legal injection. -/
theorem clock_prefix_counts_of_injective_forward
    {S T : Type*} [Fintype S] [Fintype T]
    (source : S → ℝ) (target : T → ℝ)
    (f : S → T) (hf : Injective f) (hlegal : ∀ i, source i < target (f i)) :
    ∀ i : S,
      (Finset.univ.filter (fun i' : S ↦ source i ≤ source i')).card ≤
        (Finset.univ.filter (fun j : T ↦ source i < target j)).card := by
  classical
  intro i
  apply Finset.card_le_card_of_injOn f
  · intro i' hi'
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      ((Finset.mem_filter.mp hi').2).trans_lt (hlegal i')⟩
  · intro i' hi' i'' hi'' heq
    exact hf heq

namespace PartialMatching
variable {m n : ℕ}

/-- Actual unused clock suffix counts produce a complete source matching
which preserves every original legal core edge. No residual-capacity oracle,
independence assertion, or global ordering of the two clocks is assumed. -/
theorem exists_legal_clock_completion_of_free_prefix_counts
    (source : Fin m → ℝ) (target : Fin n → ℝ)
    (σ : OTSelector.PartialMatching m n)
    (hσ : IsLegal (scalarClockLegalGraph source target) σ)
    (hprefix : ∀ i ∈ σ.freeRows,
      (σ.freeRows.filter (fun i' ↦ source i ≤ source i')).card ≤
        (σ.freeCols.filter (fun j ↦ source i < target j)).card) :
    ∃ τ : OTSelector.PartialMatching m n,
      IsLegal (scalarClockLegalGraph source target) τ ∧ τ.card = m ∧ σ.edges ⊆ τ.edges := by
  classical
  have hprefix' (i : σ.freeRows) :
      (Finset.univ.filter (fun i' : σ.freeRows ↦ source i.val ≤ source i'.val)).card ≤
        (Finset.univ.filter (fun j : σ.freeCols ↦ source i.val < target j.val)).card := by
    rw [card_univ_filter_finset_subtype σ.freeRows (fun i' : Fin m ↦ source i.val ≤ source i'),
      card_univ_filter_finset_subtype σ.freeCols (fun j : Fin n ↦ source i.val < target j)]
    exact hprefix i.val i.property
  obtain ⟨f, hf, hrel⟩ := exists_injective_forward_of_clock_prefix_counts
    (fun i : σ.freeRows ↦ source i.val) (fun j : σ.freeCols ↦ target j.val) hprefix'
  let ρ : OTSelector.PartialMatching m n :=
    { edges := Finset.univ.image (fun i : σ.freeRows ↦ (i.val, (f i).val))
      row_inj := by
        intro e he e' he' heq
        obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp he
        obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp he'
        exact congrArg (fun i : σ.freeRows ↦ (i.val, (f i).val)) (Subtype.ext heq)
      col_inj := by
        intro e he e' he' heq
        obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp he
        obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp he'
        exact congrArg (fun i : σ.freeRows ↦ (i.val, (f i).val)) (hf (Subtype.ext heq)) }
  have hρ : IsLegal (residualAllowed (scalarClockLegalGraph source target) σ) ρ := by
    intro e he
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp he
    apply Finset.mem_filter.mpr
    refine ⟨?_, (Finset.mem_sdiff.mp i.property).2, (Finset.mem_sdiff.mp (f i).property).2⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hrel i⟩
  have hρcard : ρ.card = m - σ.card := by
    dsimp only [OTSelector.PartialMatching.card, ρ]
    rw [Finset.card_image_of_injective _ (fun i j h ↦ Subtype.ext (Prod.mk.inj h).1),
      Finset.card_univ, Fintype.card_coe, OTSelector.PartialMatching.card_freeRows]
    rfl
  obtain ⟨hr, hc⟩ := residualAllowed_disjoint σ ρ hρ
  let τ := σ.union ρ hr hc
  refine ⟨τ, isLegal_union_residual σ ρ hσ hρ, ?_, Finset.subset_union_left⟩
  dsimp only [τ]
  rw [OTSelector.PartialMatching.card_union, hρcard]
  have := σ.card_le.trans (min_le_left m n)
  omega

/-- Prefix feasibility identifies the actual strict-clock legal maximum as
all original source indices; the original core also has full legal residual
capacity for the exact residual optimal repair. -/
theorem legal_capacity_of_free_clock_prefix_counts
    (source : Fin m → ℝ) (target : Fin n → ℝ)
    (σ : OTSelector.PartialMatching m n)
    (hσ : IsLegal (scalarClockLegalGraph source target) σ)
    (hprefix : ∀ i ∈ σ.freeRows,
      (σ.freeRows.filter (fun i' ↦ source i ≤ source i')).card ≤
        (σ.freeCols.filter (fun j ↦ source i < target j)).card) :
    legalMaximumCard (scalarClockLegalGraph source target) = m ∧
      σ.card + legalMaximumCard (residualAllowed (scalarClockLegalGraph source target) σ) = m := by
  obtain ⟨τ, hτ, hcard, hsub⟩ :=
    exists_legal_clock_completion_of_free_prefix_counts source target σ hσ hprefix
  have hfull : legalMaximumCard (scalarClockLegalGraph source target) = m := by
    apply le_antisymm ((legalMaximumCard_le_min _).trans (min_le_left _ _))
    exact hcard.symm.trans_le (card_le_legalMaximumCard hτ)
  exact ⟨hfull, (residual_capacity_of_legal_completion σ τ hσ hτ hsub
    (hcard.trans hfull.symm)).trans hfull⟩

end PartialMatching
end OTSelector.Reconstruction
