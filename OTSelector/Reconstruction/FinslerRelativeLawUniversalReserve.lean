import OTSelector.Reconstruction.FinslerRelativeLawLegalRepair
import Mathlib.Combinatorics.Hall.Basic

/-!
Finite legal reserve completion for arbitrary selected orphan sets.
No probability law is assigned to the orphans or surviving reserve points.
-/

open Set MeasureTheory
open scoped BigOperators
noncomputable section
namespace OTSelector.Reconstruction.PartialMatching

variable {m n : ℕ}

/-- Universal source and target reserve classes force the exact residual
capacity needed for a legal completion. The selected non-reserve endpoints may
have been chosen adaptively. -/
theorem exists_legal_completion_of_universal_reserves
    {allowed : Finset (Fin m × Fin n)} (σ : OTSelector.PartialMatching m n)
    (hσ : IsLegal allowed σ) (hmn : m ≤ n)
    (RS : Finset σ.freeRows) (RT : Finset σ.freeCols)
    (hsource : ∀ i ∈ RS, ∀ j : σ.freeCols, (i.val, j.val) ∈ allowed)
    (htarget : ∀ i : σ.freeRows, ∀ j ∈ RT, (i.val, j.val) ∈ allowed)
    (hcapacity : Fintype.card σ.freeRows - RS.card ≤ RT.card) :
    ∃ τ : OTSelector.PartialMatching m n,
      IsLegal allowed τ ∧ τ.card = min m n ∧ σ.edges ⊆ τ.edges := by
  classical
  have hcounts : Fintype.card σ.freeRows ≤ Fintype.card σ.freeCols := by
    simp only [Fintype.card_coe, OTSelector.PartialMatching.card_freeRows,
      OTSelector.PartialMatching.card_freeCols]
    omega
  let rel : σ.freeRows → σ.freeCols → Prop := fun i j ↦ (i.val, j.val) ∈ allowed
  have hhall : ∀ A : Finset σ.freeRows,
      A.card ≤ (Finset.univ.filter fun j ↦ ∃ i ∈ A, rel i j).card := by
    intro A
    by_cases hA : ∃ i ∈ A, i ∈ RS
    · obtain ⟨i, hi, hiR⟩ := hA
      have heq : (Finset.univ.filter fun j ↦ ∃ i ∈ A, rel i j) = Finset.univ := by
        ext j
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
        exact ⟨i, hi, hsource i hiR j⟩
      rw [heq, Finset.card_univ]
      exact (Finset.card_le_univ A).trans hcounts
    · have hsub : A ⊆ Finset.univ \ RS := by
        intro i hi
        exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, fun hr ↦ hA ⟨i, hi, hr⟩⟩
      have hsize : A.card ≤ RT.card :=
        (Finset.card_le_card hsub).trans (by
          rw [Finset.card_sdiff_of_subset (Finset.subset_univ RS), Finset.card_univ]
          exact hcapacity)
      by_cases hne : A.Nonempty
      · obtain ⟨i, hi⟩ := hne
        have hR : RT ⊆ Finset.univ.filter fun j ↦ ∃ i ∈ A, rel i j := by
          intro j hj
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, i, hi, htarget i j hj⟩
        exact hsize.trans (Finset.card_le_card hR)
      · simp [Finset.not_nonempty_iff_eq_empty.mp hne]
  obtain ⟨f, hf, hrel⟩ :=
    (Fintype.all_card_le_filter_rel_iff_exists_injective rel).mp hhall
  let ρ : OTSelector.PartialMatching m n :=
    { edges := Finset.univ.image fun i : σ.freeRows ↦ (i.val, (f i).val)
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
  have hρ : IsLegal (residualAllowed allowed σ) ρ := by
    intro e he
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp he
    apply Finset.mem_filter.mpr
    exact ⟨hrel i, (Finset.mem_sdiff.mp i.property).2,
      (Finset.mem_sdiff.mp (f i).property).2⟩
  have hρcard : ρ.card = m - σ.card := by
    dsimp only [OTSelector.PartialMatching.card, ρ]
    rw [Finset.card_image_of_injective _ (fun i j h ↦ Subtype.ext (Prod.mk.inj h).1),
      Finset.card_univ, Fintype.card_coe, OTSelector.PartialMatching.card_freeRows]
    rfl
  obtain ⟨hr, hc⟩ := residualAllowed_disjoint σ ρ hρ
  let τ := σ.union ρ hr hc
  refine ⟨τ, isLegal_union_residual σ ρ hσ hρ, ?_, Finset.subset_union_left⟩
  dsimp only [τ]
  rw [OTSelector.PartialMatching.card_union, hρcard, min_eq_left hmn]
  have := σ.card_le.trans (min_le_left m n)
  omega

/-- The universal-reserve conditions give the exact capacity equality, rather
than merely a lower bound on the unconstrained legal maximum. -/
theorem residual_capacity_of_universal_reserves
    {allowed : Finset (Fin m × Fin n)} (σ : OTSelector.PartialMatching m n)
    (hσ : IsLegal allowed σ) (hmn : m ≤ n)
    (RS : Finset σ.freeRows) (RT : Finset σ.freeCols)
    (hsource : ∀ i ∈ RS, ∀ j : σ.freeCols, (i.val, j.val) ∈ allowed)
    (htarget : ∀ i : σ.freeRows, ∀ j ∈ RT, (i.val, j.val) ∈ allowed)
    (hcapacity : Fintype.card σ.freeRows - RS.card ≤ RT.card) :
    legalMaximumCard allowed = min m n ∧
      σ.card + legalMaximumCard (residualAllowed allowed σ) = legalMaximumCard allowed := by
  obtain ⟨τ, hτ, hcard, hsub⟩ :=
    exists_legal_completion_of_universal_reserves σ hσ hmn RS RT hsource htarget hcapacity
  have hfull : legalMaximumCard allowed = min m n := by
    apply le_antisymm (legalMaximumCard_le_min _)
    rw [← hcard]
    exact card_le_legalMaximumCard hτ
  exact ⟨hfull, residual_capacity_of_legal_completion σ τ hσ hτ hsub (hcard.trans hfull.symm)⟩

end OTSelector.Reconstruction.PartialMatching
