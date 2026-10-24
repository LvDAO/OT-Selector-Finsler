import OTSelector.Reconstruction.FinslerRelativeLawLegalRepair

/-! Actual legal completion on retained original-label subarrays. -/

open scoped BigOperators

noncomputable section
namespace OTSelector.Reconstruction.PartialMatching

variable {m n : ℕ}

/-- The literal matching graph of a bijection between selected original labels. -/
def subarrayEquivRepair (S : Finset (Fin m)) (T : Finset (Fin n))
    (e : S ≃ T) : OTSelector.PartialMatching m n := by
  classical
  exact
    { edges := Finset.univ.image (fun i : S ↦ (i.val, (e i).val))
      row_inj := by
        intro a ha b hb hab
        obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp ha
        obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hb
        exact congrArg (fun i : S ↦ (i.val, (e i).val)) (Subtype.ext hab)
      col_inj := by
        intro a ha b hb hab
        obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp ha
        obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hb
        exact congrArg (fun i : S ↦ (i.val, (e i).val)) (e.injective (Subtype.ext hab)) }

/-- The actual repair has exactly the selected rows, columns, cardinality,
and signed edge cost, including empty selected sets. -/
theorem subarrayEquivRepair_spec (S : Finset (Fin m)) (T : Finset (Fin n))
    (e : S ≃ T) (c : Fin m → Fin n → ℝ) :
    (subarrayEquivRepair S T e).rows = S ∧
    (subarrayEquivRepair S T e).cols = T ∧
    (subarrayEquivRepair S T e).card = S.card ∧
    (subarrayEquivRepair S T e).cost c = ∑ i : S, c i.val (e i).val := by
  classical
  have hr : (subarrayEquivRepair S T e).rows = S := by
    simp only [OTSelector.PartialMatching.rows, subarrayEquivRepair, Finset.image_image]
    exact Finset.attach_image_val
  have hc : (subarrayEquivRepair S T e).cols = T := by
    ext j
    simp only [OTSelector.PartialMatching.cols, subarrayEquivRepair, Finset.image_image,
      Finset.mem_image, Finset.mem_univ, true_and, Function.comp_apply]
    constructor
    · rintro ⟨i, hi⟩
      exact hi ▸ (e i).property
    · intro hj
      obtain ⟨i, hi⟩ := e.surjective ⟨j, hj⟩
      exact ⟨i, congrArg Subtype.val hi⟩
  refine ⟨hr, hc, ?_, ?_⟩
  · rw [← OTSelector.PartialMatching.card_rows, hr]
  · unfold OTSelector.PartialMatching.cost
    dsimp only [subarrayEquivRepair]
    rw [Finset.sum_image]
    intro i _ j _ hij
    exact Subtype.ext (Prod.mk.inj hij).1

/-- A genuine legal bijection on unused original subarrays constructs a maximum
legal comparator retaining every core edge. The actual selected-label count
proves its maximality, and its signed repair cost is exact. -/
theorem exists_legalMaximum_completion_of_subarrayEquiv
    (G : Finset (Fin m × Fin n)) (σ : OTSelector.PartialMatching m n)
    (hσ : IsLegal G σ) (S : Finset (Fin m)) (T : Finset (Fin n))
    (hS : S ⊆ σ.freeRows) (hT : T ⊆ σ.freeCols)
    (hcount : σ.card + S.card = min m n)
    (e : S ≃ T) (he : ∀ i : S, (i.val, (e i).val) ∈ G)
    (c : Fin m → Fin n → ℝ) :
    ∃ τ : OTSelector.PartialMatching m n,
      IsLegal G τ ∧ τ.card = legalMaximumCard G ∧ σ.edges ⊆ τ.edges ∧
      τ.edges = σ.edges ∪ (subarrayEquivRepair S T e).edges ∧
      τ.cost c = σ.cost c + ∑ i : S, c i.val (e i).val ∧
      legalMaximumValue G c ≤ σ.cost c + ∑ i : S, c i.val (e i).val := by
  classical
  let ρ := subarrayEquivRepair S T e
  obtain ⟨_, _, hρcard, hρcost⟩ := subarrayEquivRepair_spec S T e c
  have hρ : IsLegal (residualAllowed G σ) ρ := by
    intro a ha
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp ha
    exact Finset.mem_filter.mpr ⟨he i, (Finset.mem_sdiff.mp (hS i.property)).2,
      (Finset.mem_sdiff.mp (hT (e i).property)).2⟩
  obtain ⟨hr, hc⟩ := residualAllowed_disjoint σ ρ hρ
  let τ := σ.union ρ hr hc
  have hτlegal : IsLegal G τ := isLegal_union_residual σ ρ hσ hρ
  have hτfull : τ.card = min m n := by
    rw [OTSelector.PartialMatching.card_union, hρcard]
    exact hcount
  have hfull : legalMaximumCard G = min m n := by
    apply le_antisymm (legalMaximumCard_le_min G)
    exact hτfull.symm.trans_le (card_le_legalMaximumCard hτlegal)
  have hτmax : τ.card = legalMaximumCard G := hτfull.trans hfull.symm
  have hcost : τ.cost c = σ.cost c + ∑ i : S, c i.val (e i).val := by
    rw [OTSelector.PartialMatching.cost_union, hρcost]
  exact ⟨τ, hτlegal, hτmax, Finset.subset_union_left, rfl, hcost,
    (legalMaximumValue_le c hτlegal hτmax).trans_eq hcost⟩

end OTSelector.Reconstruction.PartialMatching
