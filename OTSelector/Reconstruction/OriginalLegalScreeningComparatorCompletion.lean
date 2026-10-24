import OTSelector.Reconstruction.FinslerRelativeLawLegalRepair

/-! A genuine legal comparator obtained by adjoining an unused-label bijection. -/

open scoped BigOperators

noncomputable section
namespace OTSelector.Reconstruction.PartialMatching

variable {m n : ℕ}

/-- The literal graph of a bijection between the original unused labels. -/
def freeEquivRepair (σ : OTSelector.PartialMatching m n)
    (e : σ.freeRows ≃ σ.freeCols) : OTSelector.PartialMatching m n := by
  classical
  exact
    { edges := Finset.univ.image (fun i : σ.freeRows ↦ (i.val, (e i).val))
      row_inj := by
        intro a ha b hb hab
        obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp ha
        obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hb
        exact congrArg (fun i : σ.freeRows ↦ (i.val, (e i).val)) (Subtype.ext hab)
      col_inj := by
        intro a ha b hb hab
        obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp ha
        obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hb
        exact congrArg (fun i : σ.freeRows ↦ (i.val, (e i).val))
          (e.injective (Subtype.ext hab)) }

/-- The constructed repair uses exactly the unused rows and columns, with
their true cardinality and exact signed cost. -/
theorem freeEquivRepair_spec (σ : OTSelector.PartialMatching m n)
    (e : σ.freeRows ≃ σ.freeCols) (c : Fin m → Fin n → ℝ) :
    (freeEquivRepair σ e).rows = σ.freeRows ∧
    (freeEquivRepair σ e).cols = σ.freeCols ∧
    (freeEquivRepair σ e).card = σ.freeRows.card ∧
    (freeEquivRepair σ e).cost c = ∑ i : σ.freeRows, c i.val (e i).val := by
  classical
  have hr : (freeEquivRepair σ e).rows = σ.freeRows := by
    simp only [OTSelector.PartialMatching.rows, freeEquivRepair, Finset.image_image]
    exact Finset.attach_image_val
  have hc : (freeEquivRepair σ e).cols = σ.freeCols := by
    ext j
    simp only [OTSelector.PartialMatching.cols, freeEquivRepair, Finset.image_image,
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
    dsimp only [freeEquivRepair]
    rw [Finset.sum_image]
    intro i _ j _ hij
    exact Subtype.ext (Prod.mk.inj hij).1

/-- A real legal repair produces a maximum comparator containing the entire
retained core. Its exact signed cost bounds the legal maximum-cardinality value;
the full legal rank is proved from the constructed matching itself. -/
theorem exists_legalMaximum_completion_of_freeEquiv
    (G : Finset (Fin m × Fin n)) (σ : OTSelector.PartialMatching m n)
    (hσ : IsLegal G σ) (e : σ.freeRows ≃ σ.freeCols)
    (he : ∀ i : σ.freeRows, (i.val, (e i).val) ∈ G)
    (c : Fin m → Fin n → ℝ) :
    ∃ τ : OTSelector.PartialMatching m n,
      IsLegal G τ ∧ τ.card = legalMaximumCard G ∧ σ.edges ⊆ τ.edges ∧
      τ.edges = σ.edges ∪ (freeEquivRepair σ e).edges ∧
      τ.cost c = σ.cost c + ∑ i : σ.freeRows, c i.val (e i).val ∧
      legalMaximumValue G c ≤ σ.cost c + ∑ i : σ.freeRows, c i.val (e i).val := by
  classical
  let ρ := freeEquivRepair σ e
  obtain ⟨_, _, hρcard, hρcost⟩ := freeEquivRepair_spec σ e c
  have hρ : IsLegal (residualAllowed G σ) ρ := by
    intro a ha
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp ha
    exact Finset.mem_filter.mpr ⟨he i, (Finset.mem_sdiff.mp i.property).2,
      (Finset.mem_sdiff.mp (e i).property).2⟩
  obtain ⟨hr, hc⟩ := residualAllowed_disjoint σ ρ hρ
  let τ := σ.union ρ hr hc
  have hτlegal : IsLegal G τ := isLegal_union_residual σ ρ hσ hρ
  have hτfull : τ.card = m := by
    dsimp only [τ]
    rw [OTSelector.PartialMatching.card_union, hρcard,
      OTSelector.PartialMatching.card_freeRows]
    have := σ.card_le.trans (min_le_left m n)
    omega
  have hfull : legalMaximumCard G = m := by
    apply le_antisymm ((legalMaximumCard_le_min G).trans (min_le_left _ _))
    exact hτfull.symm.trans_le (card_le_legalMaximumCard hτlegal)
  have hτmax : τ.card = legalMaximumCard G := hτfull.trans hfull.symm
  have hcost : τ.cost c = σ.cost c + ∑ i : σ.freeRows, c i.val (e i).val := by
    rw [OTSelector.PartialMatching.cost_union, hρcost]
  exact ⟨τ, hτlegal, hτmax, Finset.subset_union_left, rfl, hcost,
    (legalMaximumValue_le c hτlegal hτmax).trans_eq hcost⟩

end OTSelector.Reconstruction.PartialMatching
