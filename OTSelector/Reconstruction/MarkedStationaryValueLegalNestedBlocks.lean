import OTSelector.Reconstruction.MarkedStationaryValueLegalSpatialDefect

/-! Legal spatial block cardinalities, with original point indices retained. -/

open Set Function
open scoped BigOperators
noncomputable section
namespace OTSelector.Reconstruction.PartialMatching
set_option backward.isDefEq.respectTransparency false

variable {m n : ℕ} {β γ J : Type*} [Fintype β] [DecidableEq β]
  [Fintype γ] [DecidableEq γ] [Fintype J]

@[simp]
theorem legalMaximumValue_empty (c : Fin m → Fin n → ℝ) :
    legalMaximumValue (∅ : Finset (Fin m × Fin n)) c = 0 := by
  obtain ⟨σ, hσ, _, hcost⟩ := exists_cost_eq_legalMaximumValue ∅ c
  have he : σ.edges = ∅ := Finset.subset_empty.mp hσ
  rw [← hcost, OTSelector.PartialMatching.cost, he, Finset.sum_empty]

omit [DecidableEq β] in
theorem sum_legalMaximumCard_le_of_disjoint_blocks
    (allowed : Finset (Fin m × Fin n)) (block : β → Finset (Fin m × Fin n))
    (hsub : ∀ b, block b ⊆ allowed)
    (hrows : Pairwise (fun b b' ↦ Disjoint ((block b).image Prod.fst)
      ((block b').image Prod.fst)))
    (hcols : Pairwise (fun b b' ↦ Disjoint ((block b).image Prod.snd)
      ((block b').image Prod.snd))) :
    ∑ b, legalMaximumCard (block b) ≤ legalMaximumCard allowed := by
  classical
  choose σ hlegal hcard using fun b ↦ exists_legalMaximumCard (block b)
  have hs (b) : (σ b).rows ⊆ (block b).image Prod.fst := by
    rintro i hi
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hi
    exact Finset.mem_image.mpr ⟨e, hlegal b he, rfl⟩
  have ht (b) : (σ b).cols ⊆ (block b).image Prod.snd := by
    rintro j hj
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hj
    exact Finset.mem_image.mpr ⟨e, hlegal b he, rfl⟩
  let core := OTSelector.PartialMatching.disjointFamily σ
    (fun b b' hbb' ↦ (hrows hbb').mono (hs b) (hs b'))
    (fun b b' hbb' ↦ (hcols hbb').mono (ht b) (ht b'))
  have hc : IsLegal allowed core := by
    intro e he
    obtain ⟨b, _, heb⟩ := Finset.mem_biUnion.mp he
    exact hsub b (hlegal b heb)
  simpa only [core, OTSelector.PartialMatching.disjointFamily_card, hcard] using
    card_le_legalMaximumCard hc

omit [Fintype β] in
theorem spatialLegalBlock_pairwise_rows
    (allowed : Finset (Fin m × Fin n)) (s : Fin m → β) (t : Fin n → β) :
    Pairwise (fun b b' ↦ Disjoint
      ((spatialLegalBlock allowed s t b).image Prod.fst)
      ((spatialLegalBlock allowed s t b').image Prod.fst)) := by
  classical
  intro b b' hbb'
  apply Finset.disjoint_left.mpr
  intro i hi hi'
  obtain ⟨e, he, heq⟩ := Finset.mem_image.mp hi
  obtain ⟨f, hf, hfq⟩ := Finset.mem_image.mp hi'
  exact hbb' ((Finset.mem_filter.mp he).2.1.symm.trans
    ((congrArg s (heq.trans hfq.symm)).trans (Finset.mem_filter.mp hf).2.1))

omit [Fintype β] in
theorem spatialLegalBlock_pairwise_cols
    (allowed : Finset (Fin m × Fin n)) (s : Fin m → β) (t : Fin n → β) :
    Pairwise (fun b b' ↦ Disjoint
      ((spatialLegalBlock allowed s t b).image Prod.snd)
      ((spatialLegalBlock allowed s t b').image Prod.snd)) := by
  classical
  intro b b' hbb'
  apply Finset.disjoint_left.mpr
  intro j hj hj'
  obtain ⟨e, he, heq⟩ := Finset.mem_image.mp hj
  obtain ⟨f, hf, hfq⟩ := Finset.mem_image.mp hj'
  exact hbb' ((Finset.mem_filter.mp he).2.2.symm.trans
    ((congrArg t (heq.trans hfq.symm)).trans (Finset.mem_filter.mp hf).2.2))

theorem sum_spatialLegalBlock_card_le
    (allowed : Finset (Fin m × Fin n)) (s : Fin m → β) (t : Fin n → β) :
    ∑ b, legalMaximumCard (spatialLegalBlock allowed s t b) ≤
      legalMaximumCard allowed :=
  sum_legalMaximumCard_le_of_disjoint_blocks allowed _
    (fun _ ↦ Finset.filter_subset _ _)
    (spatialLegalBlock_pairwise_rows allowed s t)
    (spatialLegalBlock_pairwise_cols allowed s t)

omit [Fintype β] [Fintype γ] in
/-- A child graph is an actual subgraph of its parent; other child labels
give the empty graph. This uses only the finite spatial refinement map. -/
theorem spatialLegalBlock_refine
    (allowed : Finset (Fin m × Fin n)) (s : Fin m → β) (t : Fin n → β)
    (parent : β → γ) (p : γ) (b : β) :
    spatialLegalBlock (spatialLegalBlock allowed (parent ∘ s) (parent ∘ t) p)
      s t b = if parent b = p then spatialLegalBlock allowed s t b else ∅ := by
  classical
  by_cases hb : parent b = p
  · simp only [hb, ite_true]
    ext e
    simp only [spatialLegalBlock, Finset.mem_filter, Function.comp_apply]
    constructor
    · rintro ⟨⟨he, _⟩, hs, ht⟩
      exact ⟨he, hs, ht⟩
    · rintro ⟨he, hs, ht⟩
      exact ⟨⟨he, by simpa [hs, ht] using And.intro hb hb⟩, hs, ht⟩
  · simp only [hb, ite_false]
    apply Finset.eq_empty_of_forall_notMem
    intro e he
    obtain ⟨he', hs', _⟩ := Finset.mem_filter.mp he
    have hs := (Finset.mem_filter.mp he').2.1
    exact hb (hs' ▸ hs)

omit [Fintype γ] in
/-- Disjoint actual child matchings cannot exceed the parent legal rank. -/
theorem sum_child_legalMaximumCard_le_parent
    (allowed : Finset (Fin m × Fin n)) (s : Fin m → β) (t : Fin n → β)
    (parent : β → γ) (p : γ) :
    (∑ b, if parent b = p then legalMaximumCard (spatialLegalBlock allowed s t b) else 0) ≤
      legalMaximumCard (spatialLegalBlock allowed (parent ∘ s) (parent ∘ t) p) := by
  have h := sum_spatialLegalBlock_card_le
    (spatialLegalBlock allowed (parent ∘ s) (parent ∘ t) p) s t
  simpa only [spatialLegalBlock_refine, apply_ite legalMaximumCard,
    legalMaximumCard_empty] using h

/-- Summed parent deficits are bounded by the source deficiencies of the
actual children. This is the count identity needed at every repair scale. -/
theorem sum_parent_legal_deficit_le_source_deficits
    (allowed : Finset (Fin m × Fin n)) (s : Fin m → β) (t : Fin n → β)
    (parent : β → γ) :
    (∑ p, (legalMaximumCard (spatialLegalBlock allowed (parent ∘ s) (parent ∘ t) p) -
      ∑ b, if parent b = p then legalMaximumCard (spatialLegalBlock allowed s t b) else 0)) ≤
    ∑ b, ((OTSelector.blockFinset s b).card -
      legalMaximumCard (spatialLegalBlock allowed s t b)) := by
  classical
  have hid : (∑ p, (legalMaximumCard (spatialLegalBlock allowed (parent ∘ s) (parent ∘ t) p) -
      ∑ b, if parent b = p then legalMaximumCard (spatialLegalBlock allowed s t b) else 0)) +
      ∑ b, legalMaximumCard (spatialLegalBlock allowed s t b) =
      ∑ p, legalMaximumCard (spatialLegalBlock allowed (parent ∘ s) (parent ∘ t) p) := by
    have hf : (∑ p, ∑ b, if parent b = p then
        legalMaximumCard (spatialLegalBlock allowed s t b) else 0) =
        ∑ b, legalMaximumCard (spatialLegalBlock allowed s t b) := by
      rw [Finset.sum_comm]
      simp
    rw [← hf, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun p _ ↦
      Nat.sub_add_cancel (sum_child_legalMaximumCard_le_parent allowed s t parent p)
  have hparent : (∑ p, legalMaximumCard
      (spatialLegalBlock allowed (parent ∘ s) (parent ∘ t) p)) ≤ m :=
    (sum_spatialLegalBlock_card_le allowed (parent ∘ s) (parent ∘ t)).trans
      ((legalMaximumCard_le_min allowed).trans (min_le_left m n))
  have hsource : (∑ b, ((OTSelector.blockFinset s b).card -
      legalMaximumCard (spatialLegalBlock allowed s t b))) +
      ∑ b, legalMaximumCard (spatialLegalBlock allowed s t b) = m := by
    rw [← Finset.sum_add_distrib]
    calc
      _ = ∑ b, (OTSelector.blockFinset s b).card :=
        Finset.sum_congr rfl fun b _ ↦
          Nat.sub_add_cancel (spatialLegalBlock_source_card_le allowed s t b)
      _ = m := OTSelector.sum_card_blockFinset s
  omega

end OTSelector.Reconstruction.PartialMatching
