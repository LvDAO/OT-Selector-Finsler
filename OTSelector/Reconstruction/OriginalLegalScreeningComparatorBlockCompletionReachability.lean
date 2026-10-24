import OTSelector.Reconstruction.MarkedStationaryValueLegalReachability
import OTSelector.Finite.RelationChain

/-! The converse finite Berge certificate, using only actual original-index chains. -/
open Set Function
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OTSelector.Reconstruction.PartialMatching
variable {m n : ℕ}

/-- An actual reachable free target gives a simple original-index augmenting chain. -/
theorem exists_legalAugmentingChain_of_reachable_free_target
    {G : Finset (Fin m × Fin n)} (σ : OTSelector.PartialMatching m n)
    {i : Fin m} (hi : alternatingReachable G σ i) {j : Fin n}
    (hj : j ∈ σ.freeCols) (hij : (i,j) ∈ G) :
    ∃ k : ℕ, Nonempty (LegalAugmentingChain G σ k) := by
  classical
  obtain ⟨i₀,hi₀,hpath⟩ := hi
  obtain ⟨k,row,hrow,hfirst,hlast,hstep⟩ := OTSelector.exists_injective_relation_chain hpath
  choose oldCol hnew hold using hstep
  let col : Fin (k+1) → Fin n := Fin.snoc oldCol j
  have hcolOld : Injective oldCol := by
    intro a b hab
    have heq := σ.col_inj _ (hold a) _ (hold b) hab
    exact Fin.succ_injective _ (hrow (congrArg Prod.fst heq))
  have hjnot : j ∉ range oldCol := by
    rintro ⟨a,ha⟩
    exact (Finset.mem_sdiff.mp hj).2
      (ha ▸ Finset.mem_image.mpr ⟨(row a.succ,oldCol a),hold a,rfl⟩)
  refine ⟨k,⟨⟨row,col,hrow,Fin.snoc_injective_iff.mpr ⟨hcolOld,hjnot⟩,?_,?_,?_,?_⟩⟩⟩
  · rw [hfirst]
    exact (Finset.mem_sdiff.mp hi₀).2
  · simpa only [col,Fin.snoc_last] using (Finset.mem_sdiff.mp hj).2
  · intro a
    simpa only [col,Fin.snoc_castSucc] using hold a
  · intro a
    refine Fin.lastCases ?_ (fun b ↦ ?_) a
    · simpa only [col,Fin.snoc_last,hlast] using hij
    · simpa only [col,Fin.snoc_castSucc] using hnew b

/-- A genuine legal maximum has no alternatingly reachable free target. -/
theorem no_reachable_free_target_of_card_eq_legalMaximum
    {G : Finset (Fin m × Fin n)} (σ : OTSelector.PartialMatching m n)
    (hσ : IsLegal G σ) (hmax : σ.card = legalMaximumCard G) :
    ∀ i, alternatingReachable G σ i → ∀ j ∈ σ.freeCols, (i,j) ∉ G := by
  intro i hi j hj hij
  obtain ⟨k,⟨P⟩⟩ := exists_legalAugmentingChain_of_reachable_free_target σ hi hj hij
  have hh := card_le_legalMaximumCard (P.flip_isLegal hσ)
  rw [P.flip_card,hmax] at hh
  omega

end OTSelector.Reconstruction.PartialMatching
