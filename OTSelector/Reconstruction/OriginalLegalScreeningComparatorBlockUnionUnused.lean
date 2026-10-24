import OTSelector.Reconstruction.OriginalLegalScreeningComparatorBlockUnion
import OTSelector.Reconstruction.OriginalLegalScreeningComparatorSubarrayCompletion

/-! Genuine bijections of unused original block labels create the local matchings themselves. -/
open Set Function
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OTSelector.Reconstruction.PartialMatching
variable {m n : ℕ} {β : Type*} [DecidableEq β]

/-- A genuine legal bijection of unused original labels fills one block. Its actual
cardinality gives local saturation, while all core pairs and signed costs are retained. -/
theorem exists_blockMatching_of_unused_equiv
    (G : Finset (Fin m × Fin n)) (c : Fin m → β) (d : Fin n → β)
    (σ : OTSelector.PartialMatching m n) (hσ : IsLegal G σ)
    (hsame : ∀ e ∈ σ.edges, c e.1 = d e.2) (b : β)
    (S : Finset (Fin m)) (T : Finset (Fin n))
    (hS : S ⊆ σ.freeRows) (hT : T ⊆ σ.freeCols)
    (hSb : ∀ i ∈ S, c i = b) (hTb : ∀ j ∈ T, d j = b)
    (e : S ≃ T) (he : ∀ i : S, (i.val,(e i).val) ∈ G)
    (hcount : (σ.edges.filter (fun e ↦ c e.1 = b)).card + S.card =
      min (Finset.univ.filter (fun i ↦ c i = b)).card (Finset.univ.filter (fun j ↦ d j = b)).card) :
    ∃ ζ : OTSelector.PartialMatching m n,
      IsLegal G ζ ∧ (∀ p ∈ ζ.edges, c p.1 = b ∧ d p.2 = b) ∧
      (∀ p ∈ σ.edges, c p.1 = b → p ∈ ζ.edges) ∧
      ζ.card = min (Finset.univ.filter (fun i ↦ c i = b)).card
        (Finset.univ.filter (fun j ↦ d j = b)).card ∧
      ∀ cost : Fin m → Fin n → ℝ,
        ζ.cost cost = (∑ p ∈ σ.edges.filter (fun p ↦ c p.1 = b), cost p.1 p.2) +
          ∑ i : S, cost i.val (e i).val := by
  classical
  let σb := σ.subMatching (σ.edges.filter (fun p ↦ c p.1 = b)) (Finset.filter_subset _ _)
  let ρ := subarrayEquivRepair S T e
  have hρ : IsLegal (residualAllowed G σ) ρ := by
    intro p hp
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hp
    exact Finset.mem_filter.mpr ⟨he i,(Finset.mem_sdiff.mp (hS i.property)).2,
      (Finset.mem_sdiff.mp (hT (e i).property)).2⟩
  obtain ⟨hr,hc⟩ := residualAllowed_disjoint σ ρ hρ
  have hrs : σb.rows ⊆ σ.rows := by
    intro i hi
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hi
    exact Finset.mem_image.mpr ⟨p,(Finset.mem_filter.mp hp).1,rfl⟩
  have hcs : σb.cols ⊆ σ.cols := by
    intro j hj
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hj
    exact Finset.mem_image.mpr ⟨p,(Finset.mem_filter.mp hp).1,rfl⟩
  let ζ := σb.union ρ (hr.mono_left hrs) (hc.mono_left hcs)
  refine ⟨ζ,?_,?_,?_,?_,?_⟩
  · intro p hp
    rcases Finset.mem_union.mp hp with hp | hp
    · exact hσ (Finset.mem_filter.mp hp).1
    · exact residualAllowed_subset G σ (hρ hp)
  · intro p hp
    rcases Finset.mem_union.mp hp with hp | hp
    · have hh := Finset.mem_filter.mp hp
      exact ⟨hh.2,(hsame p hh.1).symm.trans hh.2⟩
    · obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hp
      exact ⟨hSb i.val i.property,hTb (e i).val (e i).property⟩
  · intro p hp hb
    exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hp,hb⟩)
  · rw [OTSelector.PartialMatching.card_union,(subarrayEquivRepair_spec S T e (fun _ _ ↦ 0)).2.2.1]
    exact hcount
  · intro cost
    rw [OTSelector.PartialMatching.cost_union,(subarrayEquivRepair_spec S T e cost).2.2.2]
    rfl

/-- The same-block core cost splits exactly over all actual original block labels. -/
theorem sum_block_core_cost [Fintype β] (c : Fin m → β)
    (σ : OTSelector.PartialMatching m n) (cost : Fin m → Fin n → ℝ) :
    (∑ b, ∑ p ∈ σ.edges.filter (fun p ↦ c p.1 = b), cost p.1 p.2) = σ.cost cost := by
  exact Finset.sum_fiberwise_of_maps_to (s := σ.edges) (t := Finset.univ)
    (g := fun p : Fin m × Fin n ↦ c p.1) (fun _ _ ↦ Finset.mem_univ _)
    (fun p ↦ cost p.1 p.2)

end OTSelector.Reconstruction.PartialMatching
