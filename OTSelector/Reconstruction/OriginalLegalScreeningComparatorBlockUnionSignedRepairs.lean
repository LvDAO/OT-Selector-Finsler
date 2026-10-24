import OTSelector.Reconstruction.OriginalLegalScreeningComparatorBlockUnionUnused

/-! Assemble real original-label local repairs while retaining the exact signed core cost. -/
open Set Function
open scoped BigOperators Classical
noncomputable section
namespace OTSelector.Reconstruction.PartialMatching
variable {m n : ℕ} {β E : Type*} [Fintype β] [LinearOrder β] [PseudoMetricSpace E]

/-- Original-label block repairs are assembled into the unchanged graph's
true legal maximum. The local unused arrays and their signed core remain the
same, and only repaired pairs and the actual cross-block excess pay new costs. -/
theorem exists_legalMaximum_of_ordered_unused_block_signed_repairs
    (G : Finset (Fin m × Fin n)) (blockS : Fin m → β) (blockT : Fin n → β)
    (σ : OTSelector.PartialMatching m n) (hσ : IsLegal G σ)
    (hsame : ∀ e ∈ σ.edges, blockS e.1 = blockT e.2)
    (hforward : ∀ i j, (i,j) ∈ G → blockS i ≤ blockT j)
    (hcomplete : ∀ i j, blockS i < blockT j → (i,j) ∈ G)
    (S : β → Finset (Fin m)) (T : β → Finset (Fin n))
    (hS : ∀ b, S b ⊆ σ.freeRows) (hT : ∀ b, T b ⊆ σ.freeCols)
    (hSb : ∀ b i, i ∈ S b → blockS i = b)
    (hTb : ∀ b j, j ∈ T b → blockT j = b)
    (hcount : ∀ b, (σ.edges.filter (fun e ↦ blockS e.1 = b)).card + (S b).card =
      min (Finset.univ.filter (fun i ↦ blockS i = b)).card
        (Finset.univ.filter (fun j ↦ blockT j = b)).card)
    (x : Fin m → E) (y : Fin n → E) (budget : β → ℝ)
    (hrepair : ∀ b, ∃ e : S b ≃ T b,
      (∀ i, (i.val,(e i).val) ∈ G) ∧
      (∑ i : S b, dist (x i.val) (y (e i).val)^2) ≤ budget b)
    (cost : Fin m → Fin n → ℝ) (K L C : ℝ) (hK : 0 ≤ K) (hC : 0 ≤ C)
    (hnewCost : ∀ b (i : S b) (j : T b), cost i.val j.val ≤ K*dist (x i.val) (y j.val)^2+L)
    (hcrossCost : ∀ i j, blockS i < blockT j → cost i j ≤ C) :
    ∃ extra γ : OTSelector.PartialMatching m n,
      IsLegal G γ ∧ γ.card = legalMaximumCard G ∧ σ.edges ⊆ γ.edges ∧
      extra.edges ⊆ γ.edges ∧
      (∀ e ∈ extra.edges, blockS e.1 < blockT e.2) ∧
      extra.card ≤ ∑ b, Nat.dist (Finset.univ.filter (fun i ↦ blockS i = b)).card
        (Finset.univ.filter (fun j ↦ blockT j = b)).card ∧
      γ.cost cost ≤ σ.cost cost + (∑ b, (K*budget b + L*((S b).card : ℝ))) +
        C*((∑ b, Nat.dist (Finset.univ.filter (fun i ↦ blockS i = b)).card
          (Finset.univ.filter (fun j ↦ blockT j = b)).card : ℕ) : ℝ) := by
  have hlocal (b : β) : ∃ ζ : OTSelector.PartialMatching m n,
      IsLegal G ζ ∧ (∀ e ∈ ζ.edges, blockS e.1 = b ∧ blockT e.2 = b) ∧
      (∀ e ∈ σ.edges, blockS e.1 = b → e ∈ ζ.edges) ∧
      ζ.card = min (Finset.univ.filter (fun i ↦ blockS i = b)).card
        (Finset.univ.filter (fun j ↦ blockT j = b)).card ∧
      ζ.cost cost ≤ (∑ e ∈ σ.edges.filter (fun e ↦ blockS e.1 = b), cost e.1 e.2) +
        (K*budget b+L*((S b).card : ℝ)) := by
    obtain ⟨e,he,henergy⟩ := hrepair b
    obtain ⟨ζ,hlegal,hlabels,hkeep,hcard,hcost⟩ := exists_blockMatching_of_unused_equiv
      G blockS blockT σ hσ hsame b (S b) (T b) (hS b) (hT b) (hSb b) (hTb b) e he (hcount b)
    refine ⟨ζ,hlegal,hlabels,hkeep,hcard,?_⟩
    rw [hcost cost]
    apply add_le_add le_rfl
    calc
      (∑ i : S b, cost i.val (e i).val) ≤
          ∑ i : S b, (K*dist (x i.val) (y (e i).val)^2+L) :=
        Finset.sum_le_sum (fun i _ ↦ hnewCost b i (e i))
      _ = K*(∑ i : S b, dist (x i.val) (y (e i).val)^2)+L*((S b).card : ℝ) := by
        simp [Finset.sum_add_distrib,Finset.mul_sum,mul_comm]
      _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left henergy hK) le_rfl
  choose ζ hlegal hlabels hkeep hcard hcost using hlocal
  obtain ⟨extra,γ,hγ,hmax,hkeepCore,hunion,_,hstrict,hdiscrep,henergy⟩ :=
    exists_legalMaximum_of_ordered_block_matchings G blockS blockT σ ζ hlabels hlegal
      (fun e he ↦ hkeep (blockS e.1) e he rfl) hcard hforward hcomplete
  refine ⟨extra,γ,hγ,hmax,hkeepCore,(by rw [hunion]; exact Finset.subset_union_right),
    hstrict,hdiscrep,?_⟩
  have ht := (henergy cost).2 C hC (fun e he ↦ hcrossCost _ _ (hstrict e he))
  have hsum : (∑ b, (ζ b).cost cost) ≤ σ.cost cost + ∑ b, (K*budget b+L*((S b).card : ℝ)) := by
    calc
      _ ≤ ∑ b, ((∑ e ∈ σ.edges.filter (fun e ↦ blockS e.1 = b),cost e.1 e.2)+
          (K*budget b+L*((S b).card : ℝ))) := Finset.sum_le_sum (fun b _ ↦ hcost b)
      _ = _ := by rw [Finset.sum_add_distrib,sum_block_core_cost]
  exact ht.trans (add_le_add hsum le_rfl)

end OTSelector.Reconstruction.PartialMatching
