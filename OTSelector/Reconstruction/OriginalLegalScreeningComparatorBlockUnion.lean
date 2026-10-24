import OTSelector.Finite.MatchingBlockUnionCore
import OTSelector.Reconstruction.OriginalLegalScreeningComparatorBlockCompletion

/-! Finite local block repairs assemble into the true global legal maximum. -/
open Set Function
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OTSelector.Reconstruction.PartialMatching
variable {m n : ℕ} {β : Type*} [Fintype β] [LinearOrder β]

/-- Actual local block matchings of minimum-colour cardinality are unioned on their
unchanged original indices. Local saturation and the true global maximum are proved
internally. The extra matching is strictly forward, retains every original core pair,
and pays at most one common edge bound per actual block-count discrepancy. This is a
finite assembly lemma; the local matchings remain explicit inputs. -/
theorem exists_legalMaximum_of_ordered_block_matchings
    (G : Finset (Fin m × Fin n)) (c : Fin m → β) (d : Fin n → β)
    (σ : OTSelector.PartialMatching m n)
    (ζ : β → OTSelector.PartialMatching m n)
    (hlabels : ∀ b e, e ∈ (ζ b).edges → c e.1 = b ∧ d e.2 = b)
    (hlegal : ∀ b, IsLegal G (ζ b))
    (hkeep : ∀ e ∈ σ.edges, e ∈ (ζ (c e.1)).edges)
    (hcard : ∀ b, (ζ b).card = min (Finset.univ.filter (fun i ↦ c i = b)).card
      (Finset.univ.filter (fun j ↦ d j = b)).card)
    (hforward : ∀ i j, (i,j) ∈ G → c i ≤ d j)
    (hcomplete : ∀ i j, c i < d j → (i,j) ∈ G) :
    ∃ extra κ : OTSelector.PartialMatching m n,
      IsLegal G κ ∧ κ.card = legalMaximumCard G ∧ σ.edges ⊆ κ.edges ∧
      κ.edges = (orderedBlockMatchingUnion c d ζ hlabels).edges ∪ extra.edges ∧
      IsLegal (residualAllowed G (orderedBlockMatchingUnion c d ζ hlabels)) extra ∧
      (∀ e ∈ extra.edges, c e.1 < d e.2) ∧
      extra.card ≤ ∑ b, Nat.dist (Finset.univ.filter (fun i ↦ c i = b)).card
        (Finset.univ.filter (fun j ↦ d j = b)).card ∧
      ∀ cost : Fin m → Fin n → ℝ,
        κ.cost cost = (∑ b, (ζ b).cost cost) + extra.cost cost ∧
        ∀ C : ℝ, 0 ≤ C → (∀ e ∈ extra.edges, cost e.1 e.2 ≤ C) →
        κ.cost cost ≤ (∑ b, (ζ b).cost cost) + C *
          ((∑ b, Nat.dist (Finset.univ.filter (fun i ↦ c i = b)).card
            (Finset.univ.filter (fun j ↦ d j = b)).card : ℕ) : ℝ) := by
  classical
  let U := orderedBlockMatchingUnion c d ζ hlabels
  have hU := orderedBlockMatchingUnion_spec c d ζ hlabels
  have hUlegal : IsLegal G U := by
    intro e he
    obtain ⟨b,_,hb⟩ := Finset.mem_biUnion.mp he
    exact hlegal b hb
  have hkeepU : σ.edges ⊆ U.edges := by
    intro e he
    exact edges_subset_orderedBlockMatchingUnion c d ζ hlabels (c e.1) (hkeep e he)
  obtain ⟨extra,κ,hextra,hstrict,_,_,hκ,hmax,hunion,hUkeep,_,_,hcount,hcost⟩ :=
    exists_legalMaximum_completion_of_ordered_saturated_blocks G c d U hUlegal hU.2.2
      hforward hcomplete (orderedBlockMatchingUnion_saturates c d ζ hlabels hcard)
  refine ⟨extra,κ,hκ,hmax,hkeepU.trans hUkeep,hunion,hextra,hstrict,hcount,?_⟩
  intro cost
  have heq : κ.cost cost = (∑ b, (ζ b).cost cost) + extra.cost cost := by
    rw [hcost cost,hU.2.1 cost]
  refine ⟨heq,?_⟩
  intro C hC hbound
  have hb : extra.cost cost ≤ (extra.card : ℝ)*C := by
    change (∑ e ∈ extra.edges, cost e.1 e.2) ≤ _
    calc
      _ ≤ ∑ _e ∈ extra.edges, C := Finset.sum_le_sum hbound
      _ = _ := by simp [OTSelector.PartialMatching.card]
  have hc := mul_le_mul_of_nonneg_left (Nat.cast_le (α := ℝ).mpr hcount) hC
  rw [heq]
  nlinarith only [hb,hc]

end OTSelector.Reconstruction.PartialMatching
