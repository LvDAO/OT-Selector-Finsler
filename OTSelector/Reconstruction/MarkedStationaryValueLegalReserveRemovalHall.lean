import OTSelector.Reconstruction.MarkedStationaryValueLegalClockPrefixCompletion
import Mathlib.Tactic.Linarith

/-!
# Original reserve clock capacity survives controlled adaptive removals

Only the original index sets and their actual cardinalities are used.  Neither
unmatched source indices nor surviving reserve indices receive a probability law.
-/
open Set Function
open scoped BigOperators Classical
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false

/-- A selected set's filtered count is bounded by the original comparison set
and the actual indices outside that set. -/
theorem card_filter_le_filter_add_sdiff {I : Type*} [DecidableEq I]
    (s t : Finset I) (p : I → Prop) [DecidablePred p] :
    (s.filter p).card ≤ (t.filter p).card + (s \ t).card := by
  have hsub : s.filter p ⊆ (t.filter p) ∪ (s \ t) := by
    intro i hi
    obtain ⟨his, hip⟩ := Finset.mem_filter.mp hi
    by_cases hit : i ∈ t
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hit, hip⟩)
    · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨his, hit⟩)
  exact (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)

namespace PartialMatching
variable {m n : ℕ}

/-- Actual original reserve suffix counts pay for every non-reserve unmatched
source and every consumed original target reserve, even after adaptive choices. -/
theorem free_clock_prefix_counts_of_adaptive_reserve_slack
    (source : Fin m → ℝ) (target : Fin n → ℝ)
    (σ : OTSelector.PartialMatching m n) (RS : Finset (Fin m)) (RT : Finset (Fin n))
    (K : Set ℝ) (hK : ∀ i ∈ σ.freeRows, source i ∈ K) (H : ℝ)
    (hslack : ∀ c ∈ K, H ≤
      ((RT.filter (fun j ↦ c < target j)).card : ℝ) -
        ((RS.filter (fun i ↦ c ≤ source i)).card : ℝ))
    (hbudget : ((σ.freeRows \ RS).card : ℝ) + ((RT \ σ.freeCols).card : ℝ) ≤ H) :
    ∀ i ∈ σ.freeRows,
      (σ.freeRows.filter (fun i' ↦ source i ≤ source i')).card ≤
        (σ.freeCols.filter (fun j ↦ source i < target j)).card := by
  intro i hi
  have hs := card_filter_le_filter_add_sdiff σ.freeRows RS
    (fun i' ↦ source i ≤ source i')
  have ht := card_filter_le_filter_add_sdiff RT σ.freeCols
    (fun j ↦ source i < target j)
  have hsR := Nat.cast_le (α := ℝ).mpr hs
  have htR := Nat.cast_le (α := ℝ).mpr ht
  simp only [Nat.cast_add] at hsR htR
  have hc := hslack (source i) (hK i hi)
  apply Nat.cast_le (α := ℝ).mp
  linarith

/-- Controlled original reserve consumption constructs a legal extension of the
same original core matching; every original source is matched. -/
theorem exists_legal_clock_completion_of_adaptive_reserve_slack
    (source : Fin m → ℝ) (target : Fin n → ℝ)
    (σ : OTSelector.PartialMatching m n)
    (hσ : IsLegal (scalarClockLegalGraph source target) σ)
    (RS : Finset (Fin m)) (RT : Finset (Fin n))
    (K : Set ℝ) (hK : ∀ i ∈ σ.freeRows, source i ∈ K) (H : ℝ)
    (hslack : ∀ c ∈ K, H ≤
      ((RT.filter (fun j ↦ c < target j)).card : ℝ) -
        ((RS.filter (fun i ↦ c ≤ source i)).card : ℝ))
    (hbudget : ((σ.freeRows \ RS).card : ℝ) + ((RT \ σ.freeCols).card : ℝ) ≤ H) :
    ∃ τ : OTSelector.PartialMatching m n,
      IsLegal (scalarClockLegalGraph source target) τ ∧ τ.card = m ∧ σ.edges ⊆ τ.edges :=
  exists_legal_clock_completion_of_free_prefix_counts source target σ hσ
    (free_clock_prefix_counts_of_adaptive_reserve_slack source target σ RS RT K hK H hslack hbudget)

/-- The same actual reserve budget supplies the exact legal residual capacity
required by the original finite legal objective. -/
theorem legal_capacity_of_reserve_slack
    (source : Fin m → ℝ) (target : Fin n → ℝ)
    (σ : OTSelector.PartialMatching m n)
    (hσ : IsLegal (scalarClockLegalGraph source target) σ)
    (RS : Finset (Fin m)) (RT : Finset (Fin n))
    (K : Set ℝ) (hK : ∀ i ∈ σ.freeRows, source i ∈ K) (H : ℝ)
    (hslack : ∀ c ∈ K, H ≤
      ((RT.filter (fun j ↦ c < target j)).card : ℝ) -
        ((RS.filter (fun i ↦ c ≤ source i)).card : ℝ))
    (hbudget : ((σ.freeRows \ RS).card : ℝ) + ((RT \ σ.freeCols).card : ℝ) ≤ H) :
    legalMaximumCard (scalarClockLegalGraph source target) = m ∧
      σ.card + legalMaximumCard (residualAllowed (scalarClockLegalGraph source target) σ) = m :=
  legal_capacity_of_free_clock_prefix_counts source target σ hσ
    (free_clock_prefix_counts_of_adaptive_reserve_slack source target σ RS RT K hK H hslack hbudget)

end PartialMatching
end OTSelector.Reconstruction
