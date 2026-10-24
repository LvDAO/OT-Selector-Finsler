import OTSelector.Reconstruction.MarkedStationaryValueLegalClockPrefixCompletion

/-!
# Actual reserve clock counts guarantee a legal completion

A selected boundary core may depend on the entire original cloud. The unused
non-reserve sources are charged explicitly. At each actual free source clock,
the original reserve target tail then dominates the original reserve source
tail and those ports. Scalar Hall completion preserves every core edge.
-/
open Set Function
open scoped BigOperators Classical
noncomputable section
namespace OTSelector.Reconstruction.PartialMatching
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000

/-- Actual unused reserve-tail slack absorbs all non-reserve source ports.
No distribution or independence is assigned to the selected port set. -/
theorem free_clock_prefix_counts_of_reserve_slack
    {m n : ℕ} (source : Fin m → ℝ) (target : Fin n → ℝ)
    (σ : OTSelector.PartialMatching m n)
    (RS : Finset (Fin m)) (_hRS : RS ⊆ σ.freeRows)
    (RT : Finset (Fin n)) (hRT : RT ⊆ σ.freeCols)
    (hslack : ∀ i ∈ σ.freeRows,
      (σ.freeRows \ RS).card + (RS.filter (fun i' ↦ source i ≤ source i')).card ≤
        (RT.filter (fun j ↦ source i < target j)).card) :
    ∀ i ∈ σ.freeRows,
      (σ.freeRows.filter (fun i' ↦ source i ≤ source i')).card ≤
        (σ.freeCols.filter (fun j ↦ source i < target j)).card := by
  intro i hi
  have hsub : σ.freeRows.filter (fun i' ↦ source i ≤ source i') ⊆
      (σ.freeRows \ RS) ∪ RS.filter (fun i' ↦ source i ≤ source i') := by
    intro i' hi'
    obtain ⟨hf, hp⟩ := Finset.mem_filter.mp hi'
    by_cases hr : i' ∈ RS
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hr, hp⟩)
    · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hf, hr⟩)
  have htar : RT.filter (fun j ↦ source i < target j) ⊆
      σ.freeCols.filter (fun j ↦ source i < target j) :=
    Finset.filter_subset_filter _ hRT
  calc
    _ ≤ ((σ.freeRows \ RS) ∪ RS.filter (fun i' ↦ source i ≤ source i')).card :=
      Finset.card_le_card hsub
    _ ≤ (σ.freeRows \ RS).card + (RS.filter (fun i' ↦ source i ≤ source i')).card :=
      Finset.card_union_le _ _
    _ ≤ (RT.filter (fun j ↦ source i < target j)).card := hslack i hi
    _ ≤ _ := Finset.card_le_card htar

/-- Prefix slack of the actual unused reserves constructs a strict-clock
completion retaining every selected original core edge. -/
theorem exists_legal_clock_completion_of_reserve_slack
    {m n : ℕ} (source : Fin m → ℝ) (target : Fin n → ℝ)
    (σ : OTSelector.PartialMatching m n)
    (hσ : IsLegal (scalarClockLegalGraph source target) σ)
    (RS : Finset (Fin m)) (hRS : RS ⊆ σ.freeRows)
    (RT : Finset (Fin n)) (hRT : RT ⊆ σ.freeCols)
    (hslack : ∀ i ∈ σ.freeRows,
      (σ.freeRows \ RS).card + (RS.filter (fun i' ↦ source i ≤ source i')).card ≤
        (RT.filter (fun j ↦ source i < target j)).card) :
    ∃ τ : OTSelector.PartialMatching m n,
      IsLegal (scalarClockLegalGraph source target) τ ∧ τ.card = m ∧ σ.edges ⊆ τ.edges := by
  exact exists_legal_clock_completion_of_free_prefix_counts source target σ hσ
    (free_clock_prefix_counts_of_reserve_slack source target σ RS hRS RT hRT hslack)

end OTSelector.Reconstruction.PartialMatching
