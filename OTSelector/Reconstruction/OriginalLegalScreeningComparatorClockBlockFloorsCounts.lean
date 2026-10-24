import OTSelector.Reconstruction.OriginalLegalScreeningComparatorClockBlockEndpointsGlobalKept

/-! Literal reserve prefix counts lose at most the actual blockwise deletions. -/
open Set Function MeasureTheory
open scoped ENNReal BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OTSelector.Reconstruction
open OTSelector.Probability
variable {q : ℕ} {B : Type*} [Fintype B]

/-- The observed Nat clock-class count is the same count on the original finite labels. -/
theorem originalReserveBlockCount_eq_remaining_univ
    (z : MarkedCloudSpace q ℝ) (C : Set ℝ) :
    originalReserveBlockCount z.1 (fun i ↦ (z.2 i).2) C =
      originalStageRemainingReserveClassCount z Finset.univ C := by
  rw [originalReserveBlockCount,originalReserveClassNatIndices_eq_map_fin,Finset.card_map]
  rfl

/-- The real sorted deletion never exceeds the requested original excess. -/
theorem card_originalReserveDeletedNatIndices_le (n : ℕ) (marks : ℕ → ℝ)
    (C : Set ℝ) (k : ℕ) : (originalReserveDeletedNatIndices n marks C k).card ≤ k := by
  unfold originalReserveDeletedNatIndices
  exact (List.toFinset_card_le _).trans (by simp only [List.length_take]; exact Nat.min_le_left _ _)

/-- A literal kept class count is exactly its Nat-index readout under the genuine union. -/
theorem originalReserveBlocksKeptFin_class_count_eq_nat
    (K : Set (Fin q → ℝ)) (own other : Fin 2) (S T C : B → Set ℝ)
    (scene : LegalMarkedOptimalInputScene q) (source target : MarkedCloudSpace q ℝ) (U : Set ℝ) :
    originalStageRemainingReserveClassCount source
      (originalReserveBlocksKeptFin K own other S T C
        ((scene,target),source.1,fun i ↦ (source.2 i).2)) U =
      ((originalReserveBlocksKept K own other S T C
        ((scene,target),source.1,fun i ↦ (source.2 i).2)).filter (fun i ↦ (source.2 i).2 ∈ U)).card := by
  rw [originalReserveBlocksKept_eq_map_fin,Finset.filter_map,Finset.card_map]
  rfl

/-- Every raw prefix index inside the actual block cover survives or is one of
its genuine sorted excess deletions. Hence its count loss is at most their sum. -/
theorem originalReserveBlocksKeptFin_raw_class_count_le
    (K : Set (Fin q → ℝ)) (own other : Fin 2) (S T C : B → Set ℝ)
    (scene : LegalMarkedOptimalInputScene q) (source target : MarkedCloudSpace q ℝ)
    (U : Set ℝ) (hU : U ⊆ ⋃ b, S b) :
    originalReserveBlockCount source.1 (fun i ↦ (source.2 i).2) U ≤
      originalStageRemainingReserveClassCount source
        (originalReserveBlocksKeptFin K own other S T C
          ((scene,target),source.1,fun i ↦ (source.2 i).2)) U +
      ∑ b, originalReserveBlockExcess K own other (S b) (T b)
        ((scene,target),source.1,fun i ↦ (source.2 i).2) := by
  let z : OriginalReserveSceneAux q := ((scene,target),source.1,fun i ↦ (source.2 i).2)
  let kept := (originalReserveBlocksKept K own other S T C z).filter (fun i ↦ (source.2 i).2 ∈ U)
  let deleted := Finset.univ.biUnion (fun b ↦ originalReserveDeletedNatIndices source.1
    (fun i ↦ (source.2 i).2) (C b) (originalReserveBlockExcess K own other (S b) (T b) z))
  have hsub : originalReserveClassNatIndices source.1 (fun i ↦ (source.2 i).2) U ⊆ kept ∪ deleted := by
    intro i hi
    obtain ⟨hin,hiU⟩ := Finset.mem_filter.mp hi
    by_cases hk : i ∈ originalReserveBlocksKept K own other S T C z
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hk,hiU⟩)
    · obtain ⟨b,hb⟩ := mem_iUnion.mp (hU hiU)
      have hd : i ∈ originalReserveDeletedNatIndices source.1 (fun i ↦ (source.2 i).2)
          (C b) (originalReserveBlockExcess K own other (S b) (T b) z) := by
        by_contra hn
        exact hk (Finset.mem_biUnion.mpr ⟨b,Finset.mem_univ _,Finset.mem_sdiff.mpr
          ⟨Finset.mem_filter.mpr ⟨hin,hb⟩,hn⟩⟩)
      exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨b,Finset.mem_univ _,hd⟩)
  have hd : deleted.card ≤ ∑ b, originalReserveBlockExcess K own other (S b) (T b) z := by
    exact Finset.card_biUnion_le.trans (Finset.sum_le_sum (fun b _ ↦
      card_originalReserveDeletedNatIndices_le _ _ _ _))
  rw [originalReserveBlocksKeptFin_class_count_eq_nat]
  exact (Finset.card_le_card hsub).trans ((Finset.card_union_le kept deleted).trans (Nat.add_le_add_left hd _))

/-- Keeping original indices can only decrease the raw class count. -/
theorem originalRemainingReserveClassCount_le_raw
    (z : MarkedCloudSpace q ℝ) (kept : Finset (Fin z.1)) (U : Set ℝ) :
    originalStageRemainingReserveClassCount z kept U ≤ originalReserveBlockCount z.1 (fun i ↦ (z.2 i).2) U := by
  rw [originalReserveBlockCount_eq_remaining_univ]
  exact Finset.card_le_card (Finset.filter_subset_filter _ (Finset.subset_univ _))

end OTSelector.Reconstruction
