import OTSelector.Reconstruction.MarkedStationaryValueLegalNestedBlocks
import OTSelector.Reconstruction.MarkedStationaryValueLegalTypes

/-!
# Finite spatial source defects from actual common types

An existing same-type matching is split by its actual original spatial labels.
Every resulting matching is legal in its literal child graph. This bounds the
sum of true child legal source deficiencies by the original joint histograms.
-/

open Set Function
open scoped BigOperators Classical
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false

namespace PartialMatching

theorem card_le_sum_spatial_legal_ranks {m n : ℕ} {β : Type*} [Fintype β]
    [DecidableEq β] (allowed : Finset (Fin m × Fin n))
    (s : Fin m → β) (t : Fin n → β) (σ : OTSelector.PartialMatching m n)
    (hlegal : IsLegal allowed σ)
    (hcell : ∀ e ∈ σ.edges, s e.1 = t e.2) :
    σ.card ≤ ∑ b, legalMaximumCard (spatialLegalBlock allowed s t b) := by
  let piece (b : β) := σ.subMatching (σ.edges.filter fun e ↦ s e.1 = b)
    (Finset.filter_subset _ _)
  have hpiece (b : β) : IsLegal (spatialLegalBlock allowed s t b) (piece b) := by
    intro e he
    obtain ⟨hσ, hs⟩ := Finset.mem_filter.mp he
    exact Finset.mem_filter.mpr ⟨hlegal hσ, hs, (hcell e hσ).symm.trans hs⟩
  calc
    σ.card = ∑ b, (piece b).card :=
      Finset.card_eq_sum_card_fiberwise (fun _ _ ↦ Finset.mem_univ _)
    _ ≤ _ := Finset.sum_le_sum (fun b _ ↦ card_le_legalMaximumCard (hpiece b))

end PartialMatching

/-- Actual child legal deficiencies are bounded by the common joint type
histogram and the original two-color source imbalance. -/
theorem sum_spatialLegalSourceDefects_le_joint_type_discrepancy
    {m n : ℕ} {β T : Type*} [Fintype β] [DecidableEq β] [Fintype T] [DecidableEq T]
    (allowed : Finset (Fin m × Fin n)) (s : Fin m → β) (t : Fin n → β)
    (typeS : Fin m → T) (typeT : Fin n → T)
    (htype : ∀ i j, typeS i = typeT j → (i, j) ∈ allowed ∧ s i = t j) :
    (∑ b, (((OTSelector.blockFinset s b).card - PartialMatching.legalMaximumCard
      (PartialMatching.spatialLegalBlock allowed s t b) : ℕ) : ℝ)) ≤
      (1 / 2 : ℝ) * (∑ a, |(blockSizeS typeS a : ℝ) - (blockSizeT typeT a : ℝ)|) +
        ((m : ℝ) - ((min m n : ℕ) : ℝ)) := by
  let R : ℕ := ∑ b, PartialMatching.legalMaximumCard
    (PartialMatching.spatialLegalBlock allowed s t b)
  let J : ℕ := ∑ a, min (blockSizeS typeS a) (blockSizeT typeT a)
  have hJ : J ≤ R := by
    have h := PartialMatching.card_le_sum_spatial_legal_ranks allowed s t
      (blockPartialMatching typeS typeT (fun _ _ ↦ 0))
      (blockPartialMatching_isLegal typeS typeT _ allowed (fun i j h ↦ (htype i j h).1))
      (by
        intro e he
        obtain ⟨a, -, ha⟩ := Finset.mem_biUnion.mp he
        have hs := OTSelector.mem_blockFinset.mp (fst_mem_blockEdgesAmbient typeS typeT _ ha)
        have ht := OTSelector.mem_blockFinset.mp (snd_mem_blockEdgesAmbient typeS typeT _ ha)
        exact (htype e.1 e.2 (hs.trans ht.symm)).2)
    simpa only [card_blockPartialMatching, R, J] using h
  have hR : R ≤ min m n := (PartialMatching.sum_spatialLegalBlock_card_le allowed s t).trans
    (PartialMatching.legalMaximumCard_le_min allowed)
  have hres : min m n - R ≤ min (m - J) (n - J) := by omega
  have hh := two_mul_min_residual_le_sum_abs (blockSizeS typeS) (blockSizeT typeT)
  rw [show (∑ a, blockSizeS typeS a) = m from sum_card_blockFinset typeS,
    show (∑ a, blockSizeT typeT a) = n from sum_card_blockFinset typeT] at hh
  have htwo : (2 : ℝ) * ((min m n - R : ℕ) : ℝ) ≤
      ∑ a, |(blockSizeS typeS a : ℝ) - (blockSizeT typeT a : ℝ)| :=
    (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr hres) (by norm_num)).trans hh
  have hsum : (∑ b, ((OTSelector.blockFinset s b).card - PartialMatching.legalMaximumCard
      (PartialMatching.spatialLegalBlock allowed s t b))) + R = m := by
    dsimp only [R]
    rw [← Finset.sum_add_distrib]
    calc
      _ = ∑ b, (OTSelector.blockFinset s b).card := by
        apply Finset.sum_congr rfl
        intro b _
        exact Nat.sub_add_cancel (PartialMatching.spatialLegalBlock_source_card_le allowed s t b)
      _ = m := sum_card_blockFinset s
  have hsumR : (∑ b, (((OTSelector.blockFinset s b).card - PartialMatching.legalMaximumCard
      (PartialMatching.spatialLegalBlock allowed s t b) : ℕ) : ℝ)) + (R : ℝ) = (m : ℝ) := by
    exact_mod_cast hsum
  rw [Nat.cast_sub hR] at htwo
  linarith

end OTSelector.Reconstruction
