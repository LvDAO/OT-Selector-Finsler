import OTSelector.Reconstruction.MarkedStationaryValueLegalBlock
import OTSelector.Finite.BlockMatchingComparison

/-! Actual spatial block graphs and the source deficiencies which pay for
their legal multiscale augmentation. No sample balancing is imposed. -/

open Set Function
open scoped BigOperators
noncomputable section
namespace OTSelector.Reconstruction.PartialMatching
set_option backward.isDefEq.respectTransparency false

variable {m n : ℕ} {β J : Type*} [Fintype β] [DecidableEq β] [Fintype J]

def spatialLegalBlock (allowed : Finset (Fin m × Fin n))
    (sourceCell : Fin m → β) (targetCell : Fin n → β) (b : β) :
    Finset (Fin m × Fin n) := by
  classical
  exact allowed.filter fun e ↦ sourceCell e.1 = b ∧ targetCell e.2 = b

theorem spatialLegalBlock_source_card_le
    (allowed : Finset (Fin m × Fin n))
    (sourceCell : Fin m → β) (targetCell : Fin n → β) (b : β) :
    legalMaximumCard (spatialLegalBlock allowed sourceCell targetCell b) ≤
      (OTSelector.blockFinset sourceCell b).card := by
  classical
  obtain ⟨σ, hσlegal, hσcard⟩ :=
    exists_legalMaximumCard (spatialLegalBlock allowed sourceCell targetCell b)
  rw [← hσcard, ← σ.card_rows]
  apply Finset.card_le_card
  intro i hi
  obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hi
  exact OTSelector.mem_blockFinset.mpr ((Finset.mem_filter.mp (hσlegal he)).2.1)

theorem spatialLegalBlock_deficit_le_sum_source_deficits
    (allowed : Finset (Fin m × Fin n))
    (sourceCell : Fin m → β) (targetCell : Fin n → β) :
    legalMaximumCard allowed - ∑ b, legalMaximumCard
        (spatialLegalBlock allowed sourceCell targetCell b) ≤
      ∑ b, ((OTSelector.blockFinset sourceCell b).card - legalMaximumCard
        (spatialLegalBlock allowed sourceCell targetCell b)) := by
  classical
  have hsum : (∑ b, ((OTSelector.blockFinset sourceCell b).card - legalMaximumCard
      (spatialLegalBlock allowed sourceCell targetCell b))) +
      (∑ b, legalMaximumCard (spatialLegalBlock allowed sourceCell targetCell b)) = m := by
    rw [← Finset.sum_add_distrib]
    calc
      _ = ∑ b, (OTSelector.blockFinset sourceCell b).card := by
        apply Finset.sum_congr rfl
        intro b _
        exact Nat.sub_add_cancel (spatialLegalBlock_source_card_le allowed sourceCell targetCell b)
      _ = m := OTSelector.sum_card_blockFinset sourceCell
  have hglobal := (legalMaximumCard_le_min allowed).trans (min_le_left m n)
  omega

/-- The actual spatial-block value comparison is paid by original source
counts minus actual child legal cardinalities. The fixed class factor has no
sample-size dependence. -/
theorem legalMaximumValue_le_spatial_blocks_add_source_deficits
    (allowed : Finset (Fin m × Fin n))
    (sourceCell : Fin m → β) (targetCell : Fin n → β)
    (sourceClass : Fin m → J) (sourceAllows : J → Fin n → Prop)
    (hallowed : ∀ i j, (i, j) ∈ allowed ↔ sourceAllows (sourceClass i) j)
    (c : Fin m → Fin n → ℝ) {B : ℝ} (hB0 : 0 ≤ B) (hB : ∀ i j, |c i j| ≤ B) :
    legalMaximumValue allowed c ≤
      (∑ b, legalMaximumValue (spatialLegalBlock allowed sourceCell targetCell b) c) +
        (∑ b, (((OTSelector.blockFinset sourceCell b).card - legalMaximumCard
          (spatialLegalBlock allowed sourceCell targetCell b) : ℕ) : ℝ)) *
            (2 * (Fintype.card J : ℝ) * B) := by
  classical
  let block := spatialLegalBlock allowed sourceCell targetCell
  have hsub (b) : block b ⊆ allowed := Finset.filter_subset _ _
  have hr : Pairwise (fun b b' ↦ Disjoint ((block b).image Prod.fst)
      ((block b').image Prod.fst)) := by
    intro b b' hbb'
    apply Finset.disjoint_left.mpr
    intro i hi hi'
    obtain ⟨e, he, heq⟩ := Finset.mem_image.mp hi
    obtain ⟨f, hf, hfq⟩ := Finset.mem_image.mp hi'
    have hs := (Finset.mem_filter.mp he).2.1
    have ht := (Finset.mem_filter.mp hf).2.1
    exact hbb' (hs.symm.trans ((congrArg sourceCell (heq.trans hfq.symm)).trans ht))
  have hc : Pairwise (fun b b' ↦ Disjoint ((block b).image Prod.snd)
      ((block b').image Prod.snd)) := by
    intro b b' hbb'
    apply Finset.disjoint_left.mpr
    intro j hj hj'
    obtain ⟨e, he, heq⟩ := Finset.mem_image.mp hj
    obtain ⟨f, hf, hfq⟩ := Finset.mem_image.mp hj'
    have hs := (Finset.mem_filter.mp he).2.2
    have ht := (Finset.mem_filter.mp hf).2.2
    exact hbb' (hs.symm.trans ((congrArg targetCell (heq.trans hfq.symm)).trans ht))
  have hv := legalMaximumValue_le_sum_blocks_add_class_deficit allowed block hsub hr hc
    sourceClass sourceAllows hallowed c hB0 hB
  have hd := spatialLegalBlock_deficit_le_sum_source_deficits allowed sourceCell targetCell
  apply hv.trans
  apply add_le_add le_rfl
  calc
    _ ≤ ((legalMaximumCard allowed - ∑ b, legalMaximumCard (block b) : ℕ) : ℝ) *
        (2 * (Fintype.card J : ℝ) * B) := by
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      nlinarith
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      simpa only [Nat.cast_sum] using (Nat.cast_le (α := ℝ)).mpr hd

end OTSelector.Reconstruction.PartialMatching
