import OTSelector.Reconstruction.OriginalMarkSelectedPopulationCouplingBlockKeptBalance
import OTSelector.Reconstruction.OriginalLegalScreeningComparatorOrientedOriginalCore

/-! Real blockwise kept unions delete exactly the requested original mark-index excesses. -/
open Set Function MeasureTheory
open scoped ENNReal BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OTSelector.Reconstruction
open OTSelector.Probability
variable {q : ℕ} {B : Type*} [Fintype B]

/-- Actual sorted capacities make the complement of the genuine global kept set
remove exactly this block's original requested excess, on unchanged Fin sampler indices. -/
theorem originalReserveBlocksDeletedFin_block_card
    (K : Set (Fin q → ℝ)) (own other : Fin 2) (S T C : B → Set ℝ)
    (hdis : Pairwise (Disjoint on S)) (z : OriginalReserveSceneAux q) (b : B)
    (hCS : C b ⊆ S b)
    (hcap : originalReserveBlockExcess K own other (S b) (T b) z ≤
      originalReserveBlockCount z.2.1 z.2.2 (C b)) :
    ((Finset.univ \ originalReserveBlocksKeptFin K own other S T C z).filter
      (fun i : Fin z.2.1 ↦ z.2.2 i ∈ S b)).card = originalReserveBlockExcess K own other (S b) (T b) z := by
  classical
  let kept := originalReserveBlocksKeptFin K own other S T C z
  let p := fun i : Fin z.2.1 ↦ z.2.2 i ∈ S b
  have he : (Finset.univ \ kept).filter p = (Finset.univ.filter p) \ (kept.filter p) := by
    ext i
    simp only [Finset.mem_filter,Finset.mem_sdiff,Finset.mem_univ,true_and]
    tauto
  have hsub : kept.filter p ⊆ Finset.univ.filter p :=
    Finset.filter_subset_filter _ (Finset.subset_univ _)
  have hraw : (Finset.univ.filter p).card = originalReserveBlockCount z.2.1 z.2.2 (S b) := by
    rw [originalReserveBlockCount,originalReserveClassNatIndices_eq_map_fin,Finset.card_map]
  have hkept := originalReserveBlocksKeptFin_block_count K own other S T C hdis z (fun _ ↦ 0) b
  change (kept.filter p).card = _ at hkept
  rw [originalReserveBlockKept_card K own other hCS z hcap] at hkept
  have hsmall : originalReserveBlockCount z.2.1 z.2.2 (C b) ≤ originalReserveBlockCount z.2.1 z.2.2 (S b) := by
    apply Finset.card_le_card
    intro i hi
    obtain ⟨hin,hi⟩ := Finset.mem_filter.mp hi
    exact Finset.mem_filter.mpr ⟨hin,hCS hi⟩
  have hle := hcap.trans hsmall
  change ((Finset.univ \ kept).filter p).card = _
  rw [he,Finset.card_sdiff_of_subset hsub,hraw,hkept]
  omega

section OriginalEmbedding
variable {X : Type*} [MeasurableSpace X] [MeasurableSingletonClass X] {m k : ℕ}

/-- A literal original reserve embedding occupies unit reserve atoms in the same
FULL indices. This shared finite fact preserves the existing retained core. -/
theorem originalReserveEmbedding_deleted_subset_atomIndices
    (x : Fin m → X) (v : Fin k → X) (r : Fin k ↪ Fin m)
    (hx : Injective x) (hr : ∀ j, x (r j) = v j) (D : Finset (Fin k)) :
    D.map r ⊆ originalReserveAtomIndices (∑ j, Measure.dirac (v j)) x := by
  classical
  have hv : Injective v := by
    intro i j hij
    apply r.injective
    apply hx
    rw [hr,hr]
    exact hij
  have hunit (j : Fin k) : (∑ i, Measure.dirac (v i)) {x (r j)} = 1 := by
    rw [hr]
    simp [Measure.finsetSum_apply,Measure.dirac_apply',Pi.single_apply,hv.eq_iff]
  intro i hi
  obtain ⟨j,_,rfl⟩ := Finset.mem_map.mp hi
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hunit j⟩
end OriginalEmbedding

end OTSelector.Reconstruction
