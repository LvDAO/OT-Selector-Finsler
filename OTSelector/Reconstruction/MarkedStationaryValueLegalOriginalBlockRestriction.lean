import OTSelector.Reconstruction.MarkedStationaryValueLegalInputColoredScene
import OTSelector.Probability.BlockDataTransport

/-!
# Exact restrictions of the original finite point arrays

The restriction keeps precisely the original indices whose full point belongs
to the selected set. Its canonical index embedding, point values, counting
measure, measurability, and injectivity all come from the same original array.
-/
open Set Function MeasureTheory
open scoped ENNReal NNReal BigOperators Classical
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
variable {X : Type*} [MeasurableSpace X]

/-- Restrict a finite original array at the full original point, retaining
all its coordinates and its original order. -/
def legalOriginalBlockRestriction (U : Set X) (b : BlockData X) : BlockData X :=
  blockDataOfPairsGen true (fun i : Fin b.1 ↦ (restrictionLabel U (b.2 i), b.2 i))

/-- The retained observations are indexed by these original array positions. -/
def legalOriginalBlockRestrictionIndices (U : Set X) (b : BlockData X) : Finset (Fin b.1) :=
  Finset.univ.filter fun i ↦ restrictionLabel U (b.2 i) = true

/-- Canonically embed the retained finite array in the unchanged original array. -/
def legalOriginalBlockRestrictionEmbedding (U : Set X) (b : BlockData X) :
    Fin (legalOriginalBlockRestriction U b).1 ↪ Fin b.1 where
  toFun i := ((legalOriginalBlockRestrictionIndices U b).orderIsoOfFin rfl i).1
  inj' := by
    intro i j hij
    exact ((legalOriginalBlockRestrictionIndices U b).orderIsoOfFin rfl).injective (Subtype.ext hij)

omit [MeasurableSpace X] in
/-- Every retained observation is literally its original array point. -/
theorem legalOriginalBlockRestriction_point (U : Set X) (b : BlockData X)
    (i : Fin (legalOriginalBlockRestriction U b).1) :
    (legalOriginalBlockRestriction U b).2 i = b.2 (legalOriginalBlockRestrictionEmbedding U b i) := rfl

omit [MeasurableSpace X] in
/-- The original point of each retained index belongs to the selected set. -/
theorem legalOriginalBlockRestrictionEmbedding_mem (U : Set X) (b : BlockData X)
    (i : Fin (legalOriginalBlockRestriction U b).1) :
    b.2 (legalOriginalBlockRestrictionEmbedding U b i) ∈ U := by
  have hi := ((legalOriginalBlockRestrictionIndices U b).orderIsoOfFin rfl i).2
  have hl := (Finset.mem_filter.mp hi).2
  change restrictionLabel U (b.2 (legalOriginalBlockRestrictionEmbedding U b i)) = true at hl
  simpa [restrictionLabel] using hl

omit [MeasurableSpace X] in
/-- Every selected original index occurs in the retained enumeration. -/
theorem exists_legalOriginalBlockRestrictionEmbedding_eq (U : Set X) (b : BlockData X)
    (i : Fin b.1) (hi : b.2 i ∈ U) :
    ∃ j : Fin (legalOriginalBlockRestriction U b).1,
      legalOriginalBlockRestrictionEmbedding U b j = i := by
  have his : i ∈ legalOriginalBlockRestrictionIndices U b := by
    simp [legalOriginalBlockRestrictionIndices, restrictionLabel, hi]
  refine ⟨((legalOriginalBlockRestrictionIndices U b).orderIsoOfFin rfl).symm ⟨i, his⟩, ?_⟩
  exact congrArg Subtype.val
    (((legalOriginalBlockRestrictionIndices U b).orderIsoOfFin rfl).apply_symm_apply ⟨i, his⟩)

omit [MeasurableSpace X] in
/-- Restriction preserves injectivity of the actual original point enumeration. -/
theorem legalOriginalBlockRestriction_injective (U : Set X) (b : BlockData X)
    (hb : Injective b.2) : Injective (legalOriginalBlockRestriction U b).2 := by
  intro i j hij
  apply (legalOriginalBlockRestrictionEmbedding U b).injective
  apply hb
  simpa only [legalOriginalBlockRestriction_point] using hij

omit [MeasurableSpace X] in
/-- The restriction never inserts new indices or increases the original count. -/
theorem legalOriginalBlockRestriction_card_le (U : Set X) (b : BlockData X) :
    (legalOriginalBlockRestriction U b).1 ≤ b.1 := by
  simpa only [Fintype.card_fin] using
    Fintype.card_le_of_injective _ (legalOriginalBlockRestrictionEmbedding U b).injective

/-- Restricting the actual finite array is measurable for every measurable
set of full original points, including arbitrary point-clock products. -/
theorem measurable_legalOriginalBlockRestriction {U : Set X} (hU : MeasurableSet U) :
    Measurable (legalOriginalBlockRestriction U) := by
  change Measurable (blockDataLabelCloud true ∘ mapBlockData (fun x : X ↦ (restrictionLabel U x, x)))
  exact (measurable_blockDataLabelCloud true).comp
    (measurable_mapBlockData ((measurable_restrictionLabel hU).prodMk measurable_id))

/-- The restricted array has exactly the restricted original counting measure;
original multiplicities and all original coordinates are preserved. -/
theorem legalInputBlockMeasure_legalOriginalBlockRestriction (b : BlockData X)
    {U : Set X} (hU : MeasurableSet U) :
    legalInputBlockMeasure (legalOriginalBlockRestriction U b) = (legalInputBlockMeasure b).restrict U := by
  have hidx : legalOriginalBlockRestrictionIndices U b =
      Finset.univ.filter (fun i : Fin b.1 ↦ b.2 i ∈ U) := by
    ext i
    simp [legalOriginalBlockRestrictionIndices, restrictionLabel]
  have hreindex : legalInputBlockMeasure (legalOriginalBlockRestriction U b) =
      ∑ i ∈ legalOriginalBlockRestrictionIndices U b, Measure.dirac (b.2 i) := by
    change (∑ j : Fin (legalOriginalBlockRestrictionIndices U b).card,
      Measure.dirac (b.2 ((legalOriginalBlockRestrictionIndices U b).orderIsoOfFin rfl j).1)) = _
    exact (((legalOriginalBlockRestrictionIndices U b).orderIsoOfFin rfl).toEquiv.sum_comp
      (fun i ↦ Measure.dirac (b.2 i.1))).trans
        (Finset.sum_coe_sort _ (fun i ↦ Measure.dirac (b.2 i)))
  rw [hreindex, hidx, Finset.sum_filter]
  change (∑ i : Fin b.1, if b.2 i ∈ U then Measure.dirac (b.2 i) else 0) =
    (∑ i : Fin b.1, Measure.dirac (b.2 i)).restrict U
  calc
    _ = ∑ i : Fin b.1, (Measure.dirac (b.2 i)).restrict U := by
      apply Finset.sum_congr rfl
      intro i hi
      exact (restrict_dirac' hU).symm
    _ = _ := by
      exact (map_sum (Measure.restrictₗ U) (fun i : Fin b.1 ↦ Measure.dirac (b.2 i)) Finset.univ).symm

end OTSelector.Reconstruction
