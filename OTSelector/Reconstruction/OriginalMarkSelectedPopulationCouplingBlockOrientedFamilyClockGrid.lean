import OTSelector.Reconstruction.OriginalMarkSelectedPopulationCouplingBlockOrientedFamilyProbability
import OTSelector.Reconstruction.OriginalClasswiseOriginalAtomRepairClockBlockLabels
import OTSelector.Reconstruction.OriginalClasswiseOriginalAtomRepairClockSlabBlockExtremes

/-! Actual source Ico and target Ioc clock partitions construct the global
original reserve families, with the actual opposite blocks and extreme deletions. -/
open Set Function MeasureTheory
open scoped BigOperators ENNReal NNReal Classical
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
namespace OriginalStageClockGrid
variable (G : OriginalStageClockGrid) {μ ν : Measure ℝ}

/-- Source original labels use the actual Ico blocks, opposite target Ioc
blocks, and deletion from the actual first source class in each block. -/
def sourceReserveFineBlockPartition (h₀ : G.clockSlabSurplus μ ν 0 = 0)
    (hN : G.clockSlabSurplus μ ν G.count = 0) :
    OriginalReserveFineBlockPartition (G.ClockSlabBlock μ ν) (Fin G.count) where
  blockCell := G.sourceBlockCell μ ν
  oppositeCell := G.targetBlockCell μ ν
  deletionCell := fun b ↦ G.sourceCell (G.firstBlockClass b)
  fineCell := G.sourceCell
  blockFor := G.blockForClass h₀ hN
  block_disjoint := (G.blockCells_disjoint h₀ hN).1
  fine_disjoint := G.source_disjoint
  fine_subset_block := fun i _ hx ↦ (G.mem_sourceBlockCell_iff _ hx).mpr (G.blockForClass_contains h₀ hN i)
  block_covered := by
    intro b x hx
    obtain ⟨i, hi⟩ := mem_iUnion.mp hx
    obtain ⟨_, hxi⟩ := mem_iUnion.mp hi
    exact mem_iUnion.mpr ⟨i, hxi⟩
  measurable_block := fun b ↦ (G.blockCells_measurable b).1
  measurable_opposite := fun b ↦ (G.blockCells_measurable b).2
  measurable_deletion := fun _ ↦ measurableSet_Ico
  measurable_fine := fun _ ↦ measurableSet_Ico

/-- Target labels separately use the actual Ioc blocks and opposite source
Ico blocks, deleting from the actual last target class of each block. -/
def targetReserveFineBlockPartition (h₀ : G.clockSlabSurplus μ ν 0 = 0)
    (hN : G.clockSlabSurplus μ ν G.count = 0) :
    OriginalReserveFineBlockPartition (G.ClockSlabBlock μ ν) (Fin G.count) where
  blockCell := G.targetBlockCell μ ν
  oppositeCell := G.sourceBlockCell μ ν
  deletionCell := fun b ↦ G.targetCell (G.lastBlockClass b)
  fineCell := G.targetCell
  blockFor := G.blockForClass h₀ hN
  block_disjoint := (G.blockCells_disjoint h₀ hN).2
  fine_disjoint := G.target_disjoint
  fine_subset_block := fun i _ hx ↦ (G.mem_targetBlockCell_iff _ hx).mpr (G.blockForClass_contains h₀ hN i)
  block_covered := by
    intro b x hx
    obtain ⟨i, hi⟩ := mem_iUnion.mp hx
    obtain ⟨_, hxi⟩ := mem_iUnion.mp hi
    exact mem_iUnion.mpr ⟨i, hxi⟩
  measurable_block := fun b ↦ (G.blockCells_measurable b).2
  measurable_opposite := fun b ↦ (G.blockCells_measurable b).1
  measurable_deletion := fun _ ↦ measurableSet_Ioc
  measurable_fine := fun _ ↦ measurableSet_Ioc

/-- The actual source clock grid and original Poisson sampler produce a
single family on all unchanged globally kept original source labels. -/
theorem sourceReserveGlobalAtomLaws {q : ℕ} [IsProbabilityMeasure μ]
    (h₀ : G.clockSlabSurplus μ ν 0 = 0) (hN : G.clockSlabSurplus μ ν G.count = 0)
    (P : Measure (LegalMarkedOptimalInputScene q × MarkedCloudSpace q ℝ)) [IsProbabilityMeasure P]
    (b : OrthonormalBasis (Fin q) ℝ (EuclideanSpace ℝ (Fin q))) {R ρ : ℝ}
    (hR : 0 < R) (hρ : 0 ≤ ρ) (hq : 4 < q) :
    let H := G.sourceReserveFineBlockPartition h₀ hN
    let K := originalCenteredPhysicalCubeRegion b (2*R)
    let M := P.prod (markedPoissonLaw q ℝ μ (Real.toNNReal ρ*(volume K).toNNReal))
    (∀ᵐ p ∂M, H.AtomSpec b R 0 1 p) ∧ Integrable (H.atomEnergy b R 0 1) M ∧
      (∫ p, H.atomEnergy b R 0 1 p ∂M) / volume.real K ≤
        (G.count : ℝ)*((q : ℝ)*dyadicMatchingConstant q*ρ^(1-2/(q : ℝ))) := by
  simpa only [Fintype.card_fin] using
    (G.sourceReserveFineBlockPartition h₀ hN).atomLaws_normalized P μ b hR hρ 0 1 hq

/-- The actual target construction uses target Ioc cells throughout and
the reversed opposite-block count, on the unchanged original target labels. -/
theorem targetReserveGlobalAtomLaws {q : ℕ} [IsProbabilityMeasure ν]
    (h₀ : G.clockSlabSurplus μ ν 0 = 0) (hN : G.clockSlabSurplus μ ν G.count = 0)
    (P : Measure (LegalMarkedOptimalInputScene q × MarkedCloudSpace q ℝ)) [IsProbabilityMeasure P]
    (b : OrthonormalBasis (Fin q) ℝ (EuclideanSpace ℝ (Fin q))) {R ρ : ℝ}
    (hR : 0 < R) (hρ : 0 ≤ ρ) (hq : 4 < q) :
    let H := G.targetReserveFineBlockPartition h₀ hN
    let K := originalCenteredPhysicalCubeRegion b (2*R)
    let M := P.prod (markedPoissonLaw q ℝ ν (Real.toNNReal ρ*(volume K).toNNReal))
    (∀ᵐ p ∂M, H.AtomSpec b R 1 0 p) ∧ Integrable (H.atomEnergy b R 1 0) M ∧
      (∫ p, H.atomEnergy b R 1 0 p ∂M) / volume.real K ≤
        (G.count : ℝ)*((q : ℝ)*dyadicMatchingConstant q*ρ^(1-2/(q : ℝ))) := by
  simpa only [Fintype.card_fin] using
    (G.targetReserveFineBlockPartition h₀ hN).atomLaws_normalized P ν b hR hρ 1 0 hq

end OriginalStageClockGrid
end OTSelector.Reconstruction
