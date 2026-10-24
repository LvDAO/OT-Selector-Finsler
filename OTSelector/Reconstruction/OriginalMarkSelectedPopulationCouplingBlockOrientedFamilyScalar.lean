import OTSelector.Reconstruction.OriginalMarkSelectedPopulationCouplingBlockOrientedFamilyFull
import OTSelector.Reconstruction.OriginalReserveMappedWindowSampler

/-! Scalar arrival-law form for the same physically placed original reserve labels. -/
open Set Function MeasureTheory
open scoped BigOperators ENNReal Classical
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
namespace OriginalReserveFineBlockPartition
variable {q : ℕ} {B I : Type*} [Fintype B] [Fintype I]
  (H : OriginalReserveFineBlockPartition B I)
set_option backward.isDefEq.respectTransparency false

/-- The global family's center is exactly the same original physical reserve
point placed by the actual oriented cube map. -/
theorem atomPoint_eq_originalMappedReserveCloud
    (b : OrthonormalBasis (Fin q) ℝ (EuclideanSpace ℝ (Fin q))) (R : ℝ) (own other : Fin 2)
    (p : (LegalMarkedOptimalInputScene q × MarkedCloudSpace q ℝ) × MarkedCloudSpace q ℝ)
    (a : originalReserveBlocksKeptFin (originalCenteredPhysicalCubeRegion b (2*R)) own other
      H.blockCell H.oppositeCell H.deletionCell (originalReserveExcessInputAux p)) :
    H.atomPoint b R own other p a = (EuclideanSpace.equiv (Fin q) ℝ).symm
      ((originalMappedReserveCloud q (originalOrientedRawCubePhysicalMap b R) p.2).2 a.val).1 := rfl

/-- Each literal physical original class has the scalar arrival-law form
ofReal(h_D/cubeVolume) times cubeMeasure.map toEuclidean. -/
theorem atomSpec_class_sum_smul
    (b : OrthonormalBasis (Fin q) ℝ (EuclideanSpace ℝ (Fin q))) (R : ℝ) (own other : Fin 2)
    (p : (LegalMarkedOptimalInputScene q × MarkedCloudSpace q ℝ) × MarkedCloudSpace q ℝ)
    (hp : H.AtomSpec b R own other p) (i : I) :
    let K := originalCenteredPhysicalCubeRegion b (2*R)
    let cloud := originalMappedReserveCloud q (originalOrientedRawCubePhysicalMap b R) p.2
    let U := originalReserveBlocksKeptFin K own other H.blockCell H.oppositeCell H.deletionCell
      (originalReserveExcessInputAux p)
    (∑ a : U, if (cloud.2 a.val).2 ∈ H.fineCell i then H.atomLaw b R own other p a else 0) =
      ENNReal.ofReal ((originalStageRemainingReserveClassCount cloud U (H.fineCell i) : ℝ) /
        (volume.restrict K).real univ) • (volume.restrict K).map (EuclideanSpace.equiv (Fin q) ℝ).symm := by
  simpa only [withDensity_const, Measure.map_smul, measureReal_def, Measure.restrict_apply_univ,
    originalMappedReserveCloud, originalStageRemainingReserveClassCount]
    using hp.2.2 i

end OriginalReserveFineBlockPartition
end OTSelector.Reconstruction
