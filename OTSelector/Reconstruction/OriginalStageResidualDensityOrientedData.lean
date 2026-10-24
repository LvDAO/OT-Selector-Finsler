import OTSelector.Reconstruction.OriginalStageResidualDensityOrientedOmittedCut
import OTSelector.Reconstruction.OriginalStageResidualDensityOrientedActualPorts
import OTSelector.Reconstruction.OriginalStageResidualDensityOrientedCutError
import OTSelector.Reconstruction.OriginalStageResidualDensityReserveCounts

/-! Literal stage densities from the same original scene, frame and reserve indices. -/
open Set Function MeasureTheory Module Manifold
open scoped ENNReal ContDiff
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Geometry ContinuousFinslerNorm OTSelector.Probability
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}

/-- The original scene and observed reserve arrays/kept indices in one fixed physical frame.
No count balance, mass equality, positivity, cut identity or selected spatial law is a field. -/
structure OriginalOrientedStageResidualDensityData (S : CalibratedLevelSeedPatch F u)
    (w : S.covector.ker)
    (b : OrthonormalBasis (Fin (finrank ℝ S.covector.ker)) ℝ
      (EuclideanSpace ℝ (Fin (finrank ℝ S.covector.ker)))) (R ell : ℝ) where
  scene : LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker)
  sourceReserve : MarkedCloudSpace (finrank ℝ S.covector.ker) ℝ
  targetReserve : MarkedCloudSpace (finrank ℝ S.covector.ker) ℝ
  sourceKept : Finset (Fin sourceReserve.1)
  targetKept : Finset (Fin targetReserve.1)

namespace OriginalOrientedStageResidualDensityData
variable {S : CalibratedLevelSeedPatch F u} {w : S.covector.ker}
  {b : OrthonormalBasis (Fin (finrank ℝ S.covector.ker)) ℝ
    (EuclideanSpace ℝ (Fin (finrank ℝ S.covector.ker)))} {R ell : ℝ}
  (A : OriginalOrientedStageResidualDensityData S w b R ell)

def cubeMeasure (_A : OriginalOrientedStageResidualDensityData S w b R ell) :
    Measure (Fin (finrank ℝ S.covector.ker) → ℝ) :=
  volume.restrict (originalCenteredPhysicalCubeRegion b (2 * R))

def cubeVolume : ℝ := A.cubeMeasure.real univ

def sourcePortMeasure : Measure (LegalMarkedPhysicalPoint (finrank ℝ S.covector.ker)) :=
  (originalStageWindowSourcePortPlan (originalOrientedPathLengthRetained S w b R ell)
    (originalCenteredPhysicalCubeRegion b (2 * R)) A.scene :
      Measure (LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker))).fst

def targetPortMeasure : Measure (LegalMarkedPhysicalPoint (finrank ℝ S.covector.ker)) :=
  (originalStageWindowTargetPortPlan (originalOrientedPathLengthRetained S w b R ell)
    (originalCenteredPhysicalCubeRegion b (2 * R)) A.scene :
      Measure (LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker))).snd

def portPrefix (c : ℝ) : ℝ :=
  A.sourcePortMeasure.real {p | p.2 < c} - A.targetPortMeasure.real {p | p.2 ≤ c}

def reservePrefix (c : ℝ) : ℝ :=
  originalStageRemainingReservePrefix A.sourceReserve A.targetReserve A.sourceKept A.targetKept c

/-- The literal paper gamma for this same actual retained set and physical window. -/
def gamma (c : ℝ) : ℝ :=
  (A.portPrefix c + A.reservePrefix c -
    ∫ z, originalOrientedOmittedCutDensity S w b R ell c A.scene z ∂A.cubeMeasure) / A.cubeVolume

/-- Actual source stage density with the precise Ico source convention. -/
def sourceDensity (s t : ℝ) (z : Fin (finrank ℝ S.covector.ker) → ℝ) : ℝ :=
  originalOrientedOmittedCutDensity S w b R ell s A.scene z + A.gamma s +
    originalOrientedStageReflectedClassDensity b R (Ico s t) A.sourcePortMeasure z +
    (originalStageRemainingReserveClassCount A.sourceReserve A.sourceKept (Ico s t) : ℝ) / A.cubeVolume

/-- Actual target stage density with the precise Ioc target convention. -/
def targetDensity (s t : ℝ) (z : Fin (finrank ℝ S.covector.ker) → ℝ) : ℝ :=
  originalOrientedOmittedCutDensity S w b R ell t A.scene z + A.gamma t +
    originalOrientedStageReflectedClassDensity b R (Ioc s t) A.targetPortMeasure z +
    (originalStageRemainingReserveClassCount A.targetReserve A.targetKept (Ioc s t) : ℝ) / A.cubeVolume

end OriginalOrientedStageResidualDensityData
end OTSelector.Reconstruction
