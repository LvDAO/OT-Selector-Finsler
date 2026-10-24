import OTSelector.Reconstruction.OriginalStageResidualDensityOrientedActualPorts
import OTSelector.Reconstruction.OriginalStageResidualDensityGammaCancellation

/-! Actual full-main prefix and cut error in the same chosen physical cube. -/
open Set Function MeasureTheory Module Manifold
open scoped ENNReal ContDiff
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Geometry ContinuousFinslerNorm OTSelector.Probability

/-- The full unchanged original input prefix in a literal physical window. Source strict
and target closed prefixes agree with the true lifetime conventions. -/
def originalStageMainInputWindowPrefix {q : ℕ} (K : Set (Fin q → ℝ)) (c : ℝ)
    (scene : LegalMarkedOptimalInputScene q) : ℝ :=
  ((legalInputColorMeasure q scene.2 0).restrict {p | p.1 ∈ K}).real {p | p.2 < c} -
    ((legalInputColorMeasure q scene.2 1).restrict {p | p.1 ∈ K}).real {p | p.2 ≤ c}

/-- The literal general-window prefix recovers the already verified axis-aligned prefix. -/
theorem originalStageMainInputWindowPrefix_haarRootCube {q : ℕ} (R c : ℝ)
    (scene : LegalMarkedOptimalInputScene q) :
    originalStageMainInputWindowPrefix (haarRootCube (Fin q) R) c scene =
      originalStageMainInputPrefix R c scene := rfl

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}

/-- Actual full-main delta in the chosen physical cube: the unchanged full input prefix
minus the unchanged full cut occupation smoothed by the same physical canonical mollifier.
It depends on neither the retained cutoff nor selected reserve indices. -/
def originalOrientedStageFullCutError (S : CalibratedLevelSeedPatch F u) (w : S.covector.ker)
    (b : OrthonormalBasis (Fin (finrank ℝ S.covector.ker)) ℝ
      (EuclideanSpace ℝ (Fin (finrank ℝ S.covector.ker)))) (R c : ℝ)
    (scene : LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker)) : ℝ :=
  originalStageMainInputWindowPrefix (originalCenteredPhysicalCubeRegion b (2 * R)) c scene -
    ∫ z in originalCenteredPhysicalCubeRegion b (2 * R),
      ∫ x, originalEuclideanMollifier (finrank ℝ S.covector.ker) (x - z)
        ∂originalSceneActiveCutMeasure S w c scene

end OTSelector.Reconstruction
