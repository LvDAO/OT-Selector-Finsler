import OTSelector.Probability.StationaryScalarFaceAverage
import OTSelector.Reconstruction.OriginalCurrentFaceMeanErgodic

/-! Literal scalar face cells of the same original stationary matching scene. -/
open Set Function Filter MeasureTheory
open scoped ENNReal BigOperators InnerProductSpace Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000
namespace OTSelector.Reconstruction
open OTSelector.Probability
local instance originalScalarFaceColorMetric : MetricSpace (Fin 2) :=
  TopologicalSpace.metrizableSpaceMetric (Fin 2)

variable {q : ℕ} {α β : Measure ℝ}
  {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
  (Q : LegalWeightedStationaryPoissonMatching q α β kin g)
  {ι : Type*} [Fintype ι] (L : (ι → ℝ) →ₗ[ℝ] EuclideanSpace ℝ (Fin q))

private def originalFaceCoordinateMap : (ι → ℝ) →ₗ[ℝ] (Fin q → ℝ) :=
  (EuclideanSpace.equiv (Fin q) ℝ).toLinearMap.comp L

private theorem continuous_originalFaceCoordinateKoopman
    (x : Lp ℝ 2 (Q.law : Measure (LegalMarkedOptimalInputScene q))) :
    Continuous (fun y : ι → ℝ ↦ stationaryKoopman (Q.law : Measure _)
      (legalMarkedInputSceneReroot q) Q.stationary (legalMarkedInputSceneReroot_zero q)
      (legalMarkedInputSceneReroot_add q) (originalFaceCoordinateMap L y) x) := by
  change Continuous (fun y : ι → ℝ ↦ Q.sceneEuclideanKoopman (L y) x)
  exact (Q.continuous_sceneEuclideanKoopman x).comp L.continuous_of_finiteDimensional

omit [Fintype ι] in
private theorem originalFaceCoordinate_fixed_eq :
    translationFixedSubspace
      (stationaryKoopman (Q.law : Measure _) (legalMarkedInputSceneReroot q) Q.stationary
        (legalMarkedInputSceneReroot_zero q) (legalMarkedInputSceneReroot_add q))
      (originalFaceCoordinateMap L).range =
      translationFixedSubspace Q.sceneEuclideanKoopman L.range := by
  rw [← translationFixedSubspace_comp_linearMap, ← translationFixedSubspace_comp_linearMap]
  rfl

/-- The scalar observable is evaluated on the same literal complete original
scene under its actual physical reroot and the specified Euclidean face coordinates. -/
def LegalWeightedStationaryPoissonMatching.sceneScalarFaceReadout
    (offset : ℝ → EuclideanSpace ℝ (Fin q))
    (x : Lp ℝ 2 (Q.law : Measure (LegalMarkedOptimalInputScene q)))
    (R : ℝ) (y : ι → ℝ) (s : LegalMarkedOptimalInputScene q) : ℝ :=
  stationaryScalarFaceReadout (Q.law : Measure (LegalMarkedOptimalInputScene q))
    (legalMarkedInputSceneReroot q) (originalFaceCoordinateMap L)
    (fun r ↦ EuclideanSpace.equiv (Fin q) ℝ (offset r)) x R y s

/-- The actual original random face field is jointly measurable. -/
theorem LegalWeightedStationaryPoissonMatching.measurable_sceneScalarFaceReadout
    (offset : ℝ → EuclideanSpace ℝ (Fin q))
    (x : Lp ℝ 2 (Q.law : Measure (LegalMarkedOptimalInputScene q))) (R : ℝ) :
    Measurable (Function.uncurry (Q.sceneScalarFaceReadout L offset x R)) :=
  measurable_stationaryScalarFaceReadout (Q.law : Measure _) (legalMarkedInputSceneReroot q)
    (originalFaceCoordinateMap L) (measurable_legalMarkedInputSceneReroot_joint q)
    (fun r ↦ EuclideanSpace.equiv (Fin q) ℝ (offset r)) x R

/-- Every actual finite face cell supplies the original product-space L2 moment. -/
theorem LegalWeightedStationaryPoissonMatching.integrable_sq_sceneScalarFaceReadout_prod
    (offset : ℝ → EuclideanSpace ℝ (Fin q))
    (x : Lp ℝ 2 (Q.law : Measure (LegalMarkedOptimalInputScene q))) (R : ℝ)
    {A : Set (ι → ℝ)} (hAfinite : volume A ≠ ∞) :
    Integrable (fun p : (ι → ℝ) × LegalMarkedOptimalInputScene q ↦
      (Q.sceneScalarFaceReadout L offset x R p.1 p.2)^2)
      ((volume.restrict A).prod (Q.law : Measure _)) :=
  integrable_sq_stationaryScalarFaceReadout_prod (Q.law : Measure _) (legalMarkedInputSceneReroot q)
    Q.stationary (legalMarkedInputSceneReroot_zero q) (legalMarkedInputSceneReroot_add q)
    (originalFaceCoordinateMap L) (measurable_legalMarkedInputSceneReroot_joint q)
    (fun r ↦ EuclideanSpace.equiv (Fin q) ℝ (offset r)) x R hAfinite

/-- Every literal actual scene cell average has an integrable square. -/
theorem LegalWeightedStationaryPoissonMatching.integrable_sq_sceneScalarFaceCell_average
    (offset : ℝ → EuclideanSpace ℝ (Fin q))
    (x : Lp ℝ 2 (Q.law : Measure (LegalMarkedOptimalInputScene q))) (R : ℝ)
    {A : Set (ι → ℝ)} (hAfinite : volume A ≠ ∞) :
    Integrable (fun s ↦ (∫ y in A, Q.sceneScalarFaceReadout L offset x R y s)^2)
      (Q.law : Measure _) :=
  integrable_sq_stationaryScalarFaceCell_average (Q.law : Measure _) (legalMarkedInputSceneReroot q)
    Q.stationary (legalMarkedInputSceneReroot_zero q) (legalMarkedInputSceneReroot_add q)
    (originalFaceCoordinateMap L) (measurable_legalMarkedInputSceneReroot_joint q)
    (fun r ↦ EuclideanSpace.equiv (Fin q) ℝ (offset r)) x R hAfinite

/-- Exact expected original face energy, with literal spatial volume. -/
theorem LegalWeightedStationaryPoissonMatching.integral_sceneScalarFaceReadout_sq_average
    (offset : ℝ → EuclideanSpace ℝ (Fin q))
    (x : Lp ℝ 2 (Q.law : Measure (LegalMarkedOptimalInputScene q))) (R : ℝ)
    {A : Set (ι → ℝ)} (hAfinite : volume A ≠ ∞) :
    (∫ s, (∫ y in A, (Q.sceneScalarFaceReadout L offset x R y s)^2) ∂(Q.law : Measure _)) =
      volume.real A * ‖x‖^2 :=
  integral_stationaryScalarFaceReadout_sq_average (Q.law : Measure _) (legalMarkedInputSceneReroot q)
    Q.stationary (legalMarkedInputSceneReroot_zero q) (legalMarkedInputSceneReroot_add q)
    (originalFaceCoordinateMap L) (measurable_legalMarkedInputSceneReroot_joint q)
    (fun r ↦ EuclideanSpace.equiv (Fin q) ℝ (offset r)) x R hAfinite

/-- Actual original scene cell second moments vanish in each genuine chosen
face direction; no scalar convergence or boundary-rate premise is introduced. -/
theorem LegalWeightedStationaryPoissonMatching.tendsto_integral_sq_sceneScalarFaceCell_average_zero
    (offset : ℝ → EuclideanSpace ℝ (Fin q))
    {x : Lp ℝ 2 (Q.law : Measure (LegalMarkedOptimalInputScene q))}
    (hx : (translationFixedSubspace Q.sceneEuclideanKoopman L.range).starProjection x = 0)
    {A : Set (ι → ℝ)} (hA : MeasurableSet A) (hAfinite : volume A ≠ ∞) :
    Tendsto (fun R : ℝ ↦ ∫ s,
      (∫ y in A, Q.sceneScalarFaceReadout L offset x R y s)^2 ∂(Q.law : Measure _))
      atTop (𝓝 0) := by
  apply tendsto_integral_sq_stationaryScalarFaceCell_average_zero (Q.law : Measure _)
    (legalMarkedInputSceneReroot q) Q.stationary (legalMarkedInputSceneReroot_zero q)
    (legalMarkedInputSceneReroot_add q) (originalFaceCoordinateMap L)
    (continuous_originalFaceCoordinateKoopman Q L) (measurable_legalMarkedInputSceneReroot_joint q)
    (fun r ↦ EuclideanSpace.equiv (Fin q) ℝ (offset r)) ?_ hA hAfinite
  simpa only [originalFaceCoordinate_fixed_eq] using hx

end OTSelector.Reconstruction
