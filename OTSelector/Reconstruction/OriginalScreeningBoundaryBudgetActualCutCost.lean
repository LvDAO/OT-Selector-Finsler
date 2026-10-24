import OTSelector.Reconstruction.OriginalScreeningBoundaryBudgetActualCountLimit
import OTSelector.Reconstruction.OriginalScreeningBoundaryBudgetOrientedCutProbability

/-! Actual full-main cut errors pay actual same-scene input-count exceptional costs. -/
open Set Function Filter MeasureTheory Module Manifold
open scoped ENNReal Topology ContDiff BigOperators InnerProductSpace
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OTSelector.Reconstruction
open OTSelector.Geometry ContinuousFinslerNorm OTSelector.Probability
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}

/-- The canonical measurable envelope of the genuine same-frame full-main cut error.
It is taken in the unchanged actual scene law, before weighting its actual input count. -/
def originalScreeningActualCutBadEnvelope (S : CalibratedLevelSeedPatch F u)
    (w : S.covector.ker)
    (P : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker)))
    (b : OrthonormalBasis (Fin (finrank ℝ S.covector.ker)) ℝ
      (EuclideanSpace ℝ (Fin (finrank ℝ S.covector.ker)))) (R c ε : ℝ) :
    Set (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker)) :=
  toMeasurable P {scene | ε * volume.real (originalCenteredPhysicalCubeRegion b (2 * R)) ≤
    |originalOrientedStageFullCutError S w b R c scene|}

omit [BorelSpace E] in
/-- The literal full-main cut bad event is contained in this measurable envelope of
exactly the same original probability; no measurable-event input is needed. -/
theorem originalScreeningActualCutBadEnvelope_spec (S : CalibratedLevelSeedPatch F u)
    (w : S.covector.ker)
    (P : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker)))
    (b : OrthonormalBasis (Fin (finrank ℝ S.covector.ker)) ℝ
      (EuclideanSpace ℝ (Fin (finrank ℝ S.covector.ker)))) (R c ε : ℝ) :
    MeasurableSet (originalScreeningActualCutBadEnvelope S w P b R c ε) ∧
    {scene | ε * volume.real (originalCenteredPhysicalCubeRegion b (2 * R)) ≤
      |originalOrientedStageFullCutError S w b R c scene|} ⊆
      originalScreeningActualCutBadEnvelope S w P b R c ε ∧
    P.real (originalScreeningActualCutBadEnvelope S w P b R c ε) =
      P.real {scene | ε * volume.real (originalCenteredPhysicalCubeRegion b (2 * R)) ≤
        |originalOrientedStageFullCutError S w b R c scene|} := by
  refine ⟨measurableSet_toMeasurable _ _, subset_toMeasurable _ _, ?_⟩
  simp only [originalScreeningActualCutBadEnvelope, measureReal_def, measure_toMeasurable]

variable {S : CalibratedLevelSeedPatch F u} {w : S.covector.ker} {μ ν : Measure ℝ}

/-- Actual surface-scale full-cut control and actual original full-input Poisson counts
give a negligible quadratically weighted exceptional cost in this same physical cube.
Neither a cut-probability rate nor an independent selected count law is an input. -/
theorem OriginalSeedConditionalMoments.tendsto_originalScreeningActualCutBadEnvelope_count_cost_zero
    (D : OriginalSeedConditionalMoments S w μ ν)
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    (hq : 4 < finrank ℝ S.covector.ker)
    {gap diameter : ℝ} (hbounds : ConditionalClockSupportBounds μ ν gap diameter)
    {g : ℝ → ℝ → ℝ}
    (Q : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν
      (D.originalFocalKinetic gap) g)
    (b : OrthonormalBasis (Fin (finrank ℝ S.covector.ker)) ℝ
      (EuclideanSpace ℝ (Fin (finrank ℝ S.covector.ker))))
    {c : ℝ} (hc : D.lo + (S.level : ℝ) ≤ c)
    (hj : ∀ k, MemLp (fun scene ↦ originalSeedPathClockSetCurrent S w
      (originalEuclideanMollifier _) (Ioc (D.lo + (S.level : ℝ)) c) scene k) 2
        (Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))))
    (hproj : ∀ i, (translationFixedSubspace Q.sceneEuclideanKoopman (ℝ ∙ b i)ᗮ).starProjection
      (originalLinearCurrentReadoutLtwo (Q.law : Measure _)
        (originalSeedPathClockSetCurrent S w (originalEuclideanMollifier _)
          (Ioc (D.lo + (S.level : ℝ)) c)) hj
        (originalEuclideanNormalReadout (b i))) = 0)
    {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun R : ℝ ↦ R^2 *
      ((∫ scene, (originalScreeningActualCutBadEnvelope S w (Q.law : Measure _) b R c ε).indicator
          (originalScreeningPhysicalCubeActualCount b R) scene
          ∂(Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker)))) /
        volume.real (originalCenteredPhysicalCubeRegion b (2 * R)))) atTop (𝓝 0) := by
  have hrate := D.tendsto_originalOrientedStageFullCutError_quadratic_bad_probability_zero
    hF hw (by omega) hbounds Q b hc hj hproj hε
  apply Q.tendsto_originalScreeningPhysicalCubeActualCount_bad_cost_zero hq b
    (fun R ↦ originalScreeningActualCutBadEnvelope S w (Q.law : Measure _) b R c ε)
    (fun R ↦ (originalScreeningActualCutBadEnvelope_spec S w (Q.law : Measure _) b R c ε).1)
  have heq : (fun R : ℝ ↦ R^2 * (Q.law : Measure _).real
      (originalScreeningActualCutBadEnvelope S w (Q.law : Measure _) b R c ε)) =
      fun R : ℝ ↦ R^2 * (Q.law : Measure _).real
        {scene | ε * volume.real (originalCenteredPhysicalCubeRegion b (2 * R)) ≤
          |originalOrientedStageFullCutError S w b R c scene|} :=
    funext (fun R ↦ congrArg (fun x : ℝ ↦ R^2 * x)
      (originalScreeningActualCutBadEnvelope_spec S w (Q.law : Measure _) b R c ε).2.2)
  rw [heq]
  exact hrate

end OTSelector.Reconstruction
