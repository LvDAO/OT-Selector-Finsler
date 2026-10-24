import OTSelector.Reconstruction.OriginalScreeningBoundaryBudgetOrientedCutLtwo
import OTSelector.Reconstruction.OriginalScreeningBoundaryBudgetQuadraticBadEvent

/-! The actual same-frame full-main cut error pays its quadratic-scale bad-event probability. -/
open Set Function Filter MeasureTheory Module Manifold
open scoped ENNReal Topology ContDiff BigOperators InnerProductSpace
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OTSelector.Reconstruction
open OTSelector.Geometry ContinuousFinslerNorm OTSelector.Probability
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M→ℝ}
  {S : CalibratedLevelSeedPatch F u} {w : S.covector.ker} {μ ν : Measure ℝ}

/-- Actual full-main delta has a negligible quadratic-scale bad event at every fixed
positive relative-volume threshold, on the same original scene law and selected frame. -/
theorem OriginalSeedConditionalMoments.tendsto_originalOrientedStageFullCutError_quadratic_bad_probability_zero
    (D : OriginalSeedConditionalMoments S w μ ν)
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    (hq : 1 < finrank ℝ S.covector.ker)
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
        (originalSeedPathClockSetCurrent S w (originalEuclideanMollifier _) (Ioc (D.lo + (S.level : ℝ)) c)) hj
        (originalEuclideanNormalReadout (b i))) = 0)
    {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun R : ℝ ↦ R^2 * (Q.law : Measure _).real
      {scene | ε*volume.real (originalCenteredPhysicalCubeRegion b (2*R)) ≤
        |originalOrientedStageFullCutError S w b R c scene|}) atTop (𝓝 0) := by
  have hl := D.originalOrientedStageFullCutError_surface_ltwo_zero hF hw hq hbounds Q b hc hj hproj
  have h := tendsto_quadratic_cut_bad_probability_zero (Q.law : Measure _)
    (lt_trans (by norm_num : 0 < 1) hq) (fun R ↦ originalOrientedStageFullCutError S w b R c)
    hl.1 hl.2 hε
  apply h.congr'
  filter_upwards [eventually_ge_atTop (1:ℝ)] with R hR
  have hvol : volume.real (originalCenteredPhysicalCubeRegion b (2*R)) =
      (2*R)^(finrank ℝ S.covector.ker) := by
    rw [measureReal_def, volume_originalOrientedTraffic_cube, ← measureReal_def,
      volume_real_haarRootCube (Fin (finrank ℝ S.covector.ker)) (show 0 ≤ R by linarith), Fintype.card_fin]
  rw [hvol]

end OTSelector.Reconstruction
