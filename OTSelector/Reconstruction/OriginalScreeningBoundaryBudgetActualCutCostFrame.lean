import OTSelector.Reconstruction.OriginalScreeningBoundaryBudgetActualCutCost
import OTSelector.Reconstruction.OriginalScreeningBoundaryBudgetActualCutFrame

/-! One actual original frame supplies face control and count-weighted cut exceptional costs. -/
open Set Function Filter MeasureTheory Module Manifold TopologicalSpace
open scoped ENNReal Topology ContDiff BigOperators InnerProductSpace Distributions
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
namespace OTSelector.Reconstruction
open OTSelector.Geometry ContinuousFinslerNorm OTSelector.Probability
local instance originalScreeningActualCutCostFaceColorMetric : MetricSpace (Fin 2) :=
  TopologicalSpace.metrizableSpaceMetric (Fin 2)
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {S : CalibratedLevelSeedPatch F u} {w : S.covector.ker} {μ ν : Measure ℝ}

/-- Original minimization produces one common physical frame for every countable stage
clock family and actual full-main cut family. The same frame supplies all true normal
projections, subextensive face means, and negligible actual input-count weighted cut
exceptional costs. Current L2, projections and probability rates are all internal outputs. -/
theorem OriginalSeedConditionalMoments.exists_actualCanonical_screening_frame_cut_costs
    (D : OriginalSeedConditionalMoments S w μ ν)
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    (hq : 4 < finrank ℝ S.covector.ker)
    {densityμ densityν : M → ℝ} {v : M → E → ℝ} (cμ cν : ℝ≥0∞)
    (hρμ : Continuous densityμ) (hρμ0 : ∀ x, 0 ≤ densityμ x)
    (hρν : Continuous densityν) (hρν0 : ∀ x, 0 ≤ densityν x)
    (hv : ∀ old, ContinuousOn (v old) (extChartAt 𝓘(ℝ, E) old).target)
    (hv0 : ∀ old, ∀ y ∈ (extChartAt 𝓘(ℝ, E) old).target, 0 ≤ v old y)
    (hdensityμ : PopulationSeedClockDensity S w
      (μ.map (fun x : ℝ ↦ x - S.level)) densityμ v cμ.toReal)
    (hdensityν : PopulationSeedClockDensity S w
      (ν.map (fun x : ℝ ↦ x - S.level)) densityν v cν.toReal)
    {gap diameter : ℝ} (hbounds : ConditionalClockSupportBounds μ ν gap diameter)
    (hgap : 0 < gap) {g : ℝ → ℝ → ℝ} {gBound : ℝ}
    (hg : Measurable (Function.uncurry g)) (hgb : ∀ x y, |g x y| ≤ gBound) (τ : ℝ)
    (Q : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν
      (D.originalFocalKinetic gap) g)
    (hmin : ∀ P : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν
      (D.originalFocalKinetic gap) g, Q.value τ ≤ P.value τ)
    {I J : Type*} [Countable I] [Countable J]
    (A : I → Set ℝ) (cuts : J → ℝ) (hcuts : ∀ a, D.lo + (S.level : ℝ) ≤ cuts a) :
    let q := finrank ℝ S.covector.ker
    let η := originalEuclideanMollifier q
    let clocks : I ⊕ J → Set ℝ := Sum.elim A (fun a ↦ Ioc (D.lo + (S.level : ℝ)) (cuts a))
    ∃ hL2 : ∀ a k, MemLp (fun scene ↦ originalSeedPathClockSetCurrent S w η (clocks a) scene k) 2
        (Q.law : Measure (LegalMarkedOptimalInputScene q)),
      ∃ b : OrthonormalBasis (Fin q) ℝ (EuclideanSpace ℝ (Fin q)),
        (∀ i a C, (translationFixedSubspace Q.sceneEuclideanKoopman (ℝ ∙ b i)ᗮ).starProjection
          (originalLinearCurrentReadoutLtwo (Q.law : Measure _)
            (originalSeedPathClockSetCurrent S w η (clocks a)) (hL2 a) C) = 0) ∧
        (∀ a, Tendsto (fun L : ℝ ↦
          (∫ scene, originalScreeningPhysicalFaceBudget Q b
            (originalSeedPathClockSetCurrent S w η (clocks a)) (hL2 a) L scene ∂(Q.law : Measure _)) / L^q)
            atTop (𝓝 0)) ∧
        ∀ (a : J) (ε : ℝ), 0 < ε →
          (∀ R : ℝ,
            MeasurableSet (originalScreeningActualCutBadEnvelope S w (Q.law : Measure _) b R (cuts a) ε) ∧
            {scene | ε * volume.real (originalCenteredPhysicalCubeRegion b (2 * R)) ≤
              |originalOrientedStageFullCutError S w b R (cuts a) scene|} ⊆
              originalScreeningActualCutBadEnvelope S w (Q.law : Measure _) b R (cuts a) ε ∧
            (Q.law : Measure _).real
                (originalScreeningActualCutBadEnvelope S w (Q.law : Measure _) b R (cuts a) ε) =
              (Q.law : Measure _).real
                {scene | ε * volume.real (originalCenteredPhysicalCubeRegion b (2 * R)) ≤
                  |originalOrientedStageFullCutError S w b R (cuts a) scene|}) ∧
          Tendsto (fun R : ℝ ↦ R^2 *
            ((∫ scene,
              (originalScreeningActualCutBadEnvelope S w (Q.law : Measure _) b R (cuts a) ε).indicator
                (originalScreeningPhysicalCubeActualCount b R) scene ∂(Q.law : Measure _)) /
              volume.real (originalCenteredPhysicalCubeRegion b (2 * R)))) atTop (𝓝 0) := by
  let q := finrank ℝ S.covector.ker
  let η := originalEuclideanMollifier q
  let clocks : I ⊕ J → Set ℝ := Sum.elim A (fun a ↦ Ioc (D.lo + (S.level : ℝ)) (cuts a))
  obtain ⟨hL2,b,hproj,hface,_hcutrates⟩ := D.exists_actualCanonical_screening_frame_cut_rates
    hF hw (by omega) cμ cν hρμ hρμ0 hρν hρν0 hv hv0 hdensityμ hdensityν hbounds hgap
    hg hgb τ Q hmin A cuts hcuts
  refine ⟨hL2,b,hproj,hface,?_⟩
  intro a ε hε
  refine ⟨fun R ↦ originalScreeningActualCutBadEnvelope_spec S w (Q.law : Measure _) b R (cuts a) ε, ?_⟩
  have hnormal : ∀ i, (translationFixedSubspace Q.sceneEuclideanKoopman (ℝ ∙ b i)ᗮ).starProjection
      (originalLinearCurrentReadoutLtwo (Q.law : Measure _)
        (originalSeedPathClockSetCurrent S w η (Ioc (D.lo + (S.level : ℝ)) (cuts a))) (hL2 (Sum.inr a))
        (originalEuclideanNormalReadout (b i))) = 0 := fun i ↦
    hproj i (Sum.inr a) (originalEuclideanNormalReadout (b i))
  exact D.tendsto_originalScreeningActualCutBadEnvelope_count_cost_zero hF hw hq hbounds Q b
    (hcuts a) (hL2 (Sum.inr a)) hnormal hε

end OTSelector.Reconstruction
