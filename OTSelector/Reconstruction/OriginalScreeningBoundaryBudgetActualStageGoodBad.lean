import OTSelector.Reconstruction.OriginalScreeningBoundaryBudgetActualStageFrame
import OTSelector.Reconstruction.OriginalScreeningBoundaryBudgetAllCutsBadCost
import OTSelector.Reconstruction.NormalizedHaarCubeCount

/-! One natural original frame controls all finite stage budgets and all actual cut exceptions. -/
open Set Function Filter MeasureTheory Module Manifold TopologicalSpace
open scoped ENNReal Topology ContDiff BigOperators InnerProductSpace Distributions
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
namespace OTSelector.Reconstruction
open OTSelector.Geometry ContinuousFinslerNorm OTSelector.Probability
local instance originalScreeningActualStageGoodBadColorMetric : MetricSpace (Fin 2) :=
  TopologicalSpace.metrizableSpaceMetric (Fin 2)
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {S : CalibratedLevelSeedPatch F u} {w : S.covector.ker} {μ ν : Measure ℝ}

/-- A natural original minimizer supplies one frame for the finite stage sum and the union
of every genuine cut exception. The collar geometry is derived from the scale limits,
and all actual stage objects share one scene event at every sufficiently large radius. -/
theorem OriginalSeedConditionalMoments.exists_actualCanonical_finiteStage_good_bad_budget
    (D : OriginalSeedConditionalMoments S w μ ν)
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    (hq : 4 < finrank ℝ S.covector.ker)
    {densityμ densityν : M → ℝ} {v : M → E → ℝ} (cμ cν : ℝ≥0∞)
    (hρμ : Continuous densityμ) (hρμ0 : ∀ x, 0 ≤ densityμ x)
    (hρν : Continuous densityν) (hρν0 : ∀ x, 0 ≤ densityν x)
    (hv : ∀ old, ContinuousOn (v old) (extChartAt 𝓘(ℝ, E) old).target)
    (hv0 : ∀ old, ∀ y ∈ (extChartAt 𝓘(ℝ, E) old).target, 0 ≤ v old y)
    (hdensityμ : PopulationSeedClockDensity S w
      (μ.map (fun x : ℝ ↦ x-S.level)) densityμ v cμ.toReal)
    (hdensityν : PopulationSeedClockDensity S w
      (ν.map (fun x : ℝ ↦ x-S.level)) densityν v cν.toReal)
    {gap diameter : ℝ} (hbounds : ConditionalClockSupportBounds μ ν gap diameter)
    (hgap : 0 < gap) {g : ℝ → ℝ → ℝ} {gBound : ℝ}
    (hg : Measurable (Function.uncurry g)) (hgb : ∀ x y, |g x y| ≤ gBound) (τ : ℝ)
    (Q : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν
      (D.originalFocalKinetic gap) g)
    (hmin : ∀ P : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν
      (D.originalFocalKinetic gap) g, Q.value τ ≤ P.value τ)
    {I J : Type*} [Fintype I] [Fintype J]
    (s t : I → ℝ) (hst : ∀ i, s i ≤ t i)
    (cuts : J → ℝ) (hcuts : ∀ a, D.lo + (S.level : ℝ) ≤ cuts a)
    {ell : ℝ → ℝ} (hell : ∀ᶠ R in atTop, 0 ≤ ell R)
    (hlarge : Tendsto ell atTop atTop) (hsmall : Tendsto (fun R ↦ ell R/R) atTop (𝓝 0)) :
    let q := finrank ℝ S.covector.ker
    let η := originalEuclideanMollifier q
    let clocks : I ⊕ J → Set ℝ :=
      Sum.elim (fun i ↦ Ioc (s i) (t i)) (fun a ↦ Ioc (D.lo + (S.level : ℝ)) (cuts a))
    ∃ hL2 : ∀ a k, MemLp (fun scene ↦ originalSeedPathClockSetCurrent S w η (clocks a) scene k) 2
        (Q.law : Measure (LegalMarkedOptimalInputScene q)),
      ∃ b : OrthonormalBasis (Fin q) ℝ (EuclideanSpace ℝ (Fin q)),
        (∀ K : I → ℝ → Compacts (Fin q → ℝ),
          ActualRealBudgetMean (Q.law : Measure _) (fun R ↦
              volume.real (originalCenteredPhysicalCubeRegion b (2*R)))
            (fun R scene ↦ ∑ i, originalOrientedStageCurrentInputNeumannBudget S w Q b (K i R)
              R (ell R) (s i) (t i) (hL2 (Sum.inl i)) scene)) ∧
        (∀ᶠ R : ℝ in atTop, 1 ≤ ell R ∧ 2*(originalStageFrameCollarFactor b*ell R) ≤ R ∧
          ∀ K : I → Compacts (Fin q → ℝ),
          ∀ᵐ scene ∂(Q.law : Measure (LegalMarkedOptimalInputScene q)),
            ∀ (i : I) (A : OriginalOrientedStageResidualDensityData S w b R (ell R)), A.scene = scene →
              ∀ φ : 𝓓_{K i}(Fin q → ℝ, ℝ),
              (∫ z in originalCenteredPhysicalCubeRegion b (2*R), φ z) = 0 →
              (∫ z in originalCenteredPhysicalCubeRegion b (2*R),
                (A.sourceDensity (s i) (t i) z-A.targetDensity (s i) (t i) z)*φ z)^2 ≤
                originalOrientedStageCurrentInputNeumannBudget S w Q b (K i) R (ell R)
                  (s i) (t i) (hL2 (Sum.inl i)) scene *
                    ‖smoothPhysicalGradientLtwo (K i)
                      (volume.restrict (originalCenteredPhysicalCubeRegion b (2*R))) φ‖^2) ∧
        ∀ ε : J → ℝ, (∀ a, 0 < ε a) →
          let bad := fun R ↦ ⋃ a, originalScreeningActualCutBadEnvelope S w
            (Q.law : Measure _) b R (cuts a) (ε a)
          (∀ R, MeasurableSet (bad R)) ∧
          (∀ R, (⋃ a, {scene | ε a*volume.real (originalCenteredPhysicalCubeRegion b (2*R)) ≤
            |originalOrientedStageFullCutError S w b R (cuts a) scene|}) ⊆ bad R) ∧
          Tendsto (fun R : ℝ ↦ R^2 *
            ((∫ scene, (bad R).indicator (originalScreeningPhysicalCubeActualCount b R) scene
              ∂(Q.law : Measure _)) / volume.real (originalCenteredPhysicalCubeRegion b (2*R))))
            atTop (𝓝 0) := by
  obtain ⟨hL2,b,hproj,hface,hmean,hstage,hcut⟩ := D.exists_actualCanonical_finiteStage_frame_budget_cut_costs
    hF hw hq cμ cν hρμ hρμ0 hρν hρν0 hv hv0 hdensityμ hdensityν hbounds hgap hg hgb
    τ Q hmin s t hst cuts hcuts hell hlarge hsmall
  refine ⟨hL2,b,fun K ↦ (hmean K).2,?_,?_⟩
  · filter_upwards [hlarge.eventually (eventually_ge_atTop (1:ℝ)),
      eventually_collar_mul_le_radius (k := 2*originalStageFrameCollarFactor b) hsmall]
      with R hellR hR
    have hgeom : 2*(originalStageFrameCollarFactor b*ell R) ≤ R := by nlinarith [hR]
    exact ⟨hellR,hgeom,hstage R hellR hgeom⟩
  · intro ε hε
    exact D.tendsto_all_originalScreening_cutBadEnvelope_count_cost_zero hF hw hq hbounds Q b cuts ε
      hcuts hε (fun a ↦ hL2 (Sum.inr a))
      (fun a k ↦ hproj k (Sum.inr a) (originalEuclideanNormalReadout (b k)))

end OTSelector.Reconstruction
