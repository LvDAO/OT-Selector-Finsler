import OTSelector.Reconstruction.OriginalScreeningBoundaryBudgetActualCutCostFrame
import OTSelector.Reconstruction.OriginalStageResidualNeumannBudgetOrientedMean
import OTSelector.Reconstruction.OriginalStageResidualNeumannBudgetOrientedCanonical

/-! One original frame simultaneously controls finitely many actual stage budgets and cuts. -/
open Set Function Filter MeasureTheory Module Manifold TopologicalSpace
open scoped ENNReal Topology ContDiff BigOperators InnerProductSpace Distributions
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
namespace OTSelector.Reconstruction
open OTSelector.Geometry ContinuousFinslerNorm OTSelector.Probability

/-- A real budget is measurable and integrable at every radius at least one, with its
actual expectation negligible relative to the specified physical volume. -/
abbrev ActualRealBudgetMean {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (V : ℝ → ℝ) (B : ℝ → Ω → ℝ) : Prop :=
  (∀ R, 1 ≤ R → Measurable (B R) ∧ Integrable (B R) P) ∧
    Tendsto (fun R : ℝ ↦ (∫ sample, B R sample ∂P) / V R) atTop (𝓝 0)

/-- A fixed finite sum of actual budgets keeps measurability, integrability and the
same vanishing volume-normalized mean, including an empty stage family. -/
theorem finite_sum_actualRealBudgetMean
    {Ω I : Type*} [MeasurableSpace Ω] [Fintype I]
    (P : Measure Ω) (V : ℝ → ℝ) (B : I → ℝ → Ω → ℝ)
    (hB : ∀ i, ActualRealBudgetMean P V (B i)) :
    ActualRealBudgetMean P V (fun R sample ↦ ∑ i, B i R sample) := by
  refine ⟨fun R hR ↦ ⟨Finset.measurable_fun_sum _ (fun i _ ↦ ((hB i).1 R hR).1),
    integrable_finsetSum _ (fun i _ ↦ ((hB i).1 R hR).2)⟩, ?_⟩
  have hlim := tendsto_finsetSum Finset.univ (fun i _ ↦ (hB i).2)
  simp only [Finset.sum_const_zero] at hlim
  apply hlim.congr'
  filter_upwards [eventually_ge_atTop (1:ℝ)] with R hR
  rw [integral_finsetSum _ (fun i _ ↦ ((hB i).1 R hR).2), Finset.sum_div]

local instance originalScreeningActualStageFaceColorMetric : MetricSpace (Fin 2) :=
  TopologicalSpace.metrizableSpaceMetric (Fin 2)
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {S : CalibratedLevelSeedPatch F u} {w : S.covector.ker} {μ ν : Measure ℝ}

/-- The original minimizer produces one actual physical frame for finitely many ordered
stage clock slabs and countably many cuts. Every actual stage and their fixed finite sum
have measurable integrable budgets with vanishing normalized expectation. On every
admissible radius one scene event controls all stages and all actual stage objects; the
same frame also pays every genuine cut's actual full-input-count exceptional cost. -/
theorem OriginalSeedConditionalMoments.exists_actualCanonical_finiteStage_frame_budget_cut_costs
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
    {I J : Type*} [Fintype I] [Countable J]
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
        (∀ i a C, (translationFixedSubspace Q.sceneEuclideanKoopman (ℝ ∙ b i)ᗮ).starProjection
          (originalLinearCurrentReadoutLtwo (Q.law : Measure _)
            (originalSeedPathClockSetCurrent S w η (clocks a)) (hL2 a) C) = 0) ∧
        (∀ a, Tendsto (fun L : ℝ ↦
          (∫ scene, originalScreeningPhysicalFaceBudget Q b
            (originalSeedPathClockSetCurrent S w η (clocks a)) (hL2 a) L scene ∂(Q.law : Measure _))/L^q)
            atTop (𝓝 0)) ∧
        (∀ K : I → ℝ → Compacts (Fin q → ℝ),
          (∀ i, ActualRealBudgetMean (Q.law : Measure _) (fun R ↦
              volume.real (originalCenteredPhysicalCubeRegion b (2*R)))
            (fun R ↦ originalOrientedStageCurrentInputNeumannBudget S w Q b (K i R)
              R (ell R) (s i) (t i) (hL2 (Sum.inl i)))) ∧
          ActualRealBudgetMean (Q.law : Measure _) (fun R ↦
              volume.real (originalCenteredPhysicalCubeRegion b (2*R)))
            (fun R scene ↦ ∑ i, originalOrientedStageCurrentInputNeumannBudget S w Q b (K i R)
              R (ell R) (s i) (t i) (hL2 (Sum.inl i)) scene)) ∧
        (∀ (R : ℝ), 1 ≤ ell R → 2*(originalStageFrameCollarFactor b*ell R) ≤ R →
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
        ∀ (a : J) (ε : ℝ), 0 < ε →
          (∀ R : ℝ,
            MeasurableSet (originalScreeningActualCutBadEnvelope S w (Q.law : Measure _) b R (cuts a) ε) ∧
            {scene | ε * volume.real (originalCenteredPhysicalCubeRegion b (2*R)) ≤
              |originalOrientedStageFullCutError S w b R (cuts a) scene|} ⊆
              originalScreeningActualCutBadEnvelope S w (Q.law : Measure _) b R (cuts a) ε ∧
            (Q.law : Measure _).real
                (originalScreeningActualCutBadEnvelope S w (Q.law : Measure _) b R (cuts a) ε) =
              (Q.law : Measure _).real
                {scene | ε * volume.real (originalCenteredPhysicalCubeRegion b (2*R)) ≤
                  |originalOrientedStageFullCutError S w b R (cuts a) scene|}) ∧
          Tendsto (fun R : ℝ ↦ R^2 *
            ((∫ scene,
              (originalScreeningActualCutBadEnvelope S w (Q.law : Measure _) b R (cuts a) ε).indicator
                (originalScreeningPhysicalCubeActualCount b R) scene ∂(Q.law : Measure _))/
              volume.real (originalCenteredPhysicalCubeRegion b (2*R)))) atTop (𝓝 0) := by
  let q := finrank ℝ S.covector.ker
  let η := originalEuclideanMollifier q
  obtain ⟨hL2,b,hproj,hface,hcut⟩ := D.exists_actualCanonical_screening_frame_cut_costs
    hF hw hq cμ cν hρμ hρμ0 hρν hρν0 hv hv0 hdensityμ hdensityν hbounds hgap
    hg hgb τ Q hmin (fun i ↦ Ioc (s i) (t i)) cuts hcuts
  refine ⟨hL2,b,hproj,hface,?_,?_,hcut⟩
  · intro K
    have hmeans (i : I) := D.original_minimizer_orientedStageCurrentInputNeumannBudget_mean_density_zero
      hF hw (by omega) b cμ cν hρμ hρμ0 hρν hρν0 hv hv0 hdensityμ hdensityν hbounds hgap
      hg hgb τ Q hmin (K i) (s i) (t i) (hL2 (Sum.inl i))
      (fun k ↦ hproj k (Sum.inl i) (originalEuclideanNormalReadout (b k))) hell hlarge hsmall
    exact ⟨hmeans, finite_sum_actualRealBudgetMean (Q.law : Measure _)
      (fun R ↦ volume.real (originalCenteredPhysicalCubeRegion b (2*R)))
      (fun i R ↦ originalOrientedStageCurrentInputNeumannBudget S w Q b (K i R)
        R (ell R) (s i) (t i) (hL2 (Sum.inl i))) hmeans⟩
  · intro R hellR hR K
    apply ae_all_iff.mpr
    intro i
    exact D.ae_all_originalOrientedStageResidualDensity_Neumann_bound hF hw (by omega)
      hbounds Q b (K i) hellR hR (hst i) (hL2 (Sum.inl i))

end OTSelector.Reconstruction
