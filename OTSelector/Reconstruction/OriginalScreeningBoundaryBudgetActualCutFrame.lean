import OTSelector.Reconstruction.OriginalScreeningBoundaryBudgetActualFrame
import OTSelector.Reconstruction.OriginalScreeningBoundaryBudgetOrientedCutProbability
import OTSelector.Reconstruction.OriginalMinimizerActualRawFlux
import OTSelector.Reconstruction.OriginalOmittedCurrentSpatialBridgeMeasurability
import OTSelector.Reconstruction.OriginalEuclideanMollifierChoice

/-! One actually produced original frame supplies the full-current screening face budget. -/
open Set Function Filter MeasureTheory Module Manifold TopologicalSpace
open scoped ENNReal Topology ContDiff BigOperators InnerProductSpace Distributions
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
namespace OTSelector.Reconstruction
open OTSelector.Geometry ContinuousFinslerNorm OTSelector.Probability
local instance originalScreeningActualCutFaceColorMetric : MetricSpace (Fin 2) :=
  TopologicalSpace.metrizableSpaceMetric (Fin 2)
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M→ℝ}
  {S : CalibratedLevelSeedPatch F u} {w : S.covector.ker} {μ ν : Measure ℝ}

/-- The original minimizer supplies one common physical frame for both arbitrary countable
stage currents and countably many genuine full-main cuts. All current L2, normal projection,
face-mean and actual delta L2/probability rates are produced internally from the original law. -/
theorem OriginalSeedConditionalMoments.exists_actualCanonical_screening_frame_cut_rates
    (D : OriginalSeedConditionalMoments S w μ ν)
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    (hq : 2 < finrank ℝ S.covector.ker)
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
        ∀ a : J,
          (∀ R, 1 ≤ R → MemLp (originalOrientedStageFullCutError S w b R (cuts a)) 2
            (Q.law : Measure _)) ∧
          Tendsto (fun R : ℝ ↦ ∫ scene,
            ((R^(q-1))⁻¹ * originalOrientedStageFullCutError S w b R (cuts a) scene)^2
              ∂(Q.law : Measure (LegalMarkedOptimalInputScene q))) atTop (𝓝 0) ∧
          ∀ ε : ℝ, 0 < ε → Tendsto (fun R : ℝ ↦ R^2 * (Q.law : Measure _).real
            {scene | ε*volume.real (originalCenteredPhysicalCubeRegion b (2*R)) ≤
              |originalOrientedStageFullCutError S w b R (cuts a) scene|}) atTop (𝓝 0) := by
  let q := finrank ℝ S.covector.ker
  let η := originalEuclideanMollifier q
  let clocks : I ⊕ J → Set ℝ := Sum.elim A (fun a ↦ Ioc (D.lo + (S.level : ℝ)) (cuts a))
  obtain ⟨hL2, b, hproj, _, hface, _, _⟩ := D.exists_actualCanonicalCurrent_boundary_budget
    hF hw hq cμ cν hρμ hρμ0 hρν hρν0 hv hv0 hdensityμ hdensityν hbounds hgap hg hgb τ Q hmin clocks
  refine ⟨hL2, b, hproj, hface, ?_⟩
  intro a
  have hnormal : ∀ i, (translationFixedSubspace Q.sceneEuclideanKoopman (ℝ ∙ b i)ᗮ).starProjection
      (originalLinearCurrentReadoutLtwo (Q.law : Measure _)
        (originalSeedPathClockSetCurrent S w η (Ioc (D.lo + (S.level : ℝ)) (cuts a))) (hL2 (Sum.inr a))
        (originalEuclideanNormalReadout (b i))) = 0 := fun i ↦
    hproj i (Sum.inr a) (originalEuclideanNormalReadout (b i))
  have hδ := D.originalOrientedStageFullCutError_surface_ltwo_zero hF hw (by omega)
    hbounds Q b (hcuts a) (hL2 (Sum.inr a)) hnormal
  refine ⟨hδ.1, hδ.2, ?_⟩
  intro ε hε
  exact D.tendsto_originalOrientedStageFullCutError_quadratic_bad_probability_zero
    hF hw (by omega) hbounds Q b (hcuts a) (hL2 (Sum.inr a)) hnormal hε

end OTSelector.Reconstruction
