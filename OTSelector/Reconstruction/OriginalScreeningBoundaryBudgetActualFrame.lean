import OTSelector.Reconstruction.OriginalScreeningBoundaryBudgetPhysicalFaces
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
local instance originalScreeningActualFaceColorMetric : MetricSpace (Fin 2) :=
  TopologicalSpace.metrizableSpaceMetric (Fin 2)
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M→ℝ}
  {S : CalibratedLevelSeedPatch F u} {w : S.covector.ker} {μ ν : Measure ℝ}

/-- The same original minimizer and its actual two density laws internally produce one
common physical frame for every countable family of original clock restrictions. Actual
full-current face coefficients are measurable and integrable, have o(volume) expectation,
and control all physical mean-zero smooth tests; actual full flux has its true vanishing
surface-normalized second moment. No L2, projection, boundary or flux rate is an input. -/
theorem OriginalSeedConditionalMoments.exists_actualCanonicalCurrent_boundary_budget
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
    {I : Type*} [Countable I] (A : I → Set ℝ) :
    let q := finrank ℝ S.covector.ker
    let η := originalEuclideanMollifier q
    ∃ hL2 : ∀ a k, MemLp (fun scene ↦ originalSeedPathClockSetCurrent S w η (A a) scene k) 2
        (Q.law : Measure (LegalMarkedOptimalInputScene q)),
      ∃ b : OrthonormalBasis (Fin q) ℝ (EuclideanSpace ℝ (Fin q)),
        (∀ i a C, (translationFixedSubspace Q.sceneEuclideanKoopman (ℝ ∙ b i)ᗮ).starProjection
          (originalLinearCurrentReadoutLtwo (Q.law : Measure _)
            (originalSeedPathClockSetCurrent S w η (A a)) (hL2 a) C) = 0) ∧
        (∀ a L, Measurable (originalScreeningPhysicalFaceBudget Q b
            (originalSeedPathClockSetCurrent S w η (A a)) (hL2 a) L) ∧
          Integrable (originalScreeningPhysicalFaceBudget Q b
            (originalSeedPathClockSetCurrent S w η (A a)) (hL2 a) L) (Q.law : Measure _)) ∧
        (∀ a, Tendsto (fun L : ℝ ↦
          (∫ scene, originalScreeningPhysicalFaceBudget Q b
            (originalSeedPathClockSetCurrent S w η (A a)) (hL2 a) L scene ∂(Q.law : Measure _)) / L^q)
            atTop (𝓝 0)) ∧
        (∀ a L, 0 < L → ∀ᵐ scene ∂(Q.law : Measure (LegalMarkedOptimalInputScene q)),
          ∀ (K : Compacts (Fin q → ℝ)) (φ : 𝓓_{K}(Fin q → ℝ, ℝ)),
          (∫ z in originalCenteredPhysicalCubeRegion b L, φ z) = 0 →
          (originalScreeningPhysicalCurrentBoundaryPairing b
            (fun z ↦ originalSeedPathClockSetCurrent S w (fun x ↦ η (x-z)) (A a) scene) L φ)^2 ≤
            originalScreeningPhysicalFaceBudget Q b
              (originalSeedPathClockSetCurrent S w η (A a)) (hL2 a) L scene *
              ‖smoothPhysicalGradientLtwo K (volume.restrict (originalCenteredPhysicalCubeRegion b L)) φ‖^2) ∧
        ∀ a, Tendsto (fun R : ℝ ↦ ∫ scene,
          ((R^(q-1))⁻¹ * Q.sceneRawCenteredCubeFlux b
            (fun i ↦ originalLinearCurrentReadoutLtwo (Q.law : Measure _)
              (originalSeedPathClockSetCurrent S w η (A a)) (hL2 a)
              (originalEuclideanNormalReadout (b i))) R scene)^2 ∂(Q.law : Measure _)) atTop (𝓝 0) := by
  let q := finrank ℝ S.covector.ker
  let η := originalEuclideanMollifier q
  have hmη : Measurable η := (contDiff_originalEuclideanMollifier q).continuous.measurable
  have hη0 := originalEuclideanMollifier_nonneg q
  obtain ⟨hL2, b, hproj, hflux⟩ := D.exists_actual_coordinateLtwo_common_frame_rawFlux_zero
    hF hw hq cμ cν hρμ hρμ0 hρν hρν0 hv hv0 hdensityμ hdensityν hbounds hgap hg hgb τ Q hmin
    (fun _ : I ↦ η) (fun _ : I ↦ η) (fun _ ↦ hmη) (fun _ ↦ hmη)
    (fun _ ↦ integrable_originalEuclideanMollifier q) (fun _ ↦ hη0)
    (fun _ ↦ 1) (fun _ ↦ originalEuclideanMollifierBound q) (fun _ ↦ by norm_num)
    (fun _ ↦ originalEuclideanMollifierBound_nonneg q)
    (fun _ x ↦ (le_abs_self _).trans (abs_originalEuclideanMollifier_le q x))
    (fun _ x hx ↦ raw_unit_range_of_euclidean_unit_range (originalEuclideanMollifier_unit_range q) x hx.le)
    (fun _ x ↦ by rw [abs_of_nonneg (hη0 x)]) A
  refine ⟨hL2, b, hproj, ?_, ?_, ?_, hflux⟩
  · intro a L
    exact ⟨measurable_originalScreeningPhysicalFaceBudget Q b _ (hL2 a) L,
      integrable_originalScreeningPhysicalFaceBudget Q b _ (hL2 a) L⟩
  · intro a
    apply tendsto_originalScreeningPhysicalFaceBudget_mean_div_pow_zero Q b _ (hL2 a)
    intro i
    exact hproj i a (originalEuclideanNormalReadout (b i))
  · intro a L hL
    have hj : Measurable (originalSeedPathClockSetCurrent S w η (A a)) := by
      have h := (stronglyMeasurable_originalFullCurrent_joint_spatial S hF hw hmη (A a)).measurable.comp
        (measurable_id.prodMk (measurable_const : Measurable (fun _ : LegalMarkedOptimalInputScene q ↦ (0 : Fin q → ℝ))))
      simpa only [Function.comp_def, id_eq, sub_zero] using h
    have h := ae_all_originalScreeningPhysicalCurrentBoundaryPairing_sq_le Q b
      (originalSeedPathClockSetCurrent S w η (A a)) (hL2 a) hj hL
    simpa only [originalSeedPathClockSetCurrent_reroot S hF hw hmη] using h

end OTSelector.Reconstruction
