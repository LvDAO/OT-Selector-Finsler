import OTSelector.Reconstruction.OriginalStageResidualNeumannBudgetOrientedMean
import OTSelector.Reconstruction.OriginalStageReserveJoinedExperiment

/-! Actual fixed finite stage repair coefficients remain negligible on the original raw-reserve experiment. -/
open Set Function Filter MeasureTheory ProbabilityTheory Module Manifold TopologicalSpace
open scoped ENNReal NNReal Topology ContDiff BigOperators InnerProductSpace
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Geometry ContinuousFinslerNorm OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {S : CalibratedLevelSeedPatch F u} {w : S.covector.ker} {α β : Measure ℝ}

/-- The actual minimizer produces every weighted finite stage-mean estimate on
this same physical frame and original unit-main/raw-reserve product. Deterministic
support compacts may vary arbitrarily with radius; weights, including true block
width/floor coefficients, are fixed in radius. No expected-stage budget is an input. -/
theorem OriginalSeedConditionalMoments.original_screening_weightedNeumann_mean_zero
    (D : OriginalSeedConditionalMoments S w α β)
    [IsProbabilityMeasure α] [IsProbabilityMeasure β]
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels) (hq : 4 < finrank ℝ S.covector.ker)
    {densityα densityβ : M → ℝ} {v : M → E → ℝ} (cα cβ : ℝ≥0∞)
    (hρα : Continuous densityα) (hρα0 : ∀ x, 0 ≤ densityα x)
    (hρβ : Continuous densityβ) (hρβ0 : ∀ x, 0 ≤ densityβ x)
    (hv : ∀ old, ContinuousOn (v old) (extChartAt 𝓘(ℝ,E) old).target)
    (hv0 : ∀ old, ∀ y ∈ (extChartAt 𝓘(ℝ,E) old).target, 0 ≤ v old y)
    (hdensityα : PopulationSeedClockDensity S w (α.map (fun x : ℝ ↦ x-S.level)) densityα v cα.toReal)
    (hdensityβ : PopulationSeedClockDensity S w (β.map (fun x : ℝ ↦ x-S.level)) densityβ v cβ.toReal)
    {gap diameter : ℝ} (hbounds : ConditionalClockSupportBounds α β gap diameter) (hgap : 0 < gap)
    {g : ℝ → ℝ → ℝ} {G : ℝ} (hg : Measurable (Function.uncurry g)) (hgb : ∀ x y, |g x y| ≤ G)
    (τ : ℝ)
    (Q : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) α β (D.originalFocalKinetic gap) g)
    (hmin : ∀ Q' : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) α β
      (D.originalFocalKinetic gap) g, Q.value τ ≤ Q'.value τ)
    (b : OrthonormalBasis (Fin (finrank ℝ S.covector.ker)) ℝ
      (EuclideanSpace ℝ (Fin (finrank ℝ S.covector.ker))))
    {I : Type*} [Fintype I] (s t weight : I → ℝ)
    (K : I → ℝ → Compacts (Fin (finrank ℝ S.covector.ker) → ℝ))
    (hj : ∀ i k, MemLp (fun scene ↦ originalSeedPathClockSetCurrent S w
      (originalEuclideanMollifier _) (Ioc (s i) (t i)) scene k) 2 (Q.law : Measure _))
    (hproj : ∀ a i, (translationFixedSubspace Q.sceneEuclideanKoopman (ℝ ∙ b i)ᗮ).starProjection
      (originalLinearCurrentReadoutLtwo (Q.law : Measure _)
        (originalSeedPathClockSetCurrent S w (originalEuclideanMollifier _) (Ioc (s a) (t a)))
        (hj a) (originalEuclideanNormalReadout (b i))) = 0)
    (rho : ℝ) {ell : ℝ → ℝ} (hell : ∀ᶠ R in atTop, 0 ≤ ell R)
    (hlarge : Tendsto ell atTop atTop) (hsmall : Tendsto (fun R ↦ ell R/R) atTop (𝓝 0)) :
    let V := fun R ↦ volume.real (originalCenteredPhysicalCubeRegion b (2*R))
    let L := fun R ↦ originalMainReserveExperimentLaw Q (Real.toNNReal rho *
      (volume (originalCenteredPhysicalCubeRegion b (2*R))).toNNReal)
    let B := fun R p ↦ ∑ i, weight i * originalOrientedStageCurrentInputNeumannBudget S w Q b
      (K i R) R (ell R) (s i) (t i) (hj i) p.1
    (∀ R, 1 ≤ R → Measurable (B R) ∧ Integrable (B R) (L R)) ∧
      Tendsto (fun R : ℝ ↦ (∫ p, B R p ∂L R)/V R) atTop (𝓝 0) := by
  let q := finrank ℝ S.covector.ker
  let P := (Q.law : Measure (LegalMarkedOptimalInputScene q))
  let rate := fun R ↦ Real.toNNReal rho * (volume (originalCenteredPhysicalCubeRegion b (2*R))).toNNReal
  let Z := fun R ↦ twoMarkedCloudLaw q ℝ ℝ α β (rate R)
  let L := fun R ↦ originalMainReserveExperimentLaw Q (rate R)
  let B := fun i R scene ↦ originalOrientedStageCurrentInputNeumannBudget S w Q b
    (K i R) R (ell R) (s i) (t i) (hj i) scene
  let f := fun R scene ↦ ∑ i, weight i * B i R scene
  have hm (i) := D.original_minimizer_orientedStageCurrentInputNeumannBudget_mean_density_zero
    hF hw (by omega) b cα cβ hρα hρα0 hρβ hρβ0 hv hv0 hdensityα hdensityβ hbounds hgap
    hg hgb τ Q hmin (K i) (s i) (t i) (hj i) (hproj i) hell hlarge hsmall
  have hI (R) (hR : 1 ≤ R) : Integrable (f R) P :=
    integrable_finsetSum _ (fun i _ ↦ (((hm i).1 R hR).2).const_mul (weight i))
  have hM (R) (hR : 1 ≤ R) : Measurable (f R) :=
    Finset.measurable_fun_sum _ (fun i _ ↦ (((hm i).1 R hR).1).const_mul (weight i))
  refine ⟨fun R hR ↦ ⟨(hM R hR).comp measurable_fst,(hI R hR).comp_fst (Z R)⟩,?_⟩
  have hi (i) := ((hm i).2).const_mul (weight i)
  have hl := tendsto_finsetSum Finset.univ (fun i _ ↦ hi i)
  simp only [mul_zero,Finset.sum_const_zero] at hl
  apply hl.congr'
  filter_upwards [eventually_ge_atTop (1:ℝ)] with R hR
  have heq : (∫ p : LegalMarkedOptimalInputScene q × TwoMarkedCloudSpace q ℝ ℝ,
      f R p.1 ∂L R) = ∫ scene, f R scene ∂P := by
    simpa only [L,originalMainReserveExperimentLaw,P,Z,measureReal_def,measure_univ,
      ENNReal.toReal_one,one_smul] using integral_fun_fst (μ := P) (ν := Z R) (f R)
  change (∑ i, weight i*((∫ scene, B i R scene ∂P)/
      volume.real (originalCenteredPhysicalCubeRegion b (2*R)))) =
    (∫ p : LegalMarkedOptimalInputScene q × TwoMarkedCloudSpace q ℝ ℝ, f R p.1 ∂L R)/
      volume.real (originalCenteredPhysicalCubeRegion b (2*R))
  rw [heq]
  have hsum : (∫ scene, f R scene ∂P) = ∑ i, ∫ scene, weight i*B i R scene ∂P :=
    integral_finsetSum _ (fun i _ ↦ (((hm i).1 R hR).2).const_mul (weight i))
  rw [hsum,Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_const_mul]
  ring

end OTSelector.Reconstruction
