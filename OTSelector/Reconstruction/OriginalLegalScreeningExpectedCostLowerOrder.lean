import OTSelector.Reconstruction.OriginalLegalScreeningExpectedCostNeumannMean
import OTSelector.Reconstruction.OriginalLegalScreeningExpectedCostPortReserve
import OTSelector.Reconstruction.OriginalLegalScreeningExpectedCostCutFailures
import OTSelector.Reconstruction.OriginalLegalScreeningExpectedCostQuadratic

/-! The complete lower-order repair budget has negligible expected density on the actual original law. -/
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

/-- The genuine lower-order repair cost on the unchanged original joint law:
finite actual Neumann stages, actual ports, full-block leftovers and the same
joint failure count. Reserve RN energies and bounded unused-label tilt are paid
separately, since they carry the nonzero reserve-intensity contribution. -/
def originalScreeningLowerOrderCostBudget
    {I J : Type*} [Fintype I] [Fintype J]
    (S : CalibratedLevelSeedPatch F u) (w : S.covector.ker)
    {kin : ℝ → ℝ → (Fin (finrank ℝ S.covector.ker) → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (Q : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) α β kin g)
    (b : OrthonormalBasis (Fin (finrank ℝ S.covector.ker)) ℝ
      (EuclideanSpace ℝ (Fin (finrank ℝ S.covector.ker))))
    (K : I → Compacts (Fin (finrank ℝ S.covector.ker) → ℝ)) (R ell : ℝ)
    (s t weight : I → ℝ)
    (hj : ∀ i k, MemLp (fun scene ↦ originalSeedPathClockSetCurrent S w
      (originalEuclideanMollifier _) (Ioc (s i) (t i)) scene k) 2 (Q.law : Measure _))
    (rho : ℝ) (grid : OriginalStageClockGrid) (r : ℝ) (cuts ε : J → ℝ) (C Ltilt : ℝ)
    (p : LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker) ×
      TwoMarkedCloudSpace (finrank ℝ S.covector.ker) ℝ ℝ) : ℝ :=
  (∑ i, weight i * originalOrientedStageCurrentInputNeumannBudget S w Q b
    (K i) R ell (s i) (t i) (hj i) p.1) +
  3*C*(((originalStageWindowSourcePortPlan (originalOrientedPathLengthRetained S w b R ell)
    (originalCenteredPhysicalCubeRegion b (2*R)) p.1 :
      Measure (LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker))) univ).toReal +
    ((originalStageWindowTargetPortPlan (originalOrientedPathLengthRetained S w b R ell)
      (originalCenteredPhysicalCubeRegion b (2*R)) p.1 :
        Measure (LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker))) univ).toReal) +
  (4*C*(finrank ℝ S.covector.ker : ℝ)*R^2+Ltilt)*
    originalFullClockSlabDiscrepancy (α := α) (β := β) grid
      (originalCenteredPhysicalCubeRegion b (2*R)) p +
  (4*C*(finrank ℝ S.covector.ker : ℝ)*R^2+2*Ltilt)*
    (originalScreeningAllFailure S w α β (Q.law : Measure _) b rho R grid r cuts ε).indicator
      (originalScreeningFullExperimentCount (originalCenteredPhysicalCubeRegion b (2*R))) p

/-- All four literal lower-order costs are integrable and their total expected
cost is negligible per the same physical volume. Actual minimizer, current,
Poisson and capacity arguments produce every component estimate internally. -/
theorem OriginalSeedConditionalMoments.original_screening_lowerOrderCostBudget_mean_zero
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
    {rho r : ℝ} (hrho : 0 < rho) (grid : OriginalStageClockGrid) (hr : 0 < r)
    (hmono : ∀ i, α (grid.sourceCell i) = 0 ∨ β (grid.targetCell i) = 0)
    (hH : ∀ k ≤ grid.count, 0 ≤ grid.clockSlabSurplus α β k)
    {J : Type*} [Fintype J] (cuts ε : J → ℝ)
    (hcuts : ∀ i, D.lo+(S.level : ℝ) ≤ cuts i) (hε : ∀ i, 0 < ε i)
    (hcj : ∀ i k, MemLp (fun scene ↦ originalSeedPathClockSetCurrent S w
      (originalEuclideanMollifier _) (Ioc (D.lo+(S.level : ℝ)) (cuts i)) scene k) 2
      (Q.law : Measure _))
    (hcproj : ∀ a i, (translationFixedSubspace Q.sceneEuclideanKoopman (ℝ ∙ b i)ᗮ).starProjection
      (originalLinearCurrentReadoutLtwo (Q.law : Measure _)
        (originalSeedPathClockSetCurrent S w (originalEuclideanMollifier _)
          (Ioc (D.lo+(S.level : ℝ)) (cuts a))) (hcj a) (originalEuclideanNormalReadout (b i))) = 0)
    (C Ltilt : ℝ) {ell : ℝ → ℝ} (hell : ∀ᶠ R in atTop, 0 ≤ ell R)
    (hlarge : Tendsto ell atTop atTop) (hsmall : Tendsto (fun R ↦ ell R/R) atTop (𝓝 0)) :
    let V := fun R ↦ volume.real (originalCenteredPhysicalCubeRegion b (2*R))
    let Law := fun R ↦ originalMainReserveExperimentLaw Q (Real.toNNReal rho *
      (volume (originalCenteredPhysicalCubeRegion b (2*R))).toNNReal)
    let B := fun R ↦ originalScreeningLowerOrderCostBudget S w Q b (fun i ↦ K i R)
      R (ell R) s t weight hj rho grid r cuts ε C Ltilt
    (∀ R, 1 ≤ R → Integrable (B R) (Law R)) ∧
      Tendsto (fun R : ℝ ↦ (∫ p, B R p ∂Law R)/V R) atTop (𝓝 0) := by
  let q := finrank ℝ S.covector.ker
  let V := fun R ↦ volume.real (originalCenteredPhysicalCubeRegion b (2*R))
  let P := (Q.law : Measure (LegalMarkedOptimalInputScene q))
  let Z := fun R ↦ twoMarkedCloudLaw q ℝ ℝ α β
    (Real.toNNReal rho * (volume (originalCenteredPhysicalCubeRegion b (2*R))).toNNReal)
  let Law := fun R ↦ originalMainReserveExperimentLaw Q
    (Real.toNNReal rho * (volume (originalCenteredPhysicalCubeRegion b (2*R))).toNNReal)
  let stages := fun R (p : LegalMarkedOptimalInputScene q × TwoMarkedCloudSpace q ℝ ℝ) ↦ ∑ i, weight i * originalOrientedStageCurrentInputNeumannBudget S w Q b
    (K i R) R (ell R) (s i) (t i) (hj i) p.1
  let ports := fun R scene ↦
    ((originalStageWindowSourcePortPlan (originalOrientedPathLengthRetained S w b R (ell R))
      (originalCenteredPhysicalCubeRegion b (2*R)) scene : Measure (LegalMarkedPhysicalEdge q)) univ).toReal +
    ((originalStageWindowTargetPortPlan (originalOrientedPathLengthRetained S w b R (ell R))
      (originalCenteredPhysicalCubeRegion b (2*R)) scene : Measure (LegalMarkedPhysicalEdge q)) univ).toReal
  let portCost := fun R (p : LegalMarkedOptimalInputScene q × TwoMarkedCloudSpace q ℝ ℝ) ↦ 3*C*ports R p.1
  let blockCost := fun R p ↦ (4*C*(q:ℝ)*R^2+Ltilt)*originalFullClockSlabDiscrepancy
    (α := α) (β := β) grid (originalCenteredPhysicalCubeRegion b (2*R)) p
  let bad := fun R ↦ originalScreeningAllFailure S w α β P b rho R grid r cuts ε
  let badCount := fun R ↦ (bad R).indicator
    (originalScreeningFullExperimentCount (originalCenteredPhysicalCubeRegion b (2*R)))
  let badCost := fun R p ↦ (4*C*(q:ℝ)*R^2+2*Ltilt)*badCount R p
  have hs := D.original_screening_weightedNeumann_mean_zero hF hw hq cα cβ
    hρα hρα0 hρβ hρβ0 hv hv0 hdensityα hdensityβ hbounds hgap hg hgb τ Q hmin
    b s t weight K hj hproj rho hell hlarge hsmall
  have hp := D.originalOrientedStagePortCount_mean_density_zero hF hw Q b hell hlarge hsmall
  have hportI (R) : Integrable (portCost R) (Law R) :=
    (((hp.1 R).2).comp_fst (Z R)).const_mul (3*C)
  have hportL : Tendsto (fun R : ℝ ↦ (∫ p, portCost R p ∂Law R)/V R) atTop (𝓝 0) := by
    have hh := hp.2.const_mul (3*C)
    simp only [mul_zero] at hh
    apply hh.congr'
    exact Eventually.of_forall fun R ↦ by
      have heq : (∫ p : LegalMarkedOptimalInputScene q × TwoMarkedCloudSpace q ℝ ℝ,
          ports R p.1 ∂Law R) = ∫ scene, ports R scene ∂P := by
        simpa only [Law,originalMainReserveExperimentLaw,P,Z,measureReal_def,measure_univ,
          ENNReal.toReal_one,one_smul] using integral_fun_fst (μ := P) (ν := Z R) (ports R)
      change 3*C*((∫ scene, ports R scene ∂P)/V R) =
        (∫ p, 3*C*ports R p.1 ∂Law R)/V R
      rw [integral_const_mul,heq]
      ring
  have hblockI (R) : Integrable (blockCost R) (Law R) :=
    (Q.originalFullClockSlabDiscrepancy_integrable_and_integral_le b R (Real.toNNReal rho) grid).1.const_mul _
  have hblockL := Q.tendsto_original_screening_blockCompletion_cost_zero hq b rho grid
    (4*C*(q:ℝ)) Ltilt
  have hb := D.original_screening_allFailure_count_cost hF hw hq hbounds Q b hrho grid hr
    hmono hH cuts ε hcuts hε hcj hcproj
  have hbadI (R) : Integrable (badCost R) (Law R) :=
    ((Q.original_screening_fullExperimentCount (Real.toNNReal rho *
      (volume (originalCenteredPhysicalCubeRegion b (2*R))).toNNReal)
      (isCompact_originalStagePhysicalCube b (2*R)).measurableSet
      (isCompact_originalStagePhysicalCube b (2*R)).measure_ne_top).1.indicator (hb.1 R)).const_mul _
  have hbadL : Tendsto (fun R : ℝ ↦ (∫ p, badCost R p ∂Law R)/V R) atTop (𝓝 0) := by
    apply (tendsto_weighted_quadratic_zero_of_quadratic_zero hb.2.2 (4*C*(q:ℝ)) (2*Ltilt)).congr'
    exact Eventually.of_forall fun R ↦ by
      dsimp only
      rw [integral_const_mul]
      ring
  refine ⟨fun R hR ↦ (((hs.1 R hR).2.add (hportI R)).add (hblockI R)).add (hbadI R),?_⟩
  have hsum := ((hs.2.add hportL).add hblockL).add hbadL
  simp only [add_zero] at hsum
  apply hsum.congr'
  filter_upwards [eventually_ge_atTop (1:ℝ)] with R hR
  change (((∫ p, stages R p ∂Law R)/V R+(∫ p, portCost R p ∂Law R)/V R)+
    (∫ p, blockCost R p ∂Law R)/V R)+(∫ p, badCost R p ∂Law R)/V R = _
  have heq : (∫ p, ((stages R p+portCost R p)+blockCost R p)+badCost R p ∂Law R) =
      (((∫ p, stages R p ∂Law R)+(∫ p, portCost R p ∂Law R))+
        (∫ p, blockCost R p ∂Law R))+(∫ p, badCost R p ∂Law R) := by
    have hab : (∫ p, stages R p+portCost R p ∂Law R) =
        (∫ p, stages R p ∂Law R)+(∫ p, portCost R p ∂Law R) :=
      integral_add (hs.1 R hR).2 (hportI R)
    have habc : (∫ p, (stages R p+portCost R p)+blockCost R p ∂Law R) =
        (∫ p, stages R p+portCost R p ∂Law R)+(∫ p, blockCost R p ∂Law R) :=
      integral_add ((hs.1 R hR).2.add (hportI R)) (hblockI R)
    have habcd : (∫ p, ((stages R p+portCost R p)+blockCost R p)+badCost R p ∂Law R) =
        (∫ p, (stages R p+portCost R p)+blockCost R p ∂Law R)+(∫ p, badCost R p ∂Law R) :=
      integral_add (((hs.1 R hR).2.add (hportI R)).add (hblockI R)) (hbadI R)
    exact habcd.trans (congrArg (fun z : ℝ ↦ z+(∫ p, badCost R p ∂Law R))
      (habc.trans (congrArg (fun z : ℝ ↦ z+(∫ p, blockCost R p ∂Law R)) hab)))
  change (((∫ p, stages R p ∂Law R)/V R+(∫ p, portCost R p ∂Law R)/V R)+
    (∫ p, blockCost R p ∂Law R)/V R)+(∫ p, badCost R p ∂Law R)/V R =
    (∫ p, ((stages R p+portCost R p)+blockCost R p)+badCost R p ∂Law R)/V R
  rw [heq]
  simp only [add_div]

end OTSelector.Reconstruction
