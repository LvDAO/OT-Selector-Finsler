import OTSelector.Reconstruction.OriginalLegalScreeningExpectedCostLowerOrder
import OTSelector.Reconstruction.OriginalLegalScreeningExpectedCostReserve
import OTSelector.Reconstruction.OriginalLegalScreeningComparatorOrientedRetainedCostLimit

/-! Expected cost of the genuine complete screening budget, preserving the signed core. -/
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

/-- The original signed retained core plus its literal repair terms on one
original unit-main/raw-reserve observation. This is a cost budget, before the
separately constructed actual finite legal comparator is plugged into it. -/
def originalScreeningCompleteCostBudget
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
    {H : Type*} [Fintype H] (RS RT RCs RCt RDs RDt : H → Set ℝ) (τ : ℝ)
    (p : LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker) ×
      TwoMarkedCloudSpace (finrank ℝ S.covector.ker) ℝ ℝ) : ℝ :=
  (∫ e, originalWeightedEdgeCost kin g τ e
    ∂(originalStageRestrictedPathPlan (originalOrientedPathLengthRetained S w b R ell) p.1 :
      Measure (LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker)))) +
    originalScreeningLowerOrderCostBudget S w Q b K R ell s t weight hj rho grid r cuts ε C Ltilt p +
    3*C*originalScreeningReserveEndpointEnergy b R RS RT RCs RCt RDs RDt p +
    Ltilt*originalScreeningRepairCountBudget S w b R ell p

/-- The actual complete cost budget is integrable and its normalized expectation
is bounded by the unchanged signed weighted value, the explicit sublinear reserve
term and the linear bounded-probe reserve term. All other actual costs vanish;
no expected-cost bound, tail rate or core Euclidean moment is an input. -/
theorem OriginalSeedConditionalMoments.original_screening_completeCostBudget_expected_bound
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
    {H : Type*} [Fintype H] (RS RT RCs RCt RDs RDt : H → Set ℝ)
    (hRS : ∀ i, MeasurableSet (RS i)) (hRT : ∀ i, MeasurableSet (RT i))
    (hRCs : ∀ i, MeasurableSet (RCs i)) (hRCt : ∀ i, MeasurableSet (RCt i))
    (hRDs : ∀ i, MeasurableSet (RDs i)) (hRDt : ∀ i, MeasurableSet (RDt i))
    (C Ltilt : ℝ) (hC : 0 ≤ C) {ell : ℝ → ℝ} (hell : ∀ᶠ R in atTop, 0 ≤ ell R)
    (hlarge : Tendsto ell atTop atTop) (hsmall : Tendsto (fun R ↦ ell R/R) atTop (𝓝 0)) :
    let V := fun R ↦ volume.real (originalCenteredPhysicalCubeRegion b (2*R))
    let Law := fun R ↦ originalMainReserveExperimentLaw Q (Real.toNNReal rho *
      (volume (originalCenteredPhysicalCubeRegion b (2*R))).toNNReal)
    let B := fun R ↦ originalScreeningCompleteCostBudget S w Q b (fun i ↦ K i R)
      R (ell R) s t weight hj rho grid r cuts ε C Ltilt RS RT RCs RCt RDs RDt τ
    (∀ R, 1 ≤ R → Integrable (B R) (Law R)) ∧
      ∀ δ > 0, ∀ᶠ R : ℝ in atTop, (∫ p, B R p ∂Law R)/V R ≤
        Q.value τ + (6*C*(Fintype.card H : ℝ)*(finrank ℝ S.covector.ker : ℝ)*
          dyadicMatchingConstant (finrank ℝ S.covector.ker))*rho^(1-2/(finrank ℝ S.covector.ker : ℝ)) +
          2*Ltilt*rho+δ := by
  let q := finrank ℝ S.covector.ker
  let V := fun R ↦ volume.real (originalCenteredPhysicalCubeRegion b (2*R))
  let P := (Q.law : Measure (LegalMarkedOptimalInputScene q))
  let Z := fun R ↦ twoMarkedCloudLaw q ℝ ℝ α β
    (Real.toNNReal rho * (volume (originalCenteredPhysicalCubeRegion b (2*R))).toNNReal)
  let Law := fun R ↦ originalMainReserveExperimentLaw Q
    (Real.toNNReal rho * (volume (originalCenteredPhysicalCubeRegion b (2*R))).toNNReal)
  let core := fun R scene ↦ ∫ e, originalWeightedEdgeCost (D.originalFocalKinetic gap) g τ e
    ∂(originalStageRestrictedPathPlan (originalOrientedPathLengthRetained S w b R (ell R)) scene :
      Measure (LegalMarkedPhysicalEdge q))
  let lower := fun R ↦ originalScreeningLowerOrderCostBudget S w Q b (fun i ↦ K i R)
    R (ell R) s t weight hj rho grid r cuts ε C Ltilt
  let reserve := fun R ↦ originalScreeningReserveEndpointEnergy b R RS RT RCs RCt RDs RDt
  let repair := fun R ↦ originalScreeningRepairCountBudget S w b R (ell R)
  let regular := fun R (p : LegalMarkedOptimalInputScene q × TwoMarkedCloudSpace q ℝ ℝ) ↦
    (core R p.1+lower R p)+Ltilt*repair R p
  have hk := D.measurable_originalFocalKinetic hF hw gap
  have hcoreI (R) : Integrable (fun p : LegalMarkedOptimalInputScene q × TwoMarkedCloudSpace q ℝ ℝ ↦
      core R p.1) (Law R) :=
    (originalOrientedPathRetainedPlan_weightedCost_integrable_and_integral hF hw Q hk hg b
      R (ell R) τ).1.comp_fst (Z R)
  have hcoreL : Tendsto (fun R : ℝ ↦ (∫ p : LegalMarkedOptimalInputScene q ×
      TwoMarkedCloudSpace q ℝ ℝ, core R p.1 ∂Law R)/V R) atTop (𝓝 (Q.value τ)) := by
    apply (tendsto_originalOrientedPathRetainedPlan_normalized_weightedCost hF hw Q hk hg b τ
      hell hlarge hsmall).congr'
    exact Eventually.of_forall fun R ↦ by
      have heq : (∫ p : LegalMarkedOptimalInputScene q × TwoMarkedCloudSpace q ℝ ℝ,
          core R p.1 ∂Law R) = ∫ scene, core R scene ∂P := by
        simpa only [Law,originalMainReserveExperimentLaw,P,Z,measureReal_def,measure_univ,
          ENNReal.toReal_one,one_smul] using integral_fun_fst (μ := P) (ν := Z R) (core R)
      exact congrArg (fun z : ℝ ↦ z/V R) heq.symm
  have hlower := D.original_screening_lowerOrderCostBudget_mean_zero hF hw hq cα cβ
    hρα hρα0 hρβ hρβ0 hv hv0 hdensityα hdensityβ hbounds hgap hg hgb τ Q hmin
    b s t weight K hj hproj hrho grid hr hmono hH cuts ε hcuts hε hcj hcproj C Ltilt hell hlarge hsmall
  have hrepair := D.original_screening_repairCountBudget_mean hF hw Q b hrho.le hell hlarge hsmall
  have hreserve (R) (hR : 0 < R) := Q.original_screening_reserveEndpointEnergy b hR hrho.le hq
    RS RT RCs RCt RDs RDt hRS hRT hRCs hRCt hRDs hRDt
  have hregularI (R) (hR : 1 ≤ R) : Integrable (regular R) (Law R) :=
    ((hcoreI R).add (hlower.1 R hR)).add ((hrepair.1 R).const_mul Ltilt)
  have hregularL : Tendsto (fun R : ℝ ↦ (∫ p, regular R p ∂Law R)/V R)
      atTop (𝓝 (Q.value τ+2*Ltilt*rho)) := by
    have hh := (hcoreL.add hlower.2).add (hrepair.2.const_mul Ltilt)
    simp only [add_zero] at hh
    have hlim : Q.value τ+Ltilt*(2*rho) = Q.value τ+2*Ltilt*rho := by ring
    rw [hlim] at hh
    apply hh.congr'
    filter_upwards [eventually_ge_atTop (1:ℝ)] with R hR
    have hab : (∫ p, core R p.1+lower R p ∂Law R) =
        (∫ p, core R p.1 ∂Law R)+(∫ p, lower R p ∂Law R) :=
      integral_add (hcoreI R) (hlower.1 R hR)
    have habc : (∫ p, regular R p ∂Law R) =
        (∫ p, core R p.1+lower R p ∂Law R)+(∫ p, Ltilt*repair R p ∂Law R) :=
      integral_add ((hcoreI R).add (hlower.1 R hR)) ((hrepair.1 R).const_mul Ltilt)
    rw [hab,integral_const_mul] at habc
    change ((∫ p, core R p.1 ∂Law R)/V R+(∫ p, lower R p ∂Law R)/V R)+
      Ltilt*((∫ p, repair R p ∂Law R)/V R) = (∫ p, regular R p ∂Law R)/V R
    rw [habc]
    ring
  have hfullI (R) (hR : 1 ≤ R) : Integrable
      (originalScreeningCompleteCostBudget S w Q b (fun i ↦ K i R) R (ell R)
        s t weight hj rho grid r cuts ε C Ltilt RS RT RCs RCt RDs RDt τ) (Law R) :=
    (((hcoreI R).add (hlower.1 R hR)).add ((hreserve R (by linarith)).1.const_mul (3*C))).add
      ((hrepair.1 R).const_mul Ltilt)
  refine ⟨hfullI,fun δ hδ ↦ ?_⟩
  filter_upwards [hregularL.eventually_lt_const (lt_add_of_pos_right _ hδ),
    eventually_ge_atTop (1:ℝ)] with R hreg hR
  have heq : (∫ p, originalScreeningCompleteCostBudget S w Q b (fun i ↦ K i R) R (ell R)
        s t weight hj rho grid r cuts ε C Ltilt RS RT RCs RCt RDs RDt τ p ∂Law R) =
      (∫ p, regular R p ∂Law R)+3*C*(∫ p, reserve R p ∂Law R) := by
    have hpoint : (fun p ↦ originalScreeningCompleteCostBudget S w Q b (fun i ↦ K i R) R (ell R)
        s t weight hj rho grid r cuts ε C Ltilt RS RT RCs RCt RDs RDt τ p) =
        fun p ↦ regular R p+3*C*reserve R p := by
      funext p
      dsimp [originalScreeningCompleteCostBudget,regular,reserve,core,lower,repair]
      ring
    rw [hpoint]
    exact (integral_add (hregularI R hR) ((hreserve R (by linarith)).1.const_mul (3*C))).trans
      (congrArg (fun z : ℝ ↦ (∫ p, regular R p ∂Law R)+z) (integral_const_mul (3*C) _))
  change (∫ p, originalScreeningCompleteCostBudget S w Q b (fun i ↦ K i R) R (ell R)
    s t weight hj rho grid r cuts ε C Ltilt RS RT RCs RCt RDs RDt τ p ∂Law R)/V R ≤ _
  rw [heq,add_div,mul_div_assoc]
  have hrsv := mul_le_mul_of_nonneg_left (hreserve R (by linarith)).2 (show 0 ≤ 3*C by positivity)
  have hrsv' : 3*C*((∫ p, reserve R p ∂Law R)/V R) ≤
      (6*C*(Fintype.card H : ℝ)*(q:ℝ)*dyadicMatchingConstant q)*rho^(1-2/(q:ℝ)) := by
    exact hrsv.trans_eq (by ring)
  nlinarith [hrsv']

end OTSelector.Reconstruction
