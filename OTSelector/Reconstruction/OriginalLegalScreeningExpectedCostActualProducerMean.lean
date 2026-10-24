import OTSelector.Reconstruction.OriginalLegalScreeningExpectedCostWorkingScalarMean
import OTSelector.Reconstruction.OriginalLegalScreeningExpectedCostPhysicalQuadraticReadout

/-! Actual finite FULL means from original-label screening and the genuine analytic budgets. -/
open Set Function Filter MeasureTheory ProbabilityTheory Module Manifold TopologicalSpace
open scoped ENNReal NNReal Topology ContDiff BigOperators InnerProductSpace
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Geometry ContinuousFinslerNorm OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {S : CalibratedLevelSeedPatch F u} {w : S.covector.ker} {μ ν : Measure ℝ}

/-- The genuine original-label signed maximum producer and one common physical
frame give the literal FULL optimum's integrability and expected-cost bound.
Every stage, port, cross-block, cut and bad-count error is eliminated by the
actual original-law estimates. The reserve constant is explicit and independent
of the matching, tilt and reserve intensity. -/
theorem OriginalSeedConditionalMoments.original_screening_actualProducer_fullValue_mean
    (D : OriginalSeedConditionalMoments S w μ ν)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels) (hq : 4 < finrank ℝ S.covector.ker)
    {densityμ densityν : M → ℝ} {v : M → E → ℝ} (cμ cν : ℝ≥0∞)
    (hρμ : Continuous densityμ) (hρμ0 : ∀ x, 0 ≤ densityμ x)
    (hρν : Continuous densityν) (hρν0 : ∀ x, 0 ≤ densityν x)
    (hv : ∀ old, ContinuousOn (v old) (extChartAt 𝓘(ℝ,E) old).target)
    (hv0 : ∀ old, ∀ y ∈ (extChartAt 𝓘(ℝ,E) old).target, 0 ≤ v old y)
    (hdensityμ : PopulationSeedClockDensity S w (μ.map (fun x : ℝ ↦ x-S.level)) densityμ v cμ.toReal)
    (hdensityν : PopulationSeedClockDensity S w (ν.map (fun x : ℝ ↦ x-S.level)) densityν v cν.toReal)
    {gap diameter : ℝ} (hbounds : ConditionalClockSupportBounds μ ν gap diameter) (hgap : 0 < gap)
    {g : ℝ → ℝ → ℝ} {Gbound : ℝ} (hg : Measurable (Function.uncurry g)) (hgb : ∀ x y, |g x y| ≤ Gbound)
    (tilt : ℝ)
    (Q : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν (D.originalFocalKinetic gap) g)
    (hmin : ∀ Q' : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν
      (D.originalFocalKinetic gap) g, Q.value tilt ≤ Q'.value tilt)
    (G : OriginalStageClockGrid) (h₀ : G.clockSlabSurplus μ ν 0 = 0) (hN : G.clockSlabSurplus μ ν G.count = 0)
    (hlo : G.cut 0 = D.lo+(S.level : ℝ)) (hhi : G.cut G.count = D.hi+(S.level : ℝ))
    (hwidth : ∀ k : Fin G.count, G.cut (k+1)-G.cut k < gap)
    (hmono : ∀ i, μ (G.sourceCell i) = 0 ∨ ν (G.targetCell i) = 0)
    (hH : ∀ k ≤ G.count, 0 ≤ G.clockSlabSurplus μ ν k)
    (b : OrthonormalBasis (Fin (finrank ℝ S.covector.ker)) ℝ
      (EuclideanSpace ℝ (Fin (finrank ℝ S.covector.ker))))
    (hj : ∀ i : Fin G.count, ∀ k, MemLp (fun scene ↦ originalSeedPathClockSetCurrent S w
      (originalEuclideanMollifier _) (Ioc (G.cut i.val) (G.cut (i.val+1))) scene k) 2 (Q.law : Measure _))
    (hproj : ∀ a i, (translationFixedSubspace Q.sceneEuclideanKoopman (ℝ ∙ b i)ᗮ).starProjection
      (originalLinearCurrentReadoutLtwo (Q.law : Measure _)
        (originalSeedPathClockSetCurrent S w (originalEuclideanMollifier _)
          (Ioc (G.cut a.val) (G.cut (a.val+1)))) (hj a) (originalEuclideanNormalReadout (b i))) = 0)
    (hcj : ∀ a : Fin (G.count+1), ∀ k, MemLp (fun scene ↦ originalSeedPathClockSetCurrent S w
      (originalEuclideanMollifier _) (Ioc (D.lo+(S.level : ℝ)) (G.cut a.val)) scene k) 2 (Q.law : Measure _))
    (hcproj : ∀ a i, (translationFixedSubspace Q.sceneEuclideanKoopman (ℝ ∙ b i)ᗮ).starProjection
      (originalLinearCurrentReadoutLtwo (Q.law : Measure _)
        (originalSeedPathClockSetCurrent S w (originalEuclideanMollifier _)
          (Ioc (D.lo+(S.level : ℝ)) (G.cut a.val))) (hcj a) (originalEuclideanNormalReadout (b i))) = 0)
    {rawRate C : ℝ} (hrate : 0 < rawRate) (hC : 0 ≤ C)
    (hkb : ∀ a d x, |D.originalFocalKinetic gap a d x| ≤ C*∑ i, x i^2)
    (hproducer : OriginalActualClockBlockSignedMaximumProducer Q G h₀ hN b rawRate C (|tilt| * Gbound) tilt hj)
    {ell : ℝ → ℝ} (hlarge : Tendsto ell atTop atTop) (hsmall : Tendsto (fun R ↦ ell R/R) atTop (𝓝 0)) :
    let V := fun R ↦ volume.real (originalCenteredPhysicalCubeRegion b (2*R))
    let FullLaw := fun R ↦ twoMarkedCloudLaw (finrank ℝ S.covector.ker) ℝ ℝ μ ν
      (Real.toNNReal (1+rawRate)*(volume (originalCenteredPhysicalCubeRegion b (2*R))).toNNReal)
    (∀ R, 0 ≤ R → Integrable (originalScreeningFullValue b R (D.originalFocalKinetic gap) g tilt) (FullLaw R)) ∧
    ∀ ε > 0, ∀ᶠ R : ℝ in atTop,
      (∫ cloud, originalScreeningFullValue b R (D.originalFocalKinetic gap) g tilt cloud ∂FullLaw R)/V R ≤
        Q.value tilt+(12*C*(G.count : ℝ)*(finrank ℝ S.covector.ker : ℝ)*
          dyadicMatchingConstant (finrank ℝ S.covector.ker))*rawRate^(1-2/(finrank ℝ S.covector.ker : ℝ))+
          2*|tilt| * Gbound*rawRate+ε := by
  obtain ⟨e,he,floor,hfloor,hgen⟩ := hproducer
  let K (R : ℝ) : Fin G.count → Compacts (Fin (finrank ℝ S.covector.ker) → ℝ) :=
    if h : 1 ≤ ell R ∧ 2*(originalStageFrameCollarFactor b*ell R) ≤ R then
      (hgen R (ell R) h.1 h.2).choose else fun _ ↦ ⊥
  have hmatching (R : ℝ) (h1 : 1 ≤ ell R) (h2 : 2*(originalStageFrameCollarFactor b*ell R) ≤ R) :
      ∀ᵐ p ∂originalMainReserveExperimentLaw Q (Real.toNNReal rawRate*
        (volume (originalCenteredPhysicalCubeRegion b (2*R))).toNNReal),
        OriginalClockBlockGoodCounts S w G μ ν b R rawRate e p →
          OriginalActualClockBlockSignedMaximum Q G h₀ hN b (K R) R (ell R) floor C (|tilt| * Gbound) tilt hj p := by
    dsimp only [K]
    rw [dite_eq_left ⟨h1,h2⟩]
    exact (hgen R (ell R) h1 h2).choose_spec.2
  let Hs := G.sourceReserveFineBlockPartition h₀ hN
  let Ht := G.targetReserveFineBlockPartition h₀ hN
  let RS := Sum.elim (fun i ↦ Hs.blockCell (Hs.blockFor i)) (fun i ↦ Ht.blockCell (Ht.blockFor i))
  let RT := Sum.elim (fun i ↦ Hs.oppositeCell (Hs.blockFor i)) (fun i ↦ Ht.oppositeCell (Ht.blockFor i))
  let RCs := Sum.elim (fun i ↦ Hs.deletionCell (Hs.blockFor i)) (fun _ : Fin G.count ↦ (∅ : Set ℝ))
  let RCt := Sum.elim (fun _ : Fin G.count ↦ (∅ : Set ℝ)) (fun i ↦ Ht.deletionCell (Ht.blockFor i))
  let RDs := Sum.elim Hs.fineCell (fun _ : Fin G.count ↦ (∅ : Set ℝ))
  let RDt := Sum.elim (fun _ : Fin G.count ↦ (∅ : Set ℝ)) Ht.fineCell
  have hRS (i) : MeasurableSet (RS i) := by
    cases i with
    | inl i => exact Hs.measurable_block _
    | inr i => exact Ht.measurable_block _
  have hRT (i) : MeasurableSet (RT i) := by
    cases i with
    | inl i => exact Hs.measurable_opposite _
    | inr i => exact Ht.measurable_opposite _
  have hRCs (i) : MeasurableSet (RCs i) := by
    cases i with
    | inl i => exact Hs.measurable_deletion _
    | inr i => exact MeasurableSet.empty
  have hRCt (i) : MeasurableSet (RCt i) := by
    cases i with
    | inl i => exact MeasurableSet.empty
    | inr i => exact Ht.measurable_deletion _
  have hRDs (i) : MeasurableSet (RDs i) := by
    cases i with
    | inl i => exact Hs.measurable_fine _
    | inr i => exact MeasurableSet.empty
  have hRDt (i) : MeasurableSet (RDt i) := by
    cases i with
    | inl i => exact MeasurableSet.empty
    | inr i => exact Ht.measurable_fine _
  have hcuts (a : Fin (G.count+1)) : D.lo+(S.level : ℝ) ≤ G.cut a.val := by
    rw [← hlo]
    exact G.strictMono.monotone (Nat.zero_le _)
  have hell : ∀ᶠ R in atTop, 0 ≤ ell R := hlarge.eventually_ge_atTop 0
  have hb := D.original_screening_completeCostBudget_expected_bound hF hw hq cμ cν
    hρμ hρμ0 hρν hρν0 hv hv0 hdensityμ hdensityν hbounds hgap hg hgb tilt Q hmin b
    (fun i : Fin G.count ↦ G.cut i.val) (fun i ↦ G.cut (i.val+1))
    (originalScreeningBlockStageWeight G h₀ hN floor C) (fun i R ↦ K R i) hj hproj hrate G he hmono hH
    (fun a : Fin (G.count+1) ↦ G.cut a.val) (fun _ ↦ e) hcuts (fun _ ↦ he) hcj hcproj
    RS RT RCs RCt RDs RDt hRS hRT hRCs hRCt hRDs hRDt C (|tilt| * Gbound) hC hell hlarge hsmall
  have hk := D.measurable_originalFocalKinetic hF hw gap
  refine ⟨fun R hR ↦ (originalScreeningFullValue_integrable_and_ae_bound μ ν b hR _ hC hk hkb hg hgb tilt).1,?_⟩
  intro ε hε
  filter_upwards [hb.2 ε hε,eventually_ge_atTop (1 : ℝ),hlarge.eventually_ge_atTop 1,
    eventually_collar_mul_le_radius (k := 2*originalStageFrameCollarFactor b) hsmall] with R hbR hR hellR hcollar
  have hcollar' : 2*(originalStageFrameCollarFactor b*ell R) ≤ R := by nlinarith only [hcollar]
  obtain ⟨X⟩ := D.exists_originalReserve_fullWorkingInputExperiment Q Q b (R := R) (by omega) hrate (by linarith)
  have hm := D.integral_original_screening_fullValue_le_actualGridBudget Q Q G h₀ hN b (K R) hj hF hw
    (by omega) (by linarith) (by linarith) hcollar' hC hfloor.le hk
    (D.originalFocalKinetic_nonneg hF hw hgap) hkb hg hgb hlo hhi hbounds hwidth X
    (hmatching R hellR hcollar') (hb.1 R hR)
  have hdiv := div_le_div_of_nonneg_right hm (ENNReal.toReal_nonneg : 0 ≤
    (volume (originalCenteredPhysicalCubeRegion b (2*R))).toReal)
  have hcard : (Fintype.card (Fin G.count ⊕ Fin G.count) : ℝ) = 2*(G.count : ℝ) := by simp; ring
  have hbR' : (∫ p, originalScreeningClockGridCompleteCostBudget Q G h₀ hN b (K R) R (ell R)
      rawRate floor C (|tilt| * Gbound) tilt e (fun k : Fin (G.count+1) ↦ G.cut k.val) (fun _ ↦ e) hj p
      ∂originalMainReserveExperimentLaw Q (Real.toNNReal rawRate*
        (volume (originalCenteredPhysicalCubeRegion b (2*R))).toNNReal)) /
      volume.real (originalCenteredPhysicalCubeRegion b (2*R)) ≤
      Q.value tilt+(12*C*(G.count : ℝ)*(finrank ℝ S.covector.ker : ℝ)*
          dyadicMatchingConstant (finrank ℝ S.covector.ker))*rawRate^(1-2/(finrank ℝ S.covector.ker : ℝ))+
          2*|tilt| * Gbound*rawRate+ε := by
    have heq : Q.value tilt+(6*C*(Fintype.card (Fin G.count ⊕ Fin G.count) : ℝ)*
        (finrank ℝ S.covector.ker : ℝ)*dyadicMatchingConstant (finrank ℝ S.covector.ker))*
        rawRate^(1-2/(finrank ℝ S.covector.ker : ℝ))+2*(|tilt| * Gbound)*rawRate+ε =
        Q.value tilt+(12*C*(G.count : ℝ)*(finrank ℝ S.covector.ker : ℝ)*
          dyadicMatchingConstant (finrank ℝ S.covector.ker))*rawRate^(1-2/(finrank ℝ S.covector.ker : ℝ))+
          2*|tilt| * Gbound*rawRate+ε := by rw [hcard]; ring
    exact hbR.trans_eq heq
  exact hdiv.trans hbR'

end OTSelector.Reconstruction
