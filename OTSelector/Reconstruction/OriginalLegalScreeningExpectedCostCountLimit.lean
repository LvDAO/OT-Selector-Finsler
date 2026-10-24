import OTSelector.Reconstruction.OriginalLegalScreeningExpectedCostCount

/-! Arbitrary joint bad events have vanishing actual main-plus-reserve quadratic cost. -/
open Set Function MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
variable {q : ℕ} {α β : Measure ℝ} [IsProbabilityMeasure α] [IsProbabilityMeasure β]
  {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}

/-- The actual full count on the same original main/raw-reserve product pays
any jointly measurable event with negligible quadratic probability. No independence
between the selected event, main input count or reserve counts is assumed. -/
theorem LegalWeightedStationaryPoissonMatching.tendsto_original_screening_fullExperimentCount_bad_cost_zero
    (Q : LegalWeightedStationaryPoissonMatching q α β kin g) (hq : 4 < q)
    (b : OrthonormalBasis (Fin q) ℝ (EuclideanSpace ℝ (Fin q)))
    {rho : ℝ} (hrho : 0 ≤ rho)
    (bad : ℝ → Set (LegalMarkedOptimalInputScene q × TwoMarkedCloudSpace q ℝ ℝ))
    (hbad : ∀ R, MeasurableSet (bad R))
    (hprob : Tendsto (fun R : ℝ ↦ R^2 *
      (originalMainReserveExperimentLaw Q (Real.toNNReal rho *
        (volume (originalCenteredPhysicalCubeRegion b (2*R))).toNNReal)).real (bad R))
      atTop (𝓝 0)) :
    Tendsto (fun R : ℝ ↦ R^2 *
      ((∫ p, (bad R).indicator
        (originalScreeningFullExperimentCount (originalCenteredPhysicalCubeRegion b (2*R))) p
        ∂originalMainReserveExperimentLaw Q (Real.toNNReal rho *
          (volume (originalCenteredPhysicalCubeRegion b (2*R))).toNNReal)) /
          volume.real (originalCenteredPhysicalCubeRegion b (2*R)))) atTop (𝓝 0) := by
  have hup := (hprob.const_mul (2*(1+rho))).add
    ((tendsto_originalScreeningPhysicalCube_quadratic_sqrt_volume_zero hq b).const_mul
      (2*(1+Real.sqrt rho)))
  simp only [mul_zero,add_zero] at hup
  apply squeeze_zero' (Eventually.of_forall (fun R ↦ mul_nonneg (sq_nonneg R)
    (div_nonneg (integral_nonneg fun p ↦ indicator_nonneg
      (fun p _ ↦ originalScreeningFullExperimentCount_nonneg _ p) p) measureReal_nonneg))) ?_ hup
  filter_upwards [eventually_gt_atTop (0:ℝ)] with R hR
  let K := originalCenteredPhysicalCubeRegion b (2*R)
  let V := volume.real K
  let rate := Real.toNNReal rho * (volume K).toNNReal
  let M := originalMainReserveExperimentLaw Q rate
  have hVpos : 0 < V := by
    change 0 < (volume (originalCenteredPhysicalCubeRegion b (2*R))).toReal
    rw [volume_originalOrientedTraffic_cube]
    change 0 < volume.real (haarRootCube (Fin q) R)
    rw [volume_real_haarRootCube (Fin q) hR.le,Fintype.card_fin]
    positivity
  have hrate : (rate : ℝ) = rho*V := by
    simp only [rate,NNReal.coe_mul,Real.coe_toNNReal _ hrho,
      ENNReal.coe_toNNReal_eq_toReal,V,measureReal_def]
  have hfinite : volume K ≠ (∞ : ℝ≥0∞) := by
    rw [volume_originalOrientedTraffic_cube]
    exact isCompact_Icc.measure_ne_top
  have hb := (Q.original_screening_fullExperimentCount rate
    (measurableSet_originalOrientedTraffic_cube b R) hfinite).2.2 (bad R) (hbad R)
  calc
    _ ≤ R^2 * (((2*V+2*(rate : ℝ))*M.real (bad R)+2*Real.sqrt V+
        2*Real.sqrt (rate : ℝ))/V) :=
      mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hb hVpos.le) (sq_nonneg R)
    _ = (2*(1+rho))*(R^2*M.real (bad R)) +
        (2*(1+Real.sqrt rho))*R^2*(Real.sqrt V/V) := by
      rw [hrate,Real.sqrt_mul hrho]
      field_simp [hVpos.ne']
      ring
    _ = (2*(1+rho))*(R^2*M.real (bad R)) +
        (2*(1+Real.sqrt rho))*(R^2/Real.sqrt V) := by
      rw [Real.sqrt_div_self']
      ring

end OTSelector.Reconstruction
