import OTSelector.Reconstruction.OriginalMarkSelectedPopulationCouplingBlockExcessBudget
import OTSelector.Reconstruction.OriginalScreeningBoundaryBudgetActualCountLimit

/-! The actual finite collection of full-input block excesses has vanishing
quadratically weighted cost per same-frame volume in dimensions above four. -/

open Set Function MeasureTheory ProbabilityTheory Filter Topology
open scoped BigOperators ENNReal NNReal
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
variable {q : ℕ} {α β : Measure ℝ}

/-- Sum the actual full main-plus-reserve imbalance over every true Hall block,
including empty and zero-mass blocks. -/
def originalFullClockSlabDiscrepancy (G : OriginalStageClockGrid) (K : Set (Fin q → ℝ))
    (p : LegalMarkedOptimalInputScene q × TwoMarkedCloudSpace q ℝ ℝ) : ℝ :=
  ∑ b : G.ClockSlabBlock α β,
    originalFullBlockDiscrepancy K (G.sourceBlockCell α β b) (G.targetBlockCell α β b) p

/-- A fixed finite coefficient from the actual block masses and nonnegative
reserve intensity ratio. It is independent of the physical cube radius. -/
def originalClockSlabDiscrepancyConstant (G : OriginalStageClockGrid) (α β : Measure ℝ)
    (θ : ℝ≥0) : ℝ :=
  ∑ b : G.ClockSlabBlock α β,
    (Real.sqrt (2 * α.real (G.sourceBlockCell α β b)) +
      Real.sqrt (2 * (θ : ℝ) * α.real (G.sourceBlockCell α β b)))

variable [IsProbabilityMeasure α] [IsProbabilityMeasure β]
  {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}

/-- The same complete experiment has a square-root-volume total block budget.
Both original main and both reserve colors occur inside this observable. -/
theorem LegalWeightedStationaryPoissonMatching.originalFullClockSlabDiscrepancy_integrable_and_integral_le
    (Q : LegalWeightedStationaryPoissonMatching q α β kin g)
    (frame : OrthonormalBasis (Fin q) ℝ (EuclideanSpace ℝ (Fin q)))
    (R : ℝ) (θ : ℝ≥0) (G : OriginalStageClockGrid) :
    let K := originalCenteredPhysicalCubeRegion frame (2 * R)
    let rate := θ * (volume K).toNNReal
    Integrable (originalFullClockSlabDiscrepancy (α := α) (β := β) G K)
      (originalMainReserveExperimentLaw Q rate) ∧
    (∫ p, originalFullClockSlabDiscrepancy (α := α) (β := β) G K p
      ∂originalMainReserveExperimentLaw Q rate) ≤
        originalClockSlabDiscrepancyConstant G α β θ * Real.sqrt (volume.real K) := by
  let K := originalCenteredPhysicalCubeRegion frame (2 * R)
  let rate := θ * (volume K).toNNReal
  have hb (b : G.ClockSlabBlock α β) := Q.originalFullBlockDiscrepancy_integrable_and_integral_le
    rate (isCompact_originalStagePhysicalCube frame (2 * R))
    (G.blockCells_measurable b).1 (G.blockCells_measurable b).2
    ((ENNReal.toReal_eq_toReal_iff' (measure_ne_top α _) (measure_ne_top β _)).mp
      (G.block_mass_balance b))
  refine ⟨integrable_finsetSum _ (fun b _ ↦ (hb b).1), ?_⟩
  change (∫ p, ∑ b : G.ClockSlabBlock α β,
    originalFullBlockDiscrepancy K (G.sourceBlockCell α β b) (G.targetBlockCell α β b) p
      ∂originalMainReserveExperimentLaw Q rate) ≤ _
  rw [integral_finsetSum _ (fun b _ ↦ (hb b).1)]
  calc
    _ ≤ ∑ b : G.ClockSlabBlock α β,
        (Real.sqrt (2 * volume.real K * α.real (G.sourceBlockCell α β b)) +
          Real.sqrt (2 * (rate : ℝ) * α.real (G.sourceBlockCell α β b))) :=
      Finset.sum_le_sum fun b _ ↦ (hb b).2
    _ = originalClockSlabDiscrepancyConstant G α β θ * Real.sqrt (volume.real K) := by
      rw [originalClockSlabDiscrepancyConstant, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro b _
      have hrate : (rate : ℝ) = (θ : ℝ) * volume.real K := by
        simp only [rate, NNReal.coe_mul, ENNReal.coe_toNNReal_eq_toReal, measureReal_def]
      rw [hrate, show 2 * volume.real K * α.real (G.sourceBlockCell α β b) =
        (2 * α.real (G.sourceBlockCell α β b)) * volume.real K by ring,
        show 2 * ((θ : ℝ) * volume.real K) * α.real (G.sourceBlockCell α β b) =
          (2 * (θ : ℝ) * α.real (G.sourceBlockCell α β b)) * volume.real K by ring,
        Real.sqrt_mul (by positivity : 0 ≤ 2 * α.real (G.sourceBlockCell α β b)),
        Real.sqrt_mul (by positivity : 0 ≤ 2 * (θ : ℝ) * α.real (G.sourceBlockCell α β b)), add_mul]

/-- The real full-block leftover budget pays its coarse physical R² cost:
its expectation divided by the true same-frame cube volume tends to zero. -/
theorem LegalWeightedStationaryPoissonMatching.tendsto_originalFullClockSlabDiscrepancy_quadratic_cost_zero
    (Q : LegalWeightedStationaryPoissonMatching q α β kin g) (hq : 4 < q)
    (frame : OrthonormalBasis (Fin q) ℝ (EuclideanSpace ℝ (Fin q)))
    (θ : ℝ≥0) (G : OriginalStageClockGrid) :
    Tendsto (fun R : ℝ ↦
      let K := originalCenteredPhysicalCubeRegion frame (2 * R)
      R^2 * (∫ p, originalFullClockSlabDiscrepancy (α := α) (β := β) G K p
        ∂originalMainReserveExperimentLaw Q (θ * (volume K).toNNReal)) / volume.real K)
      atTop (𝓝 0) := by
  let C := originalClockSlabDiscrepancyConstant G α β θ
  have hlimit := (tendsto_originalScreeningPhysicalCube_quadratic_sqrt_volume_zero hq frame).const_mul C
  simp only [mul_zero] at hlimit
  apply squeeze_zero' (Eventually.of_forall fun R ↦
    div_nonneg (mul_nonneg (sq_nonneg R)
      (integral_nonneg fun p ↦ Finset.sum_nonneg fun b _ ↦ abs_nonneg _)) measureReal_nonneg) ?_ hlimit
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR
  let K := originalCenteredPhysicalCubeRegion frame (2 * R)
  let V := volume.real K
  have hV : V = (2 * R)^q := by
    change (volume (originalCenteredPhysicalCubeRegion frame (2 * R))).toReal = _
    rw [volume_originalOrientedTraffic_cube]
    change volume.real (haarRootCube (Fin q) R) = _
    rw [volume_real_haarRootCube (Fin q) hR.le, Fintype.card_fin]
  have hVpos : 0 < V := by rw [hV]; positivity
  have hspos := Real.sqrt_pos.mpr hVpos
  have hs := Real.sq_sqrt hVpos.le
  have hb := (Q.originalFullClockSlabDiscrepancy_integrable_and_integral_le frame R θ G).2
  calc
    _ ≤ R^2 * (C * Real.sqrt V) / V :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hb (sq_nonneg R)) hVpos.le
    _ = C * (R^2 / Real.sqrt V) := by
      field_simp [hVpos.ne', hspos.ne']
      nlinarith [congrArg (fun t : ℝ ↦ C * t) hs]

end OTSelector.Reconstruction
