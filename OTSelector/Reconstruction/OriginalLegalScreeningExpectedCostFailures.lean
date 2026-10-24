import OTSelector.Reconstruction.OriginalLegalScreeningExpectedCostCountLimit
import OTSelector.Reconstruction.OriginalReserveRawClockGridPrefixDeviation
import OTSelector.Reconstruction.OriginalMarkSelectedPopulationCouplingBlockExcessBudgetFailure

/-! Actual finite-grid raw reserve and complete block errors pay their full joint-input coarse cost. -/
open Set Function MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
variable {q : ℕ} {α β : Measure ℝ} [IsProbabilityMeasure α] [IsProbabilityMeasure β]
  {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}

/-- One actual event includes both the unchanged raw finite-grid reserve
prefix errors and the total full-input block excess budget exceeding its threshold. -/
def originalScreeningReserveBlockFailure (α β : Measure ℝ)
    (b : OrthonormalBasis (Fin q) ℝ (EuclideanSpace ℝ (Fin q)))
    (rho R : ℝ) (G : OriginalStageClockGrid) (r : ℝ) :
    Set (LegalMarkedOptimalInputScene q × TwoMarkedCloudSpace q ℝ ℝ) :=
  {p | p.2 ∈ originalReserveRawClockGridPrefixDeviationFailure α β b rho R G r} ∪
    {p | r*volume.real (originalCenteredPhysicalCubeRegion b (2*R)) <
      originalFullClockSlabDiscrepancy (α := α) (β := β) G
        (originalCenteredPhysicalCubeRegion b (2*R)) p}

omit [IsProbabilityMeasure α] [IsProbabilityMeasure β] in
/-- The actual joint failure is measurable before inspecting the original reserve positions. -/
theorem measurableSet_originalScreeningReserveBlockFailure
    (b : OrthonormalBasis (Fin q) ℝ (EuclideanSpace ℝ (Fin q)))
    (rho R : ℝ) (G : OriginalStageClockGrid) (r : ℝ) :
    MeasurableSet (originalScreeningReserveBlockFailure α β b rho R G r) :=
  ((measurableSet_originalReserveRawClockGridPrefixDeviationFailure α β b rho R G r).preimage
    measurable_snd).union (measurableSet_lt measurable_const
      (measurable_originalFullClockSlabDiscrepancy G (measurableSet_originalOrientedTraffic_cube b R)))

/-- Both genuine original fluctuation producers supply a vanishing quadratic
failure probability on the unchanged unit-main/raw-reserve product law. -/
theorem LegalWeightedStationaryPoissonMatching.tendsto_original_screening_reserveBlockFailure_probability
    (Q : LegalWeightedStationaryPoissonMatching q α β kin g) (hq : 4 < q)
    (b : OrthonormalBasis (Fin q) ℝ (EuclideanSpace ℝ (Fin q)))
    {rho r : ℝ} (hrho : 0 < rho) (G : OriginalStageClockGrid) (hr : 0 < r) :
    Tendsto (fun R : ℝ ↦ R^2 *
      (originalMainReserveExperimentLaw Q (Real.toNNReal rho *
        (volume (originalCenteredPhysicalCubeRegion b (2*R))).toNNReal)).real
          (originalScreeningReserveBlockFailure α β b rho R G r)) atTop (𝓝 0) := by
  have hp := tendsto_originalReserveRawClockGridPrefixDeviationFailure_prod hq α β b hrho G hr
    (fun _ ↦ Q.law)
  have hb := Q.tendsto_originalFullClockSlabDiscrepancy_budgetFailure_quadratic_probability_zero
    hq b (Real.toNNReal rho) G hr
  have hu := hp.add hb
  simp only [add_zero] at hu
  apply squeeze_zero' (Eventually.of_forall (fun R ↦ mul_nonneg (sq_nonneg R) measureReal_nonneg)) ?_ hu
  exact Eventually.of_forall fun R ↦ by
    rw [← mul_add]
    exact mul_le_mul_of_nonneg_left (measureReal_union_le _ _) (sq_nonneg R)

/-- Actual counts of all original main and both raw reserve observations pay
this complete reserve/block exception, with no independent-count/event hypothesis
and no probability or expected-cost rate supplied as an input. -/
theorem LegalWeightedStationaryPoissonMatching.tendsto_original_screening_reserveBlockFailure_count_cost
    (Q : LegalWeightedStationaryPoissonMatching q α β kin g) (hq : 4 < q)
    (b : OrthonormalBasis (Fin q) ℝ (EuclideanSpace ℝ (Fin q)))
    {rho r : ℝ} (hrho : 0 < rho) (G : OriginalStageClockGrid) (hr : 0 < r) :
    Tendsto (fun R : ℝ ↦ R^2 *
      ((∫ p, (originalScreeningReserveBlockFailure α β b rho R G r).indicator
        (originalScreeningFullExperimentCount (originalCenteredPhysicalCubeRegion b (2*R))) p
        ∂originalMainReserveExperimentLaw Q (Real.toNNReal rho *
          (volume (originalCenteredPhysicalCubeRegion b (2*R))).toNNReal)) /
          volume.real (originalCenteredPhysicalCubeRegion b (2*R)))) atTop (𝓝 0) :=
  Q.tendsto_original_screening_fullExperimentCount_bad_cost_zero hq b hrho.le
    (fun R ↦ originalScreeningReserveBlockFailure α β b rho R G r)
    (fun R ↦ measurableSet_originalScreeningReserveBlockFailure b rho R G r)
    (Q.tendsto_original_screening_reserveBlockFailure_probability hq b hrho G hr)

end OTSelector.Reconstruction
