import OTSelector.Reconstruction.OriginalReserveRawClassDeviation
import OTSelector.Reconstruction.OriginalReserveClassCapacityLimit

/-! Every positive raw reserve class has a genuine half-mean capacity bound at any positive intensity. -/
open Set Function MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators Classical
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-- The actual original source reserve class count exceeds half its positive
mean outside a quadratically negligible event. Theta is any positive intensity. -/
theorem tendsto_originalRawSourceReserveNatBlockCount_lower {q : ℕ} (hq : 4 < q)
    (α β : Measure ℝ) [IsProbabilityMeasure α] [IsProbabilityMeasure β]
    (b : OrthonormalBasis (Fin q) ℝ (EuclideanSpace ℝ (Fin q)))
    {θ : ℝ} (hθ : 0 < θ) {C : Set ℝ} (hC : MeasurableSet C)
    (hCmass : 0 < α.real C) :
    Tendsto (fun R : ℝ ↦
      R^2 * (twoMarkedCloudLaw q ℝ ℝ α β
        (Real.toNNReal θ * (volume (originalCenteredPhysicalCubeRegion b (2 * R))).toNNReal)).real
        {cloud | (originalReserveBlockCount cloud.1.1
          (fun i ↦ (cloud.1.2 i).2) C : ℝ) <
            θ * volume.real (originalCenteredPhysicalCubeRegion b (2 * R)) * α.real C / 2})
      atTop (𝓝 0) := by
  apply squeeze_zero' (Eventually.of_forall fun R ↦
    mul_nonneg (sq_nonneg R) measureReal_nonneg) ?_
    (tendsto_originalReserveClassCount_lower_bound_quadratic_zero hq b hθ α C hCmass)
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR
  have hb := poissonCount_lower_probability_of_hasLaw _ _
    (measurable_originalReserveBlockCount (by fun_prop) (by fun_prop) hC) _
    (hasLaw_originalRawSourceReserveNatBlockCount (q := q) α β
      (Real.toNNReal θ * (volume (originalCenteredPhysicalCubeRegion b (2 * R))).toNNReal) hC)
    (originalReserveClassCountMean_pos b hθ hR α C hCmass)
  have hb' :
      (twoMarkedCloudLaw q ℝ ℝ α β
        (Real.toNNReal θ * (volume (originalCenteredPhysicalCubeRegion b (2 * R))).toNNReal)).real
        {cloud | (originalReserveBlockCount cloud.1.1
          (fun i ↦ (cloud.1.2 i).2) C : ℝ) <
            θ * volume.real (originalCenteredPhysicalCubeRegion b (2 * R)) * α.real C / 2} ≤
        Real.sqrt (θ * volume.real (originalCenteredPhysicalCubeRegion b (2 * R)) * α.real C) /
          (θ * volume.real (originalCenteredPhysicalCubeRegion b (2 * R)) * α.real C / 2) := by
    simpa only [NNReal.coe_mul, ENNReal.coe_toNNReal_eq_toReal,
      Real.coe_toNNReal _ hθ.le, measureReal_def] using hb
  simpa only [NNReal.coe_mul, ENNReal.coe_toNNReal_eq_toReal,
    Real.coe_toNNReal _ hθ.le, measureReal_def] using
      mul_le_mul_of_nonneg_left hb' (sq_nonneg R)

/-- The actual original target reserve class count exceeds half its positive
mean outside a quadratically negligible event. Theta is any positive intensity. -/
theorem tendsto_originalRawTargetReserveNatBlockCount_lower {q : ℕ} (hq : 4 < q)
    (α β : Measure ℝ) [IsProbabilityMeasure α] [IsProbabilityMeasure β]
    (b : OrthonormalBasis (Fin q) ℝ (EuclideanSpace ℝ (Fin q)))
    {θ : ℝ} (hθ : 0 < θ) {C : Set ℝ} (hC : MeasurableSet C)
    (hCmass : 0 < β.real C) :
    Tendsto (fun R : ℝ ↦
      R^2 * (twoMarkedCloudLaw q ℝ ℝ α β
        (Real.toNNReal θ * (volume (originalCenteredPhysicalCubeRegion b (2 * R))).toNNReal)).real
        {cloud | (originalReserveBlockCount cloud.2.1
          (fun i ↦ (cloud.2.2 i).2) C : ℝ) <
            θ * volume.real (originalCenteredPhysicalCubeRegion b (2 * R)) * β.real C / 2})
      atTop (𝓝 0) := by
  apply squeeze_zero' (Eventually.of_forall fun R ↦
    mul_nonneg (sq_nonneg R) measureReal_nonneg) ?_
    (tendsto_originalReserveClassCount_lower_bound_quadratic_zero hq b hθ β C hCmass)
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR
  have hb := poissonCount_lower_probability_of_hasLaw _ _
    (measurable_originalReserveBlockCount (by fun_prop) (by fun_prop) hC) _
    (hasLaw_originalRawTargetReserveNatBlockCount (q := q) α β
      (Real.toNNReal θ * (volume (originalCenteredPhysicalCubeRegion b (2 * R))).toNNReal) hC)
    (originalReserveClassCountMean_pos b hθ hR β C hCmass)
  have hb' :
      (twoMarkedCloudLaw q ℝ ℝ α β
        (Real.toNNReal θ * (volume (originalCenteredPhysicalCubeRegion b (2 * R))).toNNReal)).real
        {cloud | (originalReserveBlockCount cloud.2.1
          (fun i ↦ (cloud.2.2 i).2) C : ℝ) <
            θ * volume.real (originalCenteredPhysicalCubeRegion b (2 * R)) * β.real C / 2} ≤
        Real.sqrt (θ * volume.real (originalCenteredPhysicalCubeRegion b (2 * R)) * β.real C) /
          (θ * volume.real (originalCenteredPhysicalCubeRegion b (2 * R)) * β.real C / 2) := by
    simpa only [NNReal.coe_mul, ENNReal.coe_toNNReal_eq_toReal,
      Real.coe_toNNReal _ hθ.le, measureReal_def] using hb
  simpa only [NNReal.coe_mul, ENNReal.coe_toNNReal_eq_toReal,
    Real.coe_toNNReal _ hθ.le, measureReal_def] using
      mul_le_mul_of_nonneg_left hb' (sq_nonneg R)

end OTSelector.Reconstruction
