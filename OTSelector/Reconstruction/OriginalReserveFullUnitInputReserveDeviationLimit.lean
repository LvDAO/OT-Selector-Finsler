import OTSelector.Reconstruction.OriginalReserveFullUnitInputReserveCapacity
import OTSelector.Reconstruction.OriginalReserveFullUnitInputBlockDeviationLimit

/-! All actual fixed reserve-class fluctuations are negligible at the physical quadratic scale. -/
open Set Function MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators Classical
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

/-- The true reserve fluctuation bound has vanishing physical quadratic weight,
for every fixed class, including null classes. -/
theorem tendsto_originalReserveClassDeviation_bound_quadratic_zero {q : ℕ}
    (hq : 4 < q) (b : OrthonormalBasis (Fin q) ℝ (EuclideanSpace ℝ (Fin q)))
    {θ r : ℝ} (hθ : 0 ≤ θ) (γ : Measure ℝ) (C : Set ℝ) :
    Tendsto (fun R : ℝ ↦
      let V := volume.real (originalCenteredPhysicalCubeRegion b (2 * R))
      R^2 * (Real.sqrt (θ * V * γ.real C) / (r * V))) atTop (𝓝 0) := by
  have h := tendsto_originalUnitBlockDiscrepancy_bound_quadratic_zero hq b
    (r := r) (w := θ * γ.real C / 2) (div_nonneg (mul_nonneg hθ measureReal_nonneg) (by norm_num))
  convert h using 1
  funext R
  dsimp only
  rw [show 2 * volume.real (originalCenteredPhysicalCubeRegion b (2 * R)) * (θ * γ.real C / 2) =
    θ * volume.real (originalCenteredPhysicalCubeRegion b (2 * R)) * γ.real C by ring]

namespace OriginalReserveFullUnitInputExperiment
variable {q : ℕ} {α β : Measure ℝ} [IsProbabilityMeasure α] [IsProbabilityMeasure β]
  {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
  {Main Reserve : LegalWeightedStationaryPoissonMatching q α β kin g}
  {b : OrthonormalBasis (Fin q) ℝ (EuclideanSpace ℝ (Fin q))}
  {θ : ℝ} {hθ : 0 < θ} {hθ1 : θ < 1}

/-- The actual source reserve-class fluctuation event is quadratically
negligible on the same full original joining, without any class positivity premise. -/
theorem tendsto_sourceReserveBlockCount_deviation_probability (hq : 4 < q)
    (X : ∀ R : ℝ, 0 < R → OriginalReserveFullUnitInputExperiment Main Reserve b θ hθ hθ1 R)
    {C : Set ℝ} (hC : MeasurableSet C) {r : ℝ} (hr : 0 < r) :
    Tendsto (fun R : ℝ ↦ if hR : 0 < R then
      let V := volume.real (originalCenteredPhysicalCubeRegion b (2 * R))
      R^2 * ((X R hR).fullLaw : Measure (OriginalReserveUnitExperimentSpace q × TwoMarkedCloudSpace q ℝ ℝ)).real
        {p | r * V < |(originalReserveBlockCount p.1.2.2.1.1 (fun i ↦ (p.1.2.2.1.2 i).2) C : ℝ) -
          θ * V * α.real C|}
      else 0) atTop (𝓝 0) := by
  apply squeeze_zero' (Eventually.of_forall fun R ↦ by split_ifs <;> positivity) ?_
    (tendsto_originalReserveClassDeviation_bound_quadratic_zero hq b (r := r) hθ.le α C)
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR
  simp only [dite_eq_left hR]
  have hV : 0 < volume.real (originalCenteredPhysicalCubeRegion b (2 * R)) := by
    change 0 < (volume (originalCenteredPhysicalCubeRegion b (2 * R))).toReal
    rw [volume_originalOrientedTraffic_cube b R]
    change 0 < volume.real (haarRootCube (Fin q) R)
    rw [volume_real_haarRootCube (Fin q) hR.le, Fintype.card_fin]
    positivity
  have hb := (X R hR).sourceReserveBlockCount_deviation_probability hC (mul_pos hr hV)
  have hb' :
      ((X R hR).fullLaw : Measure (OriginalReserveUnitExperimentSpace q × TwoMarkedCloudSpace q ℝ ℝ)).real
        {p | r * volume.real (originalCenteredPhysicalCubeRegion b (2 * R)) <
          |(originalReserveBlockCount p.1.2.2.1.1 (fun i ↦ (p.1.2.2.1.2 i).2) C : ℝ) -
            θ * volume.real (originalCenteredPhysicalCubeRegion b (2 * R)) * α.real C|} ≤
      Real.sqrt (θ * volume.real (originalCenteredPhysicalCubeRegion b (2 * R)) * α.real C) /
        (r * volume.real (originalCenteredPhysicalCubeRegion b (2 * R))) := by
    simpa only [NNReal.coe_mul, ENNReal.coe_toNNReal_eq_toReal,
      Real.coe_toNNReal _ hθ.le, measureReal_def] using hb
  exact mul_le_mul_of_nonneg_left hb' (sq_nonneg R)

/-- The actual target reserve-class fluctuation event is quadratically
negligible on the same full original joining, without any class positivity premise. -/
theorem tendsto_targetReserveBlockCount_deviation_probability (hq : 4 < q)
    (X : ∀ R : ℝ, 0 < R → OriginalReserveFullUnitInputExperiment Main Reserve b θ hθ hθ1 R)
    {C : Set ℝ} (hC : MeasurableSet C) {r : ℝ} (hr : 0 < r) :
    Tendsto (fun R : ℝ ↦ if hR : 0 < R then
      let V := volume.real (originalCenteredPhysicalCubeRegion b (2 * R))
      R^2 * ((X R hR).fullLaw : Measure (OriginalReserveUnitExperimentSpace q × TwoMarkedCloudSpace q ℝ ℝ)).real
        {p | r * V < |(originalReserveBlockCount p.1.2.2.2.1 (fun i ↦ (p.1.2.2.2.2 i).2) C : ℝ) -
          θ * V * β.real C|}
      else 0) atTop (𝓝 0) := by
  apply squeeze_zero' (Eventually.of_forall fun R ↦ by split_ifs <;> positivity) ?_
    (tendsto_originalReserveClassDeviation_bound_quadratic_zero hq b (r := r) hθ.le β C)
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR
  simp only [dite_eq_left hR]
  have hV : 0 < volume.real (originalCenteredPhysicalCubeRegion b (2 * R)) := by
    change 0 < (volume (originalCenteredPhysicalCubeRegion b (2 * R))).toReal
    rw [volume_originalOrientedTraffic_cube b R]
    change 0 < volume.real (haarRootCube (Fin q) R)
    rw [volume_real_haarRootCube (Fin q) hR.le, Fintype.card_fin]
    positivity
  have hb := (X R hR).targetReserveBlockCount_deviation_probability hC (mul_pos hr hV)
  have hb' :
      ((X R hR).fullLaw : Measure (OriginalReserveUnitExperimentSpace q × TwoMarkedCloudSpace q ℝ ℝ)).real
        {p | r * volume.real (originalCenteredPhysicalCubeRegion b (2 * R)) <
          |(originalReserveBlockCount p.1.2.2.2.1 (fun i ↦ (p.1.2.2.2.2 i).2) C : ℝ) -
            θ * volume.real (originalCenteredPhysicalCubeRegion b (2 * R)) * β.real C|} ≤
      Real.sqrt (θ * volume.real (originalCenteredPhysicalCubeRegion b (2 * R)) * β.real C) /
        (r * volume.real (originalCenteredPhysicalCubeRegion b (2 * R))) := by
    simpa only [NNReal.coe_mul, ENNReal.coe_toNNReal_eq_toReal,
      Real.coe_toNNReal _ hθ.le, measureReal_def] using hb
  exact mul_le_mul_of_nonneg_left hb' (sq_nonneg R)

end OriginalReserveFullUnitInputExperiment
end OTSelector.Reconstruction
