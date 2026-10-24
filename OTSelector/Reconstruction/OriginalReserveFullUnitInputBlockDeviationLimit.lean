import OTSelector.Reconstruction.OriginalReserveFullUnitInputBlockCounts
import OTSelector.Probability.RealMarkovBound
import OTSelector.Reconstruction.OriginalScreeningBoundaryBudgetActualCountLimit

/-! True unit-input block deviations have quadratically negligible failure probabilities. -/
open Set Function MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators Classical
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

/-- The actual unit-block Markov upper bound has vanishing physical R-squared
weight in dimension above four, including blocks of zero law mass. -/
theorem tendsto_originalUnitBlockDiscrepancy_bound_quadratic_zero {q : ℕ}
    (hq : 4 < q) (b : OrthonormalBasis (Fin q) ℝ (EuclideanSpace ℝ (Fin q)))
    {w r : ℝ} (hw : 0 ≤ w) :
    Tendsto (fun R : ℝ ↦
      let V := volume.real (originalCenteredPhysicalCubeRegion b (2 * R))
      R^2 * (Real.sqrt (2 * V * w) / (r * V))) atTop (𝓝 0) := by
  have hlim := (tendsto_originalScreeningPhysicalCube_quadratic_sqrt_volume_zero hq b).const_mul
    (Real.sqrt (2 * w) / r)
  simp only [mul_zero] at hlim
  convert hlim using 1
  funext R
  dsimp only
  rw [show 2 * volume.real (originalCenteredPhysicalCubeRegion b (2 * R)) * w =
    (2 * w) * volume.real (originalCenteredPhysicalCubeRegion b (2 * R)) by ring,
    Real.sqrt_mul (mul_nonneg (by norm_num) hw)]
  calc
    _ = (Real.sqrt (2 * w) / r) * R^2 *
        (Real.sqrt (volume.real (originalCenteredPhysicalCubeRegion b (2 * R))) /
          volume.real (originalCenteredPhysicalCubeRegion b (2 * R))) := by ring
    _ = _ := by rw [Real.sqrt_div_self']; ring

namespace OriginalReserveFullUnitInputExperiment
variable {q : ℕ} {α β : Measure ℝ} [IsProbabilityMeasure α] [IsProbabilityMeasure β]
  {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
  {Main Reserve : LegalWeightedStationaryPoissonMatching q α β kin g}
  {b : OrthonormalBasis (Fin q) ℝ (EuclideanSpace ℝ (Fin q))}
  {θ R : ℝ} {hθ : 0 < θ} {hθ1 : θ < 1}

/-- The actual unit-input count law supplies this same-join deviation-event
bound internally, without any event-independent count approximation. -/
theorem unitBlock_discrepancy_probability
    (X : OriginalReserveFullUnitInputExperiment Main Reserve b θ hθ hθ1 R)
    (hq : 0 < q) (hR : 0 < R) {S T : Set ℝ}
    (hS : MeasurableSet S) (hT : MeasurableSet T) (hbal : α S = β T) {r : ℝ} (hr : 0 < r) :
    let K := originalCenteredPhysicalCubeRegion b (2 * R)
    (X.fullLaw : Measure (OriginalReserveUnitExperimentSpace q × TwoMarkedCloudSpace q ℝ ℝ)).real
      {p | r * volume.real K <
        |(originalMainPhysicalBlockCount K S 0 (originalReserveUnitInputReadout q θ hθ hθ1 p.1) : ℝ) -
          (originalMainPhysicalBlockCount K T 1 (originalReserveUnitInputReadout q θ hθ hθ1 p.1) : ℝ)|} ≤
      Real.sqrt (2 * volume.real K * α.real S) / (r * volume.real K) := by
  dsimp only
  let K := originalCenteredPhysicalCubeRegion b (2 * R)
  let f : OriginalReserveUnitExperimentSpace q × TwoMarkedCloudSpace q ℝ ℝ → ℝ := fun p ↦
    |(originalMainPhysicalBlockCount K S 0 (originalReserveUnitInputReadout q θ hθ hθ1 p.1) : ℝ) -
      (originalMainPhysicalBlockCount K T 1 (originalReserveUnitInputReadout q θ hθ hθ1 p.1) : ℝ)|
  have hV : 0 < volume.real K := by
    change 0 < (volume (originalCenteredPhysicalCubeRegion b (2 * R))).toReal
    rw [volume_originalOrientedTraffic_cube b R]
    change 0 < volume.real (haarRootCube (Fin q) R)
    rw [volume_real_haarRootCube (Fin q) hR.le, Fintype.card_fin]
    positivity
  have hd := X.unitBlock_discrepancy hq (isCompact_originalStagePhysicalCube b (2 * R)) hS hT hbal
  have hnn : ∀ p, 0 ≤ f p := fun p ↦ abs_nonneg _
  have hm := measureReal_strict_gt_le_integral_div_of_nonneg
    (X.fullLaw : Measure (OriginalReserveUnitExperimentSpace q × TwoMarkedCloudSpace q ℝ ℝ))
    f hnn hd.1 (mul_pos hr hV)
  exact hm.trans (div_le_div_of_nonneg_right hd.2 (mul_nonneg hr.le hV.le))

/-- Every fixed balanced actual unit block has a negligible threshold-failure
probability on its family of true full original joined experiments. -/
theorem tendsto_unitBlock_discrepancy_probability (hq : 4 < q)
    (X : ∀ R : ℝ, 0 < R → OriginalReserveFullUnitInputExperiment Main Reserve b θ hθ hθ1 R)
    {S T : Set ℝ} (hS : MeasurableSet S) (hT : MeasurableSet T) (hbal : α S = β T)
    {r : ℝ} (hr : 0 < r) :
    Tendsto (fun R : ℝ ↦ if hR : 0 < R then
      let K := originalCenteredPhysicalCubeRegion b (2 * R)
      R^2 * ((X R hR).fullLaw : Measure (OriginalReserveUnitExperimentSpace q × TwoMarkedCloudSpace q ℝ ℝ)).real
        {p | r * volume.real K <
          |(originalMainPhysicalBlockCount K S 0 (originalReserveUnitInputReadout q θ hθ hθ1 p.1) : ℝ) -
            (originalMainPhysicalBlockCount K T 1 (originalReserveUnitInputReadout q θ hθ hθ1 p.1) : ℝ)|}
      else 0) atTop (𝓝 0) := by
  apply squeeze_zero' (Eventually.of_forall fun R ↦ by split_ifs <;> positivity) ?_
    (tendsto_originalUnitBlockDiscrepancy_bound_quadratic_zero hq b (w := α.real S) (r := r) measureReal_nonneg)
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR
  simp only [dite_eq_left hR]
  exact mul_le_mul_of_nonneg_left
    ((X R hR).unitBlock_discrepancy_probability (by omega) hR hS hT hbal hr) (sq_nonneg R)

end OriginalReserveFullUnitInputExperiment
end OTSelector.Reconstruction
