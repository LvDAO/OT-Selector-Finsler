import OTSelector.Reconstruction.OriginalReserveFullUnitInputReserveCapacity
import OTSelector.Reconstruction.OriginalScreeningBoundaryBudgetActualCountLimit

/-! Genuine reserve-class capacity failures are negligible at the physical quadratic scale. -/
open Set Function MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators Classical
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000

/-- The true half-mean Poisson-capacity error vanishes after physical R-squared
weighting in dimension above four. The class mean is the actual theta V mass. -/
theorem tendsto_originalReserveClassCount_lower_bound_quadratic_zero {q : ℕ}
    (hq : 4 < q) (b : OrthonormalBasis (Fin q) ℝ (EuclideanSpace ℝ (Fin q)))
    {θ : ℝ} (hθ : 0 < θ) (γ : Measure ℝ) (C : Set ℝ) (hCmass : 0 < γ.real C) :
    Tendsto (fun R : ℝ ↦
      let a := ((Real.toNNReal θ * (volume (originalCenteredPhysicalCubeRegion b (2 * R))).toNNReal) *
        (γ C).toNNReal : ℝ≥0)
      R^2 * (Real.sqrt (a : ℝ) / ((a : ℝ) / 2))) atTop (𝓝 0) := by
  let τ := θ * γ.real C
  have hτ : 0 < τ := mul_pos hθ hCmass
  have hlim := (tendsto_originalScreeningPhysicalCube_quadratic_sqrt_volume_zero hq b).const_mul
    (2 / Real.sqrt τ)
  simp only [mul_zero] at hlim
  convert hlim using 1
  funext R
  simp only [NNReal.coe_mul, ENNReal.coe_toNNReal_eq_toReal, Real.coe_toNNReal _ hθ.le]
  change R^2 * (Real.sqrt (θ * volume.real (originalCenteredPhysicalCubeRegion b (2 * R)) * γ.real C) /
      ((θ * volume.real (originalCenteredPhysicalCubeRegion b (2 * R)) * γ.real C) / 2)) = _
  rw [show θ * volume.real (originalCenteredPhysicalCubeRegion b (2 * R)) * γ.real C =
    τ * volume.real (originalCenteredPhysicalCubeRegion b (2 * R)) by dsimp [τ]; ring]
  have hh (x : ℝ) : Real.sqrt x / (x / 2) = 2 * (1 / Real.sqrt x) := by
    calc
      _ = 2 * (Real.sqrt x / x) := by rw [div_div_eq_mul_div]; ring
      _ = _ := by rw [Real.sqrt_div_self']
  rw [hh, Real.sqrt_mul hτ.le]
  ring

namespace OriginalReserveFullUnitInputExperiment
variable {q : ℕ} {α β : Measure ℝ} [IsProbabilityMeasure α] [IsProbabilityMeasure β]
  {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
  {Main Reserve : LegalWeightedStationaryPoissonMatching q α β kin g}
  {b : OrthonormalBasis (Fin q) ℝ (EuclideanSpace ℝ (Fin q))}
  {θ : ℝ} {hθ : 0 < θ} {hθ1 : θ < 1}

/-- For any constructed family of actual full experiments, failure of the
source positive-class capacity has quadratically negligible probability.
All event correlations remain on each original full joining. -/
theorem tendsto_sourceReserveBlockCount_lower_probability (hq : 4 < q)
    (X : ∀ R : ℝ, 0 < R → OriginalReserveFullUnitInputExperiment Main Reserve b θ hθ hθ1 R)
    {C : Set ℝ} (hC : MeasurableSet C) (hCmass : 0 < α.real C) :
    Tendsto (fun R : ℝ ↦ if hR : 0 < R then
      let a := (Real.toNNReal θ * (volume (originalCenteredPhysicalCubeRegion b (2 * R))).toNNReal) * (α C).toNNReal
      R^2 * ((X R hR).fullLaw : Measure (OriginalReserveUnitExperimentSpace q × TwoMarkedCloudSpace q ℝ ℝ)).real
        {p | (originalReserveBlockCount p.1.2.2.1.1 (fun i ↦ (p.1.2.2.1.2 i).2) C : ℝ) < (a : ℝ) / 2}
      else 0) atTop (𝓝 0) := by
  apply squeeze_zero' (Eventually.of_forall fun R ↦ by
    split_ifs <;> positivity) ?_
    (tendsto_originalReserveClassCount_lower_bound_quadratic_zero hq b hθ α C hCmass)
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR
  simp only [dite_eq_left hR]
  exact mul_le_mul_of_nonneg_left
    ((X R hR).sourceReserveBlockCount_lower_probability hR hC hCmass) (sq_nonneg R)

/-- For any constructed family of actual full experiments, failure of the
target positive-class capacity has quadratically negligible probability.
All event correlations remain on each original full joining. -/
theorem tendsto_targetReserveBlockCount_lower_probability (hq : 4 < q)
    (X : ∀ R : ℝ, 0 < R → OriginalReserveFullUnitInputExperiment Main Reserve b θ hθ hθ1 R)
    {C : Set ℝ} (hC : MeasurableSet C) (hCmass : 0 < β.real C) :
    Tendsto (fun R : ℝ ↦ if hR : 0 < R then
      let a := (Real.toNNReal θ * (volume (originalCenteredPhysicalCubeRegion b (2 * R))).toNNReal) * (β C).toNNReal
      R^2 * ((X R hR).fullLaw : Measure (OriginalReserveUnitExperimentSpace q × TwoMarkedCloudSpace q ℝ ℝ)).real
        {p | (originalReserveBlockCount p.1.2.2.2.1 (fun i ↦ (p.1.2.2.2.2 i).2) C : ℝ) < (a : ℝ) / 2}
      else 0) atTop (𝓝 0) := by
  apply squeeze_zero' (Eventually.of_forall fun R ↦ by
    split_ifs <;> positivity) ?_
    (tendsto_originalReserveClassCount_lower_bound_quadratic_zero hq b hθ β C hCmass)
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR
  simp only [dite_eq_left hR]
  exact mul_le_mul_of_nonneg_left
    ((X R hR).targetReserveBlockCount_lower_probability hR hC hCmass) (sq_nonneg R)

end OriginalReserveFullUnitInputExperiment
end OTSelector.Reconstruction
