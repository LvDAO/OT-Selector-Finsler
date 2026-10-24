import OTSelector.Reconstruction.OriginalMarkSelectedPopulationCouplingBlockExcessBudgetLimit

/-! Actual full-block leftovers pay fixed quadratic-plus-tilt coefficients. -/
open Set Function MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability

/-- A quadratic vanishing real quantity also pays every fixed quadratic-plus-linear coefficient. -/
theorem tendsto_weighted_quadratic_zero_of_quadratic_zero
    {f : ℝ → ℝ} (h : Tendsto (fun R ↦ R^2*f R) atTop (𝓝 0)) (A B : ℝ) :
    Tendsto (fun R ↦ (A*R^2+B)*f R) atTop (𝓝 0) := by
  have hd := h.div_atTop (tendsto_pow_atTop (by norm_num : (2:ℕ) ≠ 0))
  have hf : Tendsto f atTop (𝓝 0) := by
    apply hd.congr'
    filter_upwards [eventually_gt_atTop (0:ℝ)] with R hR
    exact mul_div_cancel_left₀ (f R) (pow_ne_zero 2 hR.ne')
  have hw := (h.const_mul A).add (hf.const_mul B)
  simp only [mul_zero,add_zero] at hw
  exact hw.congr' (Eventually.of_forall fun R ↦ by ring)

/-- The literal full main-plus-reserve block discrepancy pays every fixed
physical quadratic coefficient and bounded tilt term. Its genuine Poisson
moment and dimension-dependent decay are supplied internally. -/
theorem LegalWeightedStationaryPoissonMatching.tendsto_original_screening_blockCompletion_cost_zero
    {q : ℕ} {α β : Measure ℝ} [IsProbabilityMeasure α] [IsProbabilityMeasure β]
    {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (Q : LegalWeightedStationaryPoissonMatching q α β kin g) (hq : 4 < q)
    (b : OrthonormalBasis (Fin q) ℝ (EuclideanSpace ℝ (Fin q)))
    (rho : ℝ) (G : OriginalStageClockGrid) (A B : ℝ) :
    Tendsto (fun R : ℝ ↦
      (∫ p, (A*R^2+B)*originalFullClockSlabDiscrepancy (α := α) (β := β) G
        (originalCenteredPhysicalCubeRegion b (2*R)) p
        ∂originalMainReserveExperimentLaw Q (Real.toNNReal rho *
          (volume (originalCenteredPhysicalCubeRegion b (2*R))).toNNReal)) /
            volume.real (originalCenteredPhysicalCubeRegion b (2*R))) atTop (𝓝 0) := by
  have h := Q.tendsto_originalFullClockSlabDiscrepancy_quadratic_cost_zero hq b (Real.toNNReal rho) G
  have hquad : Tendsto (fun R : ℝ ↦ R^2 *
      ((∫ p, originalFullClockSlabDiscrepancy (α := α) (β := β) G
        (originalCenteredPhysicalCubeRegion b (2*R)) p
        ∂originalMainReserveExperimentLaw Q (Real.toNNReal rho *
          (volume (originalCenteredPhysicalCubeRegion b (2*R))).toNNReal)) /
            volume.real (originalCenteredPhysicalCubeRegion b (2*R)))) atTop (𝓝 0) :=
    h.congr' (Eventually.of_forall fun R ↦ by ring)
  apply (tendsto_weighted_quadratic_zero_of_quadratic_zero hquad A B).congr'
  exact Eventually.of_forall fun R ↦ by
    dsimp only
    rw [integral_const_mul]
    ring

end OTSelector.Reconstruction
