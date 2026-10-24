import OTSelector.Reconstruction.OriginalLegalScreeningExpectedCostFailures
import OTSelector.Reconstruction.OriginalReserveMainExperimentCapacityProbability

/-! Genuine all-block deletion capacity failures join the actual reserve and block budget exceptions. -/
open Set Function MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
variable {q : ℕ} {α β : Measure ℝ} [IsProbabilityMeasure α] [IsProbabilityMeasure β]
  {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}

/-- One original joint event contains every raw prefix, full-block excess and
actual deletion-capacity exception. Its definition uses literal original counts. -/
def originalScreeningCapacityReserveFailure (α β : Measure ℝ)
    (b : OrthonormalBasis (Fin q) ℝ (EuclideanSpace ℝ (Fin q)))
    (rho R : ℝ) (G : OriginalStageClockGrid) (r : ℝ) :
    Set (LegalMarkedOptimalInputScene q × TwoMarkedCloudSpace q ℝ ℝ) :=
  originalScreeningReserveBlockFailure α β b rho R G r ∪
    originalMainReserveClockSlabCapacityFailure α β b R G

omit [IsProbabilityMeasure α] [IsProbabilityMeasure β] in
/-- The complete capacity/reserve exception is jointly measurable on the original sampler. -/
theorem measurableSet_originalScreeningCapacityReserveFailure
    (b : OrthonormalBasis (Fin q) ℝ (EuclideanSpace ℝ (Fin q)))
    (rho R : ℝ) (G : OriginalStageClockGrid) (r : ℝ) :
    MeasurableSet (originalScreeningCapacityReserveFailure α β b rho R G r) :=
  (measurableSet_originalScreeningReserveBlockFailure b rho R G r).union
    (measurableSet_originalMainReserveClockSlabCapacityFailure α β b R G)

/-- Actual Poisson/block/capacity proofs produce the whole exception's quadratic
probability rate at every positive raw reserve intensity, without a rate callback. -/
theorem LegalWeightedStationaryPoissonMatching.tendsto_original_screening_capacityReserveFailure_probability
    (Q : LegalWeightedStationaryPoissonMatching q α β kin g) (hq : 4 < q)
    (b : OrthonormalBasis (Fin q) ℝ (EuclideanSpace ℝ (Fin q)))
    {rho r : ℝ} (hrho : 0 < rho) (G : OriginalStageClockGrid) (hr : 0 < r)
    (hmono : ∀ i, α (G.sourceCell i) = 0 ∨ β (G.targetCell i) = 0)
    (hH : ∀ k ≤ G.count, 0 ≤ G.clockSlabSurplus α β k) :
    Tendsto (fun R : ℝ ↦ R^2 *
      (originalMainReserveExperimentLaw Q (Real.toNNReal rho *
        (volume (originalCenteredPhysicalCubeRegion b (2*R))).toNNReal)).real
          (originalScreeningCapacityReserveFailure α β b rho R G r)) atTop (𝓝 0) := by
  have hu := (Q.tendsto_original_screening_reserveBlockFailure_probability hq b hrho G hr).add
    (Q.tendsto_originalMainReserveClockSlabCapacityFailure hq b hrho G hmono hH)
  simp only [add_zero] at hu
  apply squeeze_zero' (Eventually.of_forall (fun R ↦ mul_nonneg (sq_nonneg R) measureReal_nonneg)) ?_ hu
  exact Eventually.of_forall fun R ↦ by
    rw [← mul_add]
    exact mul_le_mul_of_nonneg_left (measureReal_union_le _ _) (sq_nonneg R)

/-- The same actual full main-plus-reserve count pays every simultaneous
capacity, prefix and block exception. The natural original law supplies its own
probability rate and count moments internally. -/
theorem LegalWeightedStationaryPoissonMatching.tendsto_original_screening_capacityReserveFailure_count_cost
    (Q : LegalWeightedStationaryPoissonMatching q α β kin g) (hq : 4 < q)
    (b : OrthonormalBasis (Fin q) ℝ (EuclideanSpace ℝ (Fin q)))
    {rho r : ℝ} (hrho : 0 < rho) (G : OriginalStageClockGrid) (hr : 0 < r)
    (hmono : ∀ i, α (G.sourceCell i) = 0 ∨ β (G.targetCell i) = 0)
    (hH : ∀ k ≤ G.count, 0 ≤ G.clockSlabSurplus α β k) :
    Tendsto (fun R : ℝ ↦ R^2 *
      ((∫ p, (originalScreeningCapacityReserveFailure α β b rho R G r).indicator
        (originalScreeningFullExperimentCount (originalCenteredPhysicalCubeRegion b (2*R))) p
        ∂originalMainReserveExperimentLaw Q (Real.toNNReal rho *
          (volume (originalCenteredPhysicalCubeRegion b (2*R))).toNNReal)) /
          volume.real (originalCenteredPhysicalCubeRegion b (2*R)))) atTop (𝓝 0) :=
  Q.tendsto_original_screening_fullExperimentCount_bad_cost_zero hq b hrho.le
    (fun R ↦ originalScreeningCapacityReserveFailure α β b rho R G r)
    (fun R ↦ measurableSet_originalScreeningCapacityReserveFailure b rho R G r)
    (Q.tendsto_original_screening_capacityReserveFailure_probability hq b hrho G hr hmono hH)

end OTSelector.Reconstruction
