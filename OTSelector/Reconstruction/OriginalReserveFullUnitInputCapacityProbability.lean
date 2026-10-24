import OTSelector.Reconstruction.OriginalReserveFullUnitInputCapacityEvents
import OTSelector.Reconstruction.OriginalReservePositiveBlockCapacityUnion
import OTSelector.Reconstruction.OriginalReservePositiveBlockDeviationUnion
import OTSelector.Reconstruction.OriginalReserveFullUnitInputFamily

/-! Actual original blockwise deletion capacity holds outside a quadratically negligible event. -/
open Set Function MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators Classical
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace OriginalReserveFullUnitInputExperiment
variable {q : ℕ} {α β : Measure ℝ} [IsProbabilityMeasure α] [IsProbabilityMeasure β]
  {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
  {Main Reserve : LegalWeightedStationaryPoissonMatching q α β kin g}
  {b : OrthonormalBasis (Fin q) ℝ (EuclideanSpace ℝ (Fin q))}
  {θ : ℝ} {hθ : 0 < θ} {hθ1 : θ < 1}

/-- All actual source and target blockwise deletion capacities, including zero
blocks, hold outside a quadratically negligible event in the true full joining.
Counts, actual requested excess, class positivity and probability rates are
produced internally; the only grid inputs are its proved law structure. -/
theorem tendsto_clockSlabCapacityFailure_probability (hq : 4 < q)
    (X : ∀ R : ℝ, 0 < R → OriginalReserveFullUnitInputExperiment Main Reserve b θ hθ hθ1 R)
    (G : OriginalStageClockGrid)
    (hmono : ∀ i, α (G.sourceCell i) = 0 ∨ β (G.targetCell i) = 0)
    (hH : ∀ k ≤ G.count, 0 ≤ G.clockSlabSurplus α β k) :
    Tendsto (fun R : ℝ ↦ if hR : 0 < R then
      R^2 * ((X R hR).fullLaw : Measure (OriginalReserveUnitExperimentSpace q × TwoMarkedCloudSpace q ℝ ℝ)).real
        (originalReserveClockSlabCapacityFailure α β b θ hθ1 R G)
      else 0) atTop (𝓝 0) := by
  have hs : Tendsto (fun R : ℝ ↦ if hR : 0 < R then
      R^2 * ((X R hR).fullLaw : Measure (OriginalReserveUnitExperimentSpace q × TwoMarkedCloudSpace q ℝ ℝ)).real
        (originalReservePositiveBlockExtremeFailure α β b θ R G) else 0) atTop (𝓝 0) := by
    simpa only [originalReservePositiveBlockExtremeFailure, NNReal.coe_mul,
      ENNReal.coe_toNNReal_eq_toReal, Real.coe_toNNReal _ hθ.le, measureReal_def] using
      tendsto_positiveBlockExtreme_capacity_failure hq X G hmono hH
  have ht : Tendsto (fun R : ℝ ↦ if hR : 0 < R then
      R^2 * ((X R hR).fullLaw : Measure (OriginalReserveUnitExperimentSpace q × TwoMarkedCloudSpace q ℝ ℝ)).real
        (originalReservePositiveBlockDeviationFailure α β b θ hθ hθ1 R G) else 0) atTop (𝓝 0) := by
    exact tendsto_positiveBlock_unitDiscrepancy_failure hq X G hmono hH
  have hu := hs.add ht
  simp only [zero_add] at hu
  apply squeeze_zero' (Eventually.of_forall fun R ↦ by split_ifs <;> positivity) ?_ hu
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR
  simp only [dite_eq_left hR]
  have hm :
      ((X R hR).fullLaw : Measure (OriginalReserveUnitExperimentSpace q × TwoMarkedCloudSpace q ℝ ℝ))
        (originalReserveClockSlabCapacityFailure α β b θ hθ1 R G) ≤
      ((X R hR).fullLaw : Measure (OriginalReserveUnitExperimentSpace q × TwoMarkedCloudSpace q ℝ ℝ))
        (originalReservePositiveBlockExtremeFailure α β b θ R G ∪
          originalReservePositiveBlockDeviationFailure α β b θ hθ hθ1 R G) :=
    measure_mono_ae ((X R hR).ae_capacityFailure_subset (by omega) G)
  have hp := (ENNReal.toReal_mono (measure_ne_top
    ((X R hR).fullLaw : Measure (OriginalReserveUnitExperimentSpace q × TwoMarkedCloudSpace q ℝ ℝ)) _)
      hm).trans
        (measureReal_union_le
          (originalReservePositiveBlockExtremeFailure α β b θ R G)
          (originalReservePositiveBlockDeviationFailure α β b θ hθ hθ1 R G))
  exact (mul_le_mul_of_nonneg_left hp (sq_nonneg R)).trans_eq (by ring)

end OriginalReserveFullUnitInputExperiment
end OTSelector.Reconstruction
