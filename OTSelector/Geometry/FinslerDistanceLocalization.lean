import OTSelector.Geometry.Finsler.CalibratedSeedRecovery
import OTSelector.Geometry.Finsler.SeedCalibrationSpan
import OTSelector.Geometry.Finsler.SeedKernelMeasurability

/-!
# Distance slack separates distinct active seed labels

The original complete dynamics identify labels when an endpoint pair saturates the
potential inequality. Compact label and time sets then give a uniform positive
slack for pairs separated by any fixed positive label distance.
-/

open Set Filter Metric Manifold Bundle
open scoped Topology ContDiff

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OTSelector.Geometry.ContinuousFinslerNorm

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] {F : ContinuousFinslerNorm E M} {u : M → ℝ}

namespace CalibratedLevelSeedPatch

omit [BorelSpace E] [T2Space M] [PreconnectedSpace M] in
private theorem shifted_complete_unit (S : CalibratedLevelSeedPatch F u)
    (hF : F.IsSmoothStronglyConvex) {w : S.covector.ker} (hw : w ∈ S.labels) (a : ℝ) :
    F.IsEulerLagrangeOn (fun t ↦ S.curve w (t + a)) univ ∧
      ∀ t : ℝ, F.toFun (tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E)
        (fun t ↦ S.curve w (t + a)) ⟨t, (1 : ℝ)⟩) = 1 := by
  constructor
  · simpa only [one_mul, sub_neg_eq_add, preimage_univ, Function.comp_def] using
      hF.isEulerLagrangeOn_affine (S.complete w hw) (s := 1) (a := -a) zero_lt_one
  · intro t
    have hd := (hF.contMDiffAt_of_isEulerLagrangeAt
      (S.complete w hw (1 * (t - -a)) (mem_univ _))).mdifferentiableAt (by simp)
    have hs := F.speed_affine (s := 1) (a := -a) zero_lt_one hd
    apply NNReal.coe_injective
    simpa only [one_mul, sub_neg_eq_add, Function.comp_def, S.unit w hw] using hs

omit [FiniteDimensional ℝ E] [BorelSpace E] [T2Space M] [PreconnectedSpace M] in
private theorem local_shift_clock (S : CalibratedLevelSeedPatch F u)
    {w : S.covector.ker} {a : ℝ} (ha : a ∈ interior (S.calibrationTimes w)) :
    ∃ δ > 0, ∀ t ∈ Icc (-δ) δ,
      u (S.curve w (t + a)) = u (S.curve w (0 + a)) + t := by
  obtain ⟨δ, hδ, hball⟩ := Metric.nhds_basis_closedBall.mem_iff.mp
    (mem_interior_iff_mem_nhds.mp ha)
  refine ⟨δ, hδ, fun t ht ↦ ?_⟩
  have hta : t + a ∈ S.calibrationTimes w := hball (by
    rw [mem_closedBall, Real.dist_eq, add_sub_cancel_right, abs_le]
    exact ht)
  have ha' := show a ∈ S.calibrationTimes w from interior_subset ha
  change u (S.curve w (t + a)) = (S.level : ℝ) + (t + a) at hta
  change u (S.curve w a) = (S.level : ℝ) + a at ha'
  rw [hta, zero_add, ha']
  ring

omit [BorelSpace E] in
/-- A calibrated endpoint pair in the active interiors belongs to the same original
seed label. The conclusion uses complete trajectory uniqueness and the seed's actual
initial injectivity; no prescribed equality of labels is assumed. -/
theorem label_eq_of_distance_slack_zero (S : CalibratedLevelSeedPatch F u)
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _inst : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    {w z : S.covector.ker} (hw : w ∈ S.labels) (hz : z ∈ S.labels)
    {a b : ℝ} (ha : a ∈ interior (S.calibrationTimes w))
    (hb : b ∈ interior (S.calibrationTimes z))
    (hzero : (F.lengthEDist (S.curve w a) (S.curve z b)).toReal -
      u (S.curve z b) + u (S.curve w a) = 0) : w = z := by
  let _inst : MetricSpace M := F.metricSpace
  obtain ⟨hc, hcunit⟩ := S.shifted_complete_unit hF hw a
  obtain ⟨hd, hdunit⟩ := S.shifted_complete_unit hF hz b
  obtain ⟨δ, hδ, hclockc⟩ := S.local_shift_clock ha
  obtain ⟨ε, hε, hclockd⟩ := S.local_shift_clock hb
  have hsat : u (S.curve z (0 + b)) - u (S.curve w (0 + a)) =
      dist (S.curve w (0 + a)) (S.curve z (0 + b)) := by
    simp only [zero_add, F.metricSpace_dist]
    linarith
  have heq := hF.eq_timeShift_of_calibrated_pair_of_complete_unit_clocks
    hcomplete hu hc hd hcunit hdunit hδ hε hclockc hclockd hsat
  have hwa : u (S.curve w a) = (S.level : ℝ) + a := show a ∈ S.calibrationTimes w from interior_subset ha
  have hzb : u (S.curve z b) = (S.level : ℝ) + b := show b ∈ S.calibrationTimes z from interior_subset hb
  have h := congrFun heq (-a)
  simp only [zero_add, hwa, hzb] at h
  have htime : -a + ((S.level : ℝ) + a) - ((S.level : ℝ) + b) + b = 0 := by ring
  apply S.initial_injective hw hz
  simpa only [neg_add_cancel, htime] using h

end CalibratedLevelSeedPatch
end OTSelector.Geometry.ContinuousFinslerNorm
