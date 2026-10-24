import OTSelector.Geometry.FinslerDistanceLocalization
import OTSelector.Transport.CompactCalibrationSlack
import OTSelector.Geometry.Finsler.CalibratedSeedWindowLabels

/-! # Uniform positive distance slack on original compact label cores -/

open Set Filter Metric Manifold Bundle
open scoped Topology ContDiff
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OTSelector.Geometry.ContinuousFinslerNorm.CalibratedLevelSeedPatch

variable {E M Z : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] {F : ContinuousFinslerNorm E M} {u : M → ℝ}

omit [BorelSpace E] in
/-- Every active interior point retains the original geometric root and lies in
its original regular domain. -/
theorem active_point_root_data (S : CalibratedLevelSeedPatch F u)
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _inst : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    {a : M → Z}
    (horder : let _inst : MetricSpace M := F.metricSpace
      ∀ x ∈ F.potentialRegularDomain u, ∀ y ∈ F.potentialRegularDomain u,
        (a x = a y ∧ u x ≤ u y) ↔ u y - u x = dist x y)
    {w : S.covector.ker} (hw : w ∈ S.labels) {t : ℝ}
    (ht : t ∈ interior (S.calibrationTimes w)) :
    S.curve w t ∈ F.potentialRegularDomain u ∧ a (S.curve w t) = a (S.curve w 0) := by
  let _inst : MetricSpace M := F.metricSpace
  rw [← S.iUnion_rationalWindow_timeDomain hF hu hw] at ht
  obtain ⟨k, hk⟩ := mem_iUnion.mp ht
  exact ⟨hF.mem_potentialRegularDomain_of_mem_calibratedInterior hcomplete hu
    ((S.rationalWindow k).mapsTo_calibratedInterior hF hu hk),
    (S.rationalWindow k).label_toManifold_eq_initial hF hcomplete hu horder hk⟩

omit [BorelSpace E] in
/-- The original distance slack has a positive uniform gap between separated
labels on any compact set of active endpoint pairs of the same seed. -/
theorem exists_uniform_distance_slack_gap (S : CalibratedLevelSeedPatch F u)
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _inst : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    {K : Set ((S.covector.ker × ℝ) × (S.covector.ker × ℝ))} (hK : IsCompact K)
    (hlabels : ∀ p ∈ K, p.1.1 ∈ S.labels ∧ p.2.1 ∈ S.labels)
    (hactive : ∀ p ∈ K, p.1.2 ∈ interior (S.calibrationTimes p.1.1) ∧
      p.2.2 ∈ interior (S.calibrationTimes p.2.1))
    {r : ℝ} (hr : 0 < r) :
    ∃ δ > 0, ∀ p ∈ K, r ≤ ‖p.2.1 - p.1.1‖ →
      δ ≤ (F.lengthEDist (S.curve p.1.1 p.1.2) (S.curve p.2.1 p.2.2)).toReal -
        u (S.curve p.2.1 p.2.2) + u (S.curve p.1.1 p.1.2) := by
  let _inst : MetricSpace M := F.metricSpace
  apply exists_distance_slack_gap_of_compact hK (X := fun p ↦ S.curve p.1.1 p.1.2)
    (Y := fun p ↦ S.curve p.2.1 p.2.2)
    (fun p hp ↦ ((S.continuousAt_joint_curve (S.labels_subset (hlabels p hp).1)).comp
      continuous_fst.continuousAt).continuousWithinAt)
    (fun p hp ↦ ((S.continuousAt_joint_curve (S.labels_subset (hlabels p hp).2)).comp
      continuous_snd.continuousAt).continuousWithinAt) hu
    ((continuous_snd.fst.sub continuous_fst.fst).norm.continuousOn) ?_ hr
  intro p hp hzero
  have heq := S.label_eq_of_distance_slack_zero hF hcomplete hu
    (hlabels p hp).1 (hlabels p hp).2 (hactive p hp).1 (hactive p hp).2 hzero
  change ‖p.2.1 - p.1.1‖ = 0
  rw [heq, sub_self, norm_zero]

end OTSelector.Geometry.ContinuousFinslerNorm.CalibratedLevelSeedPatch
