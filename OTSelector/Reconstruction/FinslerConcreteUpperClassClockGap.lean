import OTSelector.Reconstruction.FinslerConcreteUpperClassMask
import OTSelector.Geometry.FinslerDistanceLocalizationPopulation
import OTSelector.Topology.MetricSpace.CompactFlowClockGap

/-!
Actual opposite-color support separation restores the original scalar Taylor
window after finite-class clock resampling. The common label scale is produced
from the original compact seed-label image and actual unit-speed seed curves.
-/

open Set Function MeasureTheory ProbabilityTheory Matrix Manifold OTSelector.Geometry
open scoped Topology ContDiff ENNReal Matrix.Norms.Operator
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
set_option linter.unusedSectionVars false

namespace OTSelector.Reconstruction.PopulationLocalPressureCore

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {P : ℕ → F.CalibratedSeedWindow u} {a : M → (ℚ → M)}
  {κ : ∀ j, Measure (P j).seed.covector.ker} {lambda : Measure (ℚ → M)}
  {η₀ η₁ : Measure M} [IsFiniteMeasure η₀] [IsFiniteMeasure η₁]
  {ρ₀ ρ₁ : M → ℝ} {v : ℕ → E → ℝ} {b : (ℚ → M) × ℝ → M}
  {Good : (ℚ → M) → Prop} {r : ℝ} {δ ε : ℝ≥0∞}

variable (D : PopulationLocalPressureCore P a κ lambda η₀ η₁ ρ₀ ρ₁ v b Good r δ ε)

/-- The original compact physical support gap gives a common seed-coordinate
scale at which every actual opposite-color pair has half that clock gap. -/
theorem exists_uniform_original_clock_support_gap (hF : F.IsSmoothStronglyConvex)
    (i : Fin D.haar.continuous.count) {A B : Set M} {gap : ℝ} (hgap : 0 < gap)
    (hsep : let _inst : MetricSpace M := F.metricSpace
      ∀ x ∈ A, ∀ y ∈ B, gap ≤ dist x y) :
    ∃ radius > 0, ∀ z ∈ (D.haar.continuous.coefficient i).roots,
      ∀ z' ∈ (D.haar.continuous.coefficient i).roots,
      ∀ s ∈ Icc ((D.haar.continuous.coefficient i).window.val.1 : ℝ)
        ((D.haar.continuous.coefficient i).window.val.2.1 : ℝ),
      ∀ t ∈ Icc ((D.haar.continuous.coefficient i).window.val.1 : ℝ)
        ((D.haar.continuous.coefficient i).window.val.2.1 : ℝ),
      ‖populationSeedRootLabelValue (P (D.haar.continuous.coefficient i).seedIndex).seed a z -
        populationSeedRootLabelValue (P (D.haar.continuous.coefficient i).seedIndex).seed a z'‖ < radius →
      D.corePoint i (z, s) ∈ A → D.corePoint i (z', t) ∈ B → gap / 2 ≤ |t - s| := by
  let _inst : MetricSpace M := F.metricSpace
  let C := D.haar.continuous.coefficient i
  let S := (P C.seedIndex).seed
  let R := populationSeedRootLabelValue S a
  let K := R '' C.roots
  let T := Icc (C.window.val.1 : ℝ) (C.window.val.2.1 : ℝ)
  have hK : IsCompact K := by
    simpa only [D.haar.intensity_roots i] using (D.haar.intensity i).compact_labels
  have hlabels : K ⊆ S.labels := by
    simpa only [D.haar.intensity_roots i] using (D.haar.intensity i).labels_subset
  let flow : S.covector.ker → ℝ → M := fun w t ↦ S.curve w (t - S.level)
  have hflow : ContinuousOn (Function.uncurry flow) (K ×ˢ T) := by
    intro p hp
    exact (S.continuousAt_joint_curve (q := (p.1, p.2 - S.level))
      (S.labels_subset (hlabels hp.1))).comp_continuousWithinAt
      (f := fun q : S.covector.ker × ℝ ↦ (q.1, q.2 - S.level))
      (continuous_fst.prodMk (continuous_snd.sub continuous_const)).continuousWithinAt
  have hclock : ∀ w ∈ K, ∀ s ∈ T, ∀ t ∈ T,
      dist (flow w s) (flow w t) ≤ |t - s| := by
    intro w hw s _ t _
    have hL := hF.lipschitzWith_of_isEulerLagrangeOn_univ (S.complete w (hlabels hw)) 0
    rw [S.unit w (hlabels hw) 0] at hL
    have hdist := hL.dist_le_mul (s - S.level) (t - S.level)
    simpa only [NNReal.coe_one, one_mul, Real.dist_eq, sub_sub_sub_cancel_right,
      abs_sub_comm, flow] using hdist
  obtain ⟨radius, hradius, hbound⟩ := exists_uniform_clock_gap_of_compact_flow hK
    isCompact_Icc flow hflow hclock hgap hsep
  refine ⟨radius, hradius, fun z hz z' hz' s hs t ht hzz hA hB ↦ ?_⟩
  exact hbound (R z) ⟨z, hz, rfl⟩ (R z') ⟨z', hz', rfl⟩ s hs t ht
    (by simpa only [dist_eq_norm] using hzz) hA hB

/-- On an internally produced small scalar screen, actual separated support
points in the retained main bins lie in the original Taylor region. -/
theorem exists_original_clock_region_radius (hF : F.IsSmoothStronglyConvex)
    (i : Fin D.haar.continuous.count) {A B : Set M} {gap : ℝ} (hgap : 0 < gap)
    (hsep : let _inst : MetricSpace M := F.metricSpace
      ∀ x ∈ A, ∀ y ∈ B, gap ≤ dist x y)
    (hscreen : ((D.haar.continuous.coefficient i).window.val.2.2 : ℝ) ≤ gap / 2) :
    ∃ radius > 0, ∀ z ∈ (D.haar.continuous.coefficient i).roots,
      ∀ z' ∈ (D.haar.continuous.coefficient i).roots,
      ∀ s ∈ Icc ((D.haar.continuous.coefficient i).window.val.1 : ℝ)
        ((D.haar.continuous.coefficient i).window.val.2.1 : ℝ),
      ∀ t ∈ Icc ((D.haar.continuous.coefficient i).window.val.1 : ℝ)
        ((D.haar.continuous.coefficient i).window.val.2.1 : ℝ),
      ‖populationSeedRootLabelValue (P (D.haar.continuous.coefficient i).seedIndex).seed a z -
        populationSeedRootLabelValue (P (D.haar.continuous.coefficient i).seedIndex).seed a z'‖ < radius →
      s < t → D.corePoint i (z, s) ∈ A → D.corePoint i (z', t) ∈ B →
      (s, t) ∈ (D.haar.continuous.coefficient i).window.region := by
  obtain ⟨radius, hradius, hbound⟩ := D.exists_uniform_original_clock_support_gap hF i hgap hsep
  refine ⟨radius, hradius, fun z hz z' hz' s hs t ht hzz hst hA hB ↦ ?_⟩
  have h := hbound z hz z' hz' s hs t ht hzz hA hB
  rw [abs_of_pos (sub_pos.mpr hst)] at h
  exact ⟨⟨hs, ht⟩, hscreen.trans h⟩

end OTSelector.Reconstruction.PopulationLocalPressureCore
