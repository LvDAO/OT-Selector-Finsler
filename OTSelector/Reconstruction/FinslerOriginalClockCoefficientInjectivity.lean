import OTSelector.Reconstruction.FinslerPhysicalSceneRootedOriginalIntrinsicClockKernel

/-!
# Original coefficient injectivity in the target clock

The compliance increment between two target clocks is the integral of the
same positive kernel on the intervening interval. In positive dimension it
cannot vanish, so inverse compliance distinguishes the two clock endpoints.
-/
open Set Matrix Module Manifold MeasureTheory
open scoped Topology ContDiff Matrix.Norms.Operator
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Geometry ContinuousFinslerNorm
set_option backward.isDefEq.respectTransparency false

/-- A positive kernel has distinct inverse compliances at strictly ordered
right endpoints. Positive dimension is the only nondegeneracy assumption. -/
theorem inverse_intervalCompliance_right_ne_of_lt
    {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
    {K : ℝ → Matrix n n ℝ} {s t r : ℝ} (hst : s < t) (htr : t < r)
    (hK : ContinuousOn K (Icc s r)) (hpos : ∀ a ∈ Icc s r, (K a).PosDef) :
    (∫ a in s..t, K a)⁻¹ ≠ (∫ a in s..r, K a)⁻¹ := by
  have hstsub : Icc s t ⊆ Icc s r := Icc_subset_Icc le_rfl htr.le
  have htrsub : Icc t r ⊆ Icc s r := Icc_subset_Icc hst.le le_rfl
  have hp₁ := posDef_intervalIntegral hst (hK.mono hstsub)
    (fun a ha ↦ hpos a (hstsub ha))
  have hp₂ := posDef_intervalIntegral htr (hK.mono htrsub)
    (fun a ha ↦ hpos a (htrsub ha))
  have hi : IntervalIntegrable K volume s r :=
    (show ContinuousOn K (uIcc s r) by
      simpa only [uIcc_of_le (hst.trans htr).le] using hK).intervalIntegrable
  have hi₁ : IntervalIntegrable K volume s t := hi.mono_set (by
    rw [uIcc_of_le hst.le, uIcc_of_le (hst.trans htr).le]
    exact hstsub)
  have hi₂ : IntervalIntegrable K volume t r := hi.mono_set (by
    rw [uIcc_of_le htr.le, uIcc_of_le (hst.trans htr).le]
    exact htrsub)
  intro heq
  have hc : (∫ a in s..t, K a) = ∫ a in s..r, K a :=
    Matrix.inv_inj heq (isUnit_iff_ne_zero.mpr hp₁.det_pos.ne')
  have hz : (∫ a in t..r, K a) = 0 := by
    apply add_left_cancel (a := ∫ a in s..t, K a)
    simpa only [add_zero] using
      (intervalIntegral.integral_add_adjacent_intervals hi₁ hi₂).trans hc.symm
  classical
  let i : n := Classical.choice inferInstance
  let v : n → ℝ := Pi.single i 1
  have hv : v ≠ 0 := by
    intro h
    have hh := congrFun h i
    simp [v] at hh
  have hp := hp₂.dotProduct_mulVec_pos hv
  rw [hz] at hp
  simp at hp

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {S : CalibratedLevelSeedPatch F u} {w : S.covector.ker} {μ ν : Measure ℝ}

namespace OriginalSeedConditionalMoments
variable (D : OriginalSeedConditionalMoments S w μ ν)
include D

/-- The actual Finsler coefficient distinguishes distinct target clocks in
the same original calibrated interior, including coincident spatial targets. -/
theorem pair_coefficient_right_injective_calibrationInterior
    (hF : F.IsSmoothStronglyConvex)
    (hu : let _inst : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (hw : w ∈ S.labels) (hdim : 0 < finrank ℝ S.covector.ker)
    {x y z : ℝ}
    (hx : x - S.level ∈ interior (S.calibrationTimes w))
    (hy : y - S.level ∈ interior (S.calibrationTimes w))
    (hz : z - S.level ∈ interior (S.calibrationTimes w))
    (hxy : x < y) (hxz : x < z) (hyz : y ≠ z) :
    originalSeedPairCoefficient S w (x, y) ≠ originalSeedPairCoefficient S w (x, z) := by
  classical
  let _inst : Nonempty (Fin (finrank ℝ S.covector.ker)) := ⟨⟨0, hdim⟩⟩
  have hK := D.original_kernel_regular_calibrationInterior hF hw
  have hinterval := original_calibrationInterior_ordConnected hF hu hw
  rcases lt_or_gt_of_ne hyz with h | h
  · exact inverse_intervalCompliance_right_ne_of_lt
      (sub_lt_sub_right hxy _) (sub_lt_sub_right h _)
      (hK.1.mono (hinterval.out hx hz))
      (fun a ha ↦ hK.2 a (hinterval.out hx hz ha))
  · exact (inverse_intervalCompliance_right_ne_of_lt
      (sub_lt_sub_right hxz _) (sub_lt_sub_right h _)
      (hK.1.mono (hinterval.out hx hy))
      (fun a ha ↦ hK.2 a (hinterval.out hx hy ha))).symm

end OriginalSeedConditionalMoments
end OTSelector.Reconstruction
