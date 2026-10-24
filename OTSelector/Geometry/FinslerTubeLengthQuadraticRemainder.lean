import OTSelector.Geometry.FinslerSelectedTubeQuadratic
import OTSelector.Geometry.FinslerQuadraticCoefficients
import Mathlib.Analysis.Asymptotics.Lemmas

/-!
# Actual length-response remainder in the selected calibrated tube

The same selected tube has a cubic distance remainder with its integrated
restricted-length coefficient. Consequently the actual distance deficit has
this coefficient as its quadratic expansion at every central label.
-/

open Set Filter Metric Manifold Bundle Asymptotics
open scoped Topology ContDiff

noncomputable section
namespace OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

set_option backward.isDefEq.respectTransparency false

variable {E W M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  [FiniteDimensional ℝ E] [FiniteDimensional ℝ W]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] {F : ContinuousFinslerNorm E M}

/-- The actual integrated restricted-length quadratic coefficient has a cubic
remainder for the original distance in the same selected tube at any central label. -/
theorem exists_selected_tube_lengthQuadratic_remainder
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    {Y : OpenPartialHomeomorph (ℝ × W) M} {Λ : W → ℝ → M}
    (hY : ContMDiffOn 𝓘(ℝ, ℝ × W) 𝓘(ℝ, E) ∞ Y Y.source)
    (hi : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, ℝ × W) ∞ Y.symm Y.target)
    (heq : (Y : ℝ × W → M) = fun q ↦ Λ q.2 q.1)
    (hhalf : ∀ q ∈ Y.source,
      F.energy (tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (Λ q.2) ⟨q.1, (1 : ℝ)⟩) = 1 / 2)
    (t₀ : ℝ)
    (hbound : ∀ x ∈ Y.target, ∀ v : TangentSpace 𝓘(ℝ, E) x,
      @LE.le ℝ _ (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) (manifoldFlowTimePotential Y 1 t₀) x v)
        (F.toFun ⟨x, v⟩ : ℝ))
    {a b : ℝ} (hab : a < b) {v : W}
    (hΛ : F.IsEulerLagrangeOn (Λ v) univ)
    (hstay : ∀ t ∈ Icc a b, (t, v) ∈ Y.source)
    (hmin : letI : ∀ x : M, ENorm (TangentSpace 𝓘(ℝ, E) x) := F.enorm
      F.lengthEDist (Λ v a) (Λ v b) = Manifold.pathELength 𝓘(ℝ, E) (Λ v) a b)
    {u : M → ℝ} (hu : letI : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (hsat : letI : MetricSpace M := F.metricSpace
      u (Λ v b) - u (Λ v a) = dist (Λ v a) (Λ v b))
    (hdu : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ) u (Λ v a)) :
    ∃ r > 0, ∃ C ≥ 0, ∀ w : W × W, ‖w‖ ≤ r →
      ‖(F.lengthEDist (Λ (v + w.1) a) (Λ (v + w.2) b)).toReal - (b - a) -
        F.tubeLengthQuadratic Y (Λ v) a b w‖ ≤ C * ‖w‖ ^ 3 := by
  obtain ⟨r, hr, C, hC, hrem⟩ :=
    hF.exists_selected_tube_distance_quadratic_remainder
      hcomplete hY hi heq hhalf t₀ hbound hab hΛ hstay hmin hu hsat hdu
  refine ⟨r, hr, C, hC, ?_⟩
  intro w hw
  rw [hF.tubeLengthQuadratic_eq_endpointCompliance hY hi heq hhalf t₀ hbound hab hstay w]
  exact hrem w.1 w.2 hw

/-- The actual distance deficit in the selected tube differs from its integrated
restricted-length quadratic coefficient by a second-order little-o at zero. -/
theorem selected_tube_distance_sub_lengthQuadratic_isLittleO
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    {Y : OpenPartialHomeomorph (ℝ × W) M} {Λ : W → ℝ → M}
    (hY : ContMDiffOn 𝓘(ℝ, ℝ × W) 𝓘(ℝ, E) ∞ Y Y.source)
    (hi : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, ℝ × W) ∞ Y.symm Y.target)
    (heq : (Y : ℝ × W → M) = fun q ↦ Λ q.2 q.1)
    (hhalf : ∀ q ∈ Y.source,
      F.energy (tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (Λ q.2) ⟨q.1, (1 : ℝ)⟩) = 1 / 2)
    (t₀ : ℝ)
    (hbound : ∀ x ∈ Y.target, ∀ v : TangentSpace 𝓘(ℝ, E) x,
      @LE.le ℝ _ (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) (manifoldFlowTimePotential Y 1 t₀) x v)
        (F.toFun ⟨x, v⟩ : ℝ))
    {a b : ℝ} (hab : a < b) {v : W}
    (hΛ : F.IsEulerLagrangeOn (Λ v) univ)
    (hstay : ∀ t ∈ Icc a b, (t, v) ∈ Y.source)
    (hmin : letI : ∀ x : M, ENorm (TangentSpace 𝓘(ℝ, E) x) := F.enorm
      F.lengthEDist (Λ v a) (Λ v b) = Manifold.pathELength 𝓘(ℝ, E) (Λ v) a b)
    {u : M → ℝ} (hu : letI : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (hsat : letI : MetricSpace M := F.metricSpace
      u (Λ v b) - u (Λ v a) = dist (Λ v a) (Λ v b))
    (hdu : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ) u (Λ v a)) :
    (fun w : W × W ↦
      (F.lengthEDist (Λ (v + w.1) a) (Λ (v + w.2) b)).toReal - (b - a) -
        F.tubeLengthQuadratic Y (Λ v) a b w) =o[𝓝 (0 : W × W)] fun w ↦ ‖w‖ ^ 2 := by
  obtain ⟨r, hr, C, _, hrem⟩ := hF.exists_selected_tube_lengthQuadratic_remainder
    hcomplete hY hi heq hhalf t₀ hbound hab hΛ hstay hmin hu hsat hdu
  have hbig : (fun w : W × W ↦
      (F.lengthEDist (Λ (v + w.1) a) (Λ (v + w.2) b)).toReal - (b - a) -
        F.tubeLengthQuadratic Y (Λ v) a b w)
      =O[𝓝 (0 : W × W)] fun w ↦ ‖w‖ ^ 3 := by
    apply IsBigO.of_bound C
    filter_upwards [Metric.closedBall_mem_nhds (0 : W × W) hr] with w hw
    have hnorm : ‖w‖ ≤ r := by
      simpa only [Metric.mem_closedBall, dist_zero_right] using hw
    simpa only [Real.norm_of_nonneg (pow_nonneg (norm_nonneg w) 3)] using hrem w hnorm
  exact hbig.trans_isLittleO
    (isLittleO_norm_pow_norm_pow (E' := W × W) (m := 2) (n := 3) (by decide))

end OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex
