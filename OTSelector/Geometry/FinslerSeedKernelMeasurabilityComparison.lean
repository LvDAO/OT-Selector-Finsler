import OTSelector.Geometry.Finsler.SeedKernelMeasurability
import OTSelector.Geometry.FinslerSeedActiveJacobian
import OTSelector.Geometry.FinslerIntrinsicKernelOriginal

/-!
# The measurable original seed kernel is the comparison kernel

Actual phase-jet matching identifies the jointly Borel original matrix with each
constructed comparison along its entire central curve. The original active-window
producer then supplies continuity and positive definiteness of that same kernel
for almost every label; no measurable comparison choice enters its definition.
-/

open Set Filter MeasureTheory Matrix Module Manifold
open scoped Topology ContDiff Matrix.Norms.Operator

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OTSelector.Geometry.ContinuousFinslerNorm.CalibratedLevelSeedPatch

variable {E M ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}

omit [FiniteDimensional ℝ E] [BorelSpace E] in
/-- Actual phase-jet agreement identifies the literal original intrinsic Hessian
with the same comparison at every original time. -/
theorem familyLabelHessianMatrix_eq_comparison (S : CalibratedLevelSeedPatch F u)
    (hF : F.IsSmoothStronglyConvex) (bW : Basis ι ℝ S.covector.ker)
    {w : S.covector.ker} (hw : w ∈ S.labels)
    {initial : M} {t₀ : ℝ} {z₀ : E × (E →L[ℝ] ℝ)}
    {R : S.covector.ker →L[ℝ] E} {Q : S.covector.ker →L[ℝ] E →L[ℝ] ℝ}
    (C : F.SmoothPhaseJetComparison initial t₀ w z₀ R Q)
    (hcurve : S.curve w = C.curve w)
    (hjet : ∀ old t, S.curve w t ∈ (extChartAt 𝓘(ℝ, E) old).source →
      HasFDerivAt (F.chartMomentumFamily old S.curve)
        (fderiv ℝ (F.chartMomentumFamily old C.curve) (w, t)) (w, t) ∧
      HasFDerivAt (F.chartMomentumFamily old C.curve)
        (fderiv ℝ (F.chartMomentumFamily old C.curve) (w, t)) (w, t))
    (t : ℝ) :
    F.familyLabelHessianMatrix bW (fun q ↦ S.curve q.1 q.2) (w, t) =
      F.familyLabelHessianMatrix bW (fun q ↦ C.curve q.1 q.2) (w, t) := by
  let old := S.curve w t
  have hx : S.curve w t ∈ (extChartAt 𝓘(ℝ, E) old).source := mem_extChartAt_source _
  obtain ⟨h₁, h₂⟩ := hjet old t hx
  exact (S.chart_labelHessian_eq_intrinsic hF old bW hw hx).symm.trans
    (C.original_labelHessian_eq_intrinsic hF old bW t hcurve hx h₁ h₂)

variable [Fintype ι] [DecidableEq ι]

omit [FiniteDimensional ℝ E] [BorelSpace E] in
/-- The jointly measurable original inverse matrix equals the comparison kernel
at every original time, without any choice of a time-dependent coordinate frame. -/
theorem familyLabelKernel_eq_comparison (S : CalibratedLevelSeedPatch F u)
    (hF : F.IsSmoothStronglyConvex) (bW : Basis ι ℝ S.covector.ker)
    {w : S.covector.ker} (hw : w ∈ S.labels)
    {initial : M} {t₀ : ℝ} {z₀ : E × (E →L[ℝ] ℝ)}
    {R : S.covector.ker →L[ℝ] E} {Q : S.covector.ker →L[ℝ] E →L[ℝ] ℝ}
    (C : F.SmoothPhaseJetComparison initial t₀ w z₀ R Q)
    (hcurve : S.curve w = C.curve w)
    (hjet : ∀ old t, S.curve w t ∈ (extChartAt 𝓘(ℝ, E) old).source →
      HasFDerivAt (F.chartMomentumFamily old S.curve)
        (fderiv ℝ (F.chartMomentumFamily old C.curve) (w, t)) (w, t) ∧
      HasFDerivAt (F.chartMomentumFamily old C.curve)
        (fderiv ℝ (F.chartMomentumFamily old C.curve) (w, t)) (w, t))
    (t : ℝ) :
    (F.familyLabelHessianMatrix bW (fun q ↦ S.curve q.1 q.2) (w, t))⁻¹ =
      C.intrinsicKernel bW t :=
  congrArg Inv.inv (S.familyLabelHessianMatrix_eq_comparison hF bW hw C hcurve hjet t)

/-- Almost every original label has a continuous positive definite original
kernel throughout its full active interval. All rank facts come from the original
calibration-window producer. -/
theorem ae_continuousOn_posDef_familyLabelKernel [T2Space M] [PreconnectedSpace M]
    (S : CalibratedLevelSeedPatch F u) (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _instSeedKernelLip : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (m : Measure S.covector.ker) [m.IsAddHaarMeasure]
    (bW : Basis ι ℝ S.covector.ker) :
    ∀ᵐ w ∂m.restrict S.labels,
      let K := fun t ↦
        (F.familyLabelHessianMatrix bW (fun q ↦ S.curve q.1 q.2) (w, t))⁻¹
      ContinuousOn K (interior (S.calibrationTimes w)) ∧
        ∀ t ∈ interior (S.calibrationTimes w), (K t).PosDef := by
  filter_upwards [S.ae_exists_comparison_active_jacobian S.c11Data hF hcomplete hu m]
    with w hwdata
  obtain ⟨hw, C, _, hcurve, hjet, hpos⟩ := hwdata
  have heq : (fun t ↦
      (F.familyLabelHessianMatrix bW (fun q ↦ S.curve q.1 q.2) (w, t))⁻¹) =
      C.intrinsicKernel bW :=
    funext (S.familyLabelKernel_eq_comparison hF bW hw C hcurve hjet)
  obtain ⟨hc, hp⟩ := C.continuousOn_posDef_intrinsicKernel_of_original
    hF bW S.normalization hcurve (fun old t _ hx ↦ hjet old t hx) hpos
  refine ⟨hc.congr (fun t _ ↦ congrFun heq t), ?_⟩
  intro t ht
  dsimp only
  rw [congrFun heq t]
  exact hp t ht

end OTSelector.Geometry.ContinuousFinslerNorm.CalibratedLevelSeedPatch
