import OTSelector.Geometry.Finsler.IntrinsicLabelHessian
import OTSelector.Geometry.FinslerSmoothPhaseJetData
import OTSelector.Geometry.FinslerPhaseJetHessianTransfer

/-!
# One intrinsic label Hessian along the complete comparison

The constructed comparison has a genuine nonzero joint time derivative at every
label and time. Each legal chart therefore computes the same intrinsic label Hessian.
Matching original phase jets identify the original matrix with this single matrix,
even when different endpoints use different local manifold charts.
-/

open Set Filter Matrix Module Manifold
open scoped Topology ContDiff

noncomputable section
namespace OTSelector.Geometry.ContinuousFinslerNorm.SmoothPhaseJetComparison

set_option backward.isDefEq.respectTransparency false

variable {E W M ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {F : ContinuousFinslerNorm E M}
  {initial : M} {t₀ : ℝ} {w₀ : W} {z₀ : E × (E →L[ℝ] ℝ)}
  {R : W →L[ℝ] E} {Q : W →L[ℝ] E →L[ℝ] ℝ}
  (C : F.SmoothPhaseJetComparison initial t₀ w₀ z₀ R Q)

/-- The comparison's actual joint position is differentiable at every allowed label and time. -/
theorem mdifferentiableAt_position {w : W} (hw : w ∈ C.labels) (t : ℝ) :
    MDifferentiableAt 𝓘(ℝ, W × ℝ) 𝓘(ℝ, E) (fun q ↦ C.curve q.1 q.2) (w, t) :=
  ((contMDiffOn_positionFamily_of_tangentFamily C.tangent_C2).contMDiffAt
    ((C.open_labels.prod isOpen_univ).mem_nhds ⟨hw, mem_univ _⟩)).mdifferentiableAt
      (by norm_num)

/-- The actual joint time derivative cannot vanish because the same curve has energy one half. -/
theorem position_time_mfderiv_ne_zero {w : W} (hw : w ∈ C.labels) (t : ℝ) :
    mfderiv 𝓘(ℝ, W × ℝ) 𝓘(ℝ, E) (fun q ↦ C.curve q.1 q.2) (w, t) (0, 1) ≠ 0 := by
  have hs : HasFDerivAt (fun s : ℝ ↦ (w, s)) (ContinuousLinearMap.inr ℝ W ℝ) t :=
    (hasFDerivAt_const w t).prodMk (hasFDerivAt_id t)
  have hD := mfderiv_comp t (C.mdifferentiableAt_position hw t)
    hs.differentiableAt.mdifferentiableAt
  rw [mfderiv_eq_fderiv, hs.fderiv] at hD
  have ht : mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (C.curve w) t 1 =
      mfderiv 𝓘(ℝ, W × ℝ) 𝓘(ℝ, E) (fun q ↦ C.curve q.1 q.2) (w, t) (0, 1) :=
    congrArg (fun L : ℝ →L[ℝ] TangentSpace 𝓘(ℝ, E) (C.curve w t) ↦ L 1) hD
  intro hzero
  have he := C.energy_eq w hw t
  change F.fiberEnergy (C.curve w t) (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (C.curve w) t 1) = 1 / 2 at he
  rw [ht, hzero, F.fiberEnergy_zero] at he
  norm_num at he

/-- Each legal chart computes the same chart-independent label Hessian along the comparison. -/
theorem chart_labelHessian_eq_intrinsic
    (hF : F.IsSmoothStronglyConvex) (old : M) (bW : Basis ι ℝ W)
    {w : W} (hw : w ∈ C.labels) (t : ℝ)
    (hx : C.curve w t ∈ (extChartAt 𝓘(ℝ, E) old).source) :
    F.chartFamilyLabelHessianMatrix old bW
      (fun q ↦ extChartAt 𝓘(ℝ, E) old (C.curve q.1 q.2)) (w, t) =
      F.familyLabelHessianMatrix bW (fun q ↦ C.curve q.1 q.2) (w, t) :=
  hF.chartFamilyLabelHessianMatrix_eq_intrinsic old bW
    (C.mdifferentiableAt_position hw t) hx (C.position_time_mfderiv_ne_zero hw t)

/-- The original rough family computes that same intrinsic comparison matrix whenever its
actual joint phase jet agrees, retaining the original label basis. -/
theorem original_labelHessian_eq_intrinsic
    (hF : F.IsSmoothStronglyConvex) (old : M) (bW : Basis ι ℝ W)
    {Γ : W → ℝ → M} (t : ℝ) (hcurve : Γ w₀ = C.curve w₀)
    (hx : Γ w₀ t ∈ (extChartAt 𝓘(ℝ, E) old).source)
    {D : (W × ℝ) →L[ℝ] E × (E →L[ℝ] ℝ)}
    (h₁ : HasFDerivAt (F.chartMomentumFamily old Γ) D (w₀, t))
    (h₂ : HasFDerivAt (F.chartMomentumFamily old C.curve) D (w₀, t)) :
    F.chartFamilyLabelHessianMatrix old bW
      (fun q ↦ extChartAt 𝓘(ℝ, E) old (Γ q.1 q.2)) (w₀, t) =
      F.familyLabelHessianMatrix bW (fun q ↦ C.curve q.1 q.2) (w₀, t) := by
  have hvalue := congrFun hcurve t
  exact (F.chartFamilyLabelHessianMatrix_eq_of_chartMomentum_same_firstJet old bW
    hvalue h₁ h₂).trans (C.chart_labelHessian_eq_intrinsic hF old bW C.anchor_mem t
      (hvalue ▸ hx))

end OTSelector.Geometry.ContinuousFinslerNorm.SmoothPhaseJetComparison
