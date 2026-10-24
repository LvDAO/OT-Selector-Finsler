import OTSelector.Geometry.FinslerIntrinsicKernelRegularity

/-!
# The original family and one intrinsic comparison kernel

Actual joint phase jets identify the original chart Hessian with the same intrinsic
comparison Hessian. Original physical Jacobian positivity therefore gives continuity
and positive definiteness of that single kernel throughout the active time set.
-/

open Set Matrix Module Manifold
open scoped Topology ContDiff Matrix.Norms.Operator

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OTSelector.Geometry.ContinuousFinslerNorm.SmoothPhaseJetComparison

variable {E W M ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup W] [NormedSpace ℝ W]
  [Fintype ι] [DecidableEq ι]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {F : ContinuousFinslerNorm E M}
  {initial : M} {t₀ : ℝ} {w₀ : W} {z₀ : E × (E →L[ℝ] ℝ)}
  {R : W →L[ℝ] E} {Q : W →L[ℝ] E →L[ℝ] ℝ}
  (C : F.SmoothPhaseJetComparison initial t₀ w₀ z₀ R Q)

omit [FiniteDimensional ℝ E] in
/-- The inverse original label Hessian in any legal chart is the same intrinsic kernel. -/
theorem original_intrinsicKernel_eq
    (hF : F.IsSmoothStronglyConvex) (old : M) (bW : Basis ι ℝ W)
    {Γ : W → ℝ → M} (t : ℝ) (hcurve : Γ w₀ = C.curve w₀)
    (hx : Γ w₀ t ∈ (extChartAt 𝓘(ℝ, E) old).source)
    {D : (W × ℝ) →L[ℝ] E × (E →L[ℝ] ℝ)}
    (h₁ : HasFDerivAt (F.chartMomentumFamily old Γ) D (w₀, t))
    (h₂ : HasFDerivAt (F.chartMomentumFamily old C.curve) D (w₀, t)) :
    (F.chartFamilyLabelHessianMatrix old bW
      (fun q ↦ extChartAt 𝓘(ℝ, E) old (Γ q.1 q.2)) (w₀, t))⁻¹ =
      C.intrinsicKernel bW t :=
  congrArg Inv.inv (C.original_labelHessian_eq_intrinsic hF old bW t hcurve hx h₁ h₂)

omit [FiniteDimensional ℝ E] [Fintype ι] [DecidableEq ι] in
/-- At a differentiable original joint position, the literal intrinsic Hessian also
agrees with the comparison; its nonzero time derivative follows from their same curve. -/
theorem original_familyLabelHessian_eq_intrinsic
    (hF : F.IsSmoothStronglyConvex) (old : M) (bW : Basis ι ℝ W)
    {Γ : W → ℝ → M} (t : ℝ) (hcurve : Γ w₀ = C.curve w₀)
    (hx : Γ w₀ t ∈ (extChartAt 𝓘(ℝ, E) old).source)
    (hΓ : MDifferentiableAt 𝓘(ℝ, W × ℝ) 𝓘(ℝ, E)
      (fun q ↦ Γ q.1 q.2) (w₀, t))
    {D : (W × ℝ) →L[ℝ] E × (E →L[ℝ] ℝ)}
    (h₁ : HasFDerivAt (F.chartMomentumFamily old Γ) D (w₀, t))
    (h₂ : HasFDerivAt (F.chartMomentumFamily old C.curve) D (w₀, t)) :
    F.familyLabelHessianMatrix bW (fun q ↦ Γ q.1 q.2) (w₀, t) =
      F.familyLabelHessianMatrix bW (fun q ↦ C.curve q.1 q.2) (w₀, t) := by
  have hs : HasFDerivAt (fun s : ℝ ↦ (w₀, s)) (ContinuousLinearMap.inr ℝ W ℝ) t :=
    (hasFDerivAt_const w₀ t).prodMk (hasFDerivAt_id t)
  have hD := mfderiv_comp t hΓ hs.differentiableAt.mdifferentiableAt
  rw [mfderiv_eq_fderiv, hs.fderiv] at hD
  have ht : mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (Γ w₀) t 1 =
      mfderiv 𝓘(ℝ, W × ℝ) 𝓘(ℝ, E) (fun q ↦ Γ q.1 q.2) (w₀, t) (0, 1) :=
    congrArg (fun L : ℝ →L[ℝ] TangentSpace 𝓘(ℝ, E) (Γ w₀ t) ↦ L 1) hD
  have hv : mfderiv 𝓘(ℝ, W × ℝ) 𝓘(ℝ, E) (fun q ↦ Γ q.1 q.2)
      (w₀, t) (0, 1) ≠ 0 := by
    intro hz
    have he := C.energy_eq w₀ C.anchor_mem t
    change F.fiberEnergy (C.curve w₀ t) (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (C.curve w₀) t 1) = 1 / 2 at he
    rw [← hcurve, ht, hz, F.fiberEnergy_zero] at he
    norm_num at he
  exact (hF.chartFamilyLabelHessianMatrix_eq_intrinsic old bW hΓ hx hv).symm.trans
    (C.original_labelHessian_eq_intrinsic hF old bW t hcurve hx h₁ h₂)

/-- Original phase-jet agreement and original physical Jacobian positivity supply
all regularity and positivity of the one intrinsic kernel, without a new rank input. -/
theorem continuousOn_posDef_intrinsicKernel_of_original
    (hF : F.IsSmoothStronglyConvex) (bW : Basis ι ℝ W) (ℓ : (ℝ × W) ≃L[ℝ] E)
    {Γ : W → ℝ → M} {I : Set ℝ} (hcurve : Γ w₀ = C.curve w₀)
    (hjet : ∀ old t, t ∈ I → Γ w₀ t ∈ (extChartAt 𝓘(ℝ, E) old).source →
      HasFDerivAt (F.chartMomentumFamily old Γ)
        (fderiv ℝ (F.chartMomentumFamily old C.curve) (w₀, t)) (w₀, t) ∧
      HasFDerivAt (F.chartMomentumFamily old C.curve)
        (fderiv ℝ (F.chartMomentumFamily old C.curve) (w₀, t)) (w₀, t))
    (hpos : ∀ old t, t ∈ I → Γ w₀ t ∈ (extChartAt 𝓘(ℝ, E) old).source →
      0 < parameterizedJacobian
        (fun q : ℝ × W ↦ extChartAt 𝓘(ℝ, E) old (Γ q.2 q.1)) ℓ (t, w₀)) :
    ContinuousOn (C.intrinsicKernel bW) I ∧ ∀ t ∈ I, (C.intrinsicKernel bW t).PosDef := by
  apply C.continuousOn_posDef_intrinsicKernel hF bW ℓ
  intro old t ht hx
  have hx' : Γ w₀ t ∈ (extChartAt 𝓘(ℝ, E) old).source := by rwa [hcurve]
  obtain ⟨h₁, h₂⟩ := hjet old t ht hx'
  rw [← F.parameterizedJacobian_eq_of_chartMomentum_same_firstJet old h₁ h₂ ℓ]
  exact hpos old t ht hx'

/-- Any legal selection of original manifold charts reads the very same continuous
positive definite kernel; no regularity of the chart-selection function is needed. -/
theorem continuousOn_posDef_original_inverseHessian
    (hF : F.IsSmoothStronglyConvex) (bW : Basis ι ℝ W) (ℓ : (ℝ × W) ≃L[ℝ] E)
    {Γ : W → ℝ → M} {I : Set ℝ} (hcurve : Γ w₀ = C.curve w₀)
    (hjet : ∀ old t, t ∈ I → Γ w₀ t ∈ (extChartAt 𝓘(ℝ, E) old).source →
      HasFDerivAt (F.chartMomentumFamily old Γ)
        (fderiv ℝ (F.chartMomentumFamily old C.curve) (w₀, t)) (w₀, t) ∧
      HasFDerivAt (F.chartMomentumFamily old C.curve)
        (fderiv ℝ (F.chartMomentumFamily old C.curve) (w₀, t)) (w₀, t))
    (hpos : ∀ old t, t ∈ I → Γ w₀ t ∈ (extChartAt 𝓘(ℝ, E) old).source →
      0 < parameterizedJacobian
        (fun q : ℝ × W ↦ extChartAt 𝓘(ℝ, E) old (Γ q.2 q.1)) ℓ (t, w₀))
    (old : ℝ → M) (hlegal : ∀ t ∈ I, Γ w₀ t ∈ (extChartAt 𝓘(ℝ, E) (old t)).source) :
    let K := fun t ↦ (F.chartFamilyLabelHessianMatrix (old t) bW
      (fun q ↦ extChartAt 𝓘(ℝ, E) (old t) (Γ q.1 q.2)) (w₀, t))⁻¹
    EqOn K (C.intrinsicKernel bW) I ∧ ContinuousOn K I ∧ ∀ t ∈ I, (K t).PosDef := by
  dsimp only
  have heq : EqOn (fun t ↦ (F.chartFamilyLabelHessianMatrix (old t) bW
      (fun q ↦ extChartAt 𝓘(ℝ, E) (old t) (Γ q.1 q.2)) (w₀, t))⁻¹)
      (C.intrinsicKernel bW) I := by
    intro t ht
    obtain ⟨h₁, h₂⟩ := hjet (old t) t ht (hlegal t ht)
    exact C.original_intrinsicKernel_eq hF (old t) bW t hcurve (hlegal t ht) h₁ h₂
  obtain ⟨hc, hp⟩ := C.continuousOn_posDef_intrinsicKernel_of_original hF bW ℓ
    hcurve hjet hpos
  refine ⟨heq, hc.congr heq, ?_⟩
  intro t ht
  have hh := hp t ht
  rw [← heq ht] at hh
  exact hh

end OTSelector.Geometry.ContinuousFinslerNorm.SmoothPhaseJetComparison
