import OTSelector.Analysis.Calculus.Variational.EndpointComplianceUniform
import OTSelector.Geometry.FinslerTubeKernelCompliance

/-!
# Uniform bounds for the actual tube length coefficient

On a compact ordered endpoint set, the inverse of the time integral of the inverse
restricted length Hessians is continuous and has uniform positive quadratic bounds.
The coefficient uses one fixed genuine tube and the same original central curve.
-/

open Set Filter Manifold Bundle
open scoped Topology ContDiff NNReal

noncomputable section
namespace OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

set_option backward.isDefEq.respectTransparency false

variable {E W M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  [FiniteDimensional ℝ E] [FiniteDimensional ℝ W]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {F : ContinuousFinslerNorm E M}

/-- The actual restricted length coefficient is continuous and uniformly positive
on a compact ordered endpoint set in the same genuine tube. -/
theorem tubeLengthKernelCompliance_inverse_uniform_on_compact_endpoints
    (hF : F.IsSmoothStronglyConvex)
    {Y : OpenPartialHomeomorph (ℝ × W) M} {Λ : W → ℝ → M}
    (hY : ContMDiffOn 𝓘(ℝ, ℝ × W) 𝓘(ℝ, E) ∞ Y Y.source)
    (hi : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, ℝ × W) ∞ Y.symm Y.target)
    (heq : (Y : ℝ × W → M) = fun q ↦ Λ q.2 q.1)
    (hhalf : ∀ q ∈ Y.source,
      F.energy (tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (Λ q.2) ⟨q.1, (1 : ℝ)⟩) = 1 / 2)
    (t₀ : ℝ)
    (hbound : ∀ y ∈ Y.target, ∀ z : TangentSpace 𝓘(ℝ, E) y,
      @LE.le ℝ _ (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) (manifoldFlowTimePotential Y 1 t₀) y z)
        (F.toFun ⟨y, z⟩ : ℝ))
    {c : ℝ → M} {w : W} (hcentral : c = Λ w)
    {l r : ℝ} (hlr : l ≤ r)
    (hstay : ∀ t ∈ Icc l r, (t, w) ∈ Y.source)
    {T : Set (ℝ × ℝ)} (hT : IsCompact T)
    (hord : ∀ q ∈ T, l ≤ q.1 ∧ q.1 < q.2 ∧ q.2 ≤ r) :
    let p := ContinuousLinearMap.fst ℝ ℝ W
    let Q := fun q : ℝ × ℝ ↦ F.tubeLengthKernelCompliance Y p c q.1 q.2
    ContinuousOn (fun q ↦ (Q q).inverse) T ∧
      ∃ c₀ C₀ : ℝ, 0 < c₀ ∧ c₀ ≤ C₀ ∧
        ∀ q ∈ T, ∀ v : p.ker,
          c₀ * ‖v‖ ^ 2 ≤ (Q q).inverse v v ∧
          (Q q).inverse v v ≤ C₀ * ‖v‖ ^ 2 := by
  subst c
  let p := ContinuousLinearMap.fst ℝ ℝ W
  let v₀ : ℝ × W := (1, 0)
  let Q := fun q : ℝ × ℝ ↦ F.tubeLengthKernelCompliance Y p (Λ w) q.1 q.2
  let C := F.tubeInverseEnergyHessian Y (Λ w)
  let j := p.ker.subtypeL
  let R := (ContinuousLinearMap.compL ℝ p.ker (ℝ × W) ℝ).flip j
  change ContinuousOn (fun q ↦ (Q q).inverse) T ∧
    ∃ c₀ C₀ : ℝ, 0 < c₀ ∧ c₀ ≤ C₀ ∧
      ∀ q ∈ T, ∀ v : p.ker,
        c₀ * ‖v‖ ^ 2 ≤ (Q q).inverse v v ∧
        (Q q).inverse v v ≤ C₀ * ‖v‖ ^ 2
  have hphase (t : ℝ) (ht : t ∈ Icc l r) :
      ((Y.symm ∘ Λ w) t, deriv (Y.symm ∘ Λ w) t) = ((t, w), v₀) := by
    have hn : (fun s : ℝ ↦ (s, w)) ⁻¹' Y.source ∈ 𝓝 t :=
      (continuousAt_id.prodMk continuousAt_const).preimage_mem_nhds
        (Y.open_source.mem_nhds (hstay t ht))
    have he : (Y.symm ∘ Λ w) =ᶠ[𝓝 t] (fun s ↦ (s, w)) := by
      filter_upwards [hn] with s hs
      change Y.symm (Λ w s) = (s, w)
      rw [← congrFun heq (s, w)]
      exact Y.left_inv hs
    rw [he.eq_of_nhds, he.deriv_eq]
    congr 1
    exact (hasDerivAt_id t |>.prodMk (hasDerivAt_const t w)).deriv
  have hCeq (t : ℝ) (ht : t ∈ Icc l r) :
      C t = (verticalEnergyHessian (F.tubeCoordinateEnergy Y) ((t, w), v₀)).inverse := by
    dsimp only [C, tubeInverseEnergyHessian]
    rw [hphase t ht]
  have hC : ContinuousOn C (Icc l r) := by
    have hrad : ContinuousOn
        (fun t ↦ (verticalEnergyHessian (F.tubeCoordinateEnergy Y) ((t, w), v₀)).inverse)
        (Icc l r) :=
      (hF.contDiffOn_tubeInverseVerticalEnergyHessian hY hi).continuousOn.comp
        ((continuous_id.prodMk continuous_const).prodMk continuous_const).continuousOn
        (fun t ht ↦ ⟨hstay t ht, by simp [v₀]⟩)
    exact hrad.congr (fun t ht ↦ hCeq t ht)
  have hpos (t : ℝ) (ht : t ∈ Icc l r) (θ : (ℝ × W) →L[ℝ] ℝ) (hθ : θ ≠ 0) :
      0 < θ (C t θ) := by
    rw [hCeq t ht]
    exact inverse_verticalEnergyHessian_pos
      (fun u hu ↦ hF.tubeCoordinateEnergy_fiber_hessian_pos hY hi
        (hstay t ht) (by simp [v₀]) hu) hθ
  obtain ⟨hfull, c₀, C₀, hc₀, hc₀C₀, hbounds⟩ :=
    endpointCompliance_inverse_continuous_uniform_bounds hlr hC hpos hT hord
  have hrestriction (q : ℝ × ℝ) (hq : q ∈ T) :
      (Q q).inverse = R.comp ((endpointCompliance C q.1 q.2).inverse.comp j) := by
    apply ContinuousLinearMap.ext
    intro ξ
    apply ContinuousLinearMap.ext
    intro η
    have hqord := hord q hq
    have hsub : Icc q.1 q.2 ⊆ Icc l r := fun t ht ↦
      ⟨hqord.1.trans ht.1, ht.2.trans hqord.2.2⟩
    have hpair := hF.tubeEndpointCompliance_inverse_on_timeKernel hY hi heq hhalf
      t₀ hbound hqord.2.1 (fun t ht ↦ hstay t (hsub ht))
      (ξ : ℝ × W).2 (η : ℝ × W).2
    have hξ0 : (ξ : ℝ × W).1 = 0 := ξ.property
    have hη0 : (η : ℝ × W).1 = 0 := η.property
    have hξval : (0, (ξ : ℝ × W).2) = (ξ : ℝ × W) := Prod.ext hξ0.symm rfl
    have hηval : (0, (η : ℝ × W).2) = (η : ℝ × W) := Prod.ext hη0.symm rfl
    have hξ : (⟨(0, (ξ : ℝ × W).2), by simp [p]⟩ : p.ker) = ξ :=
      Subtype.ext hξval
    have hη : (⟨(0, (η : ℝ × W).2), by simp [p]⟩ : p.ker) = η :=
      Subtype.ext hηval
    change (Q q).inverse ξ η =
      (F.tubeEndpointCompliance Y (Λ w) q.1 q.2).inverse (ξ : ℝ × W) (η : ℝ × W)
    simpa only [Q, hξ, hη, hξval, hηval] using hpair.symm
  have hrestricted : ContinuousOn
      (fun q ↦ R.comp ((endpointCompliance C q.1 q.2).inverse.comp j)) T :=
    continuousOn_const.clm_comp (hfull.clm_comp continuousOn_const)
  refine ⟨hrestricted.congr hrestriction, c₀, C₀, hc₀, hc₀C₀, ?_⟩
  intro q hq v
  rw [hrestriction q hq]
  change c₀ * ‖(v : ℝ × W)‖ ^ 2 ≤
      (endpointCompliance C q.1 q.2).inverse (v : ℝ × W) (v : ℝ × W) ∧
    (endpointCompliance C q.1 q.2).inverse (v : ℝ × W) (v : ℝ × W) ≤
      C₀ * ‖(v : ℝ × W)‖ ^ 2
  exact hbounds q hq (v : ℝ × W)

end OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex
