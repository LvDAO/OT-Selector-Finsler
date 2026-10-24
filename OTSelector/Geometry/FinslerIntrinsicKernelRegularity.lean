import OTSelector.Geometry.Finsler.Hamiltonian.LengthHessianRegularity
import OTSelector.Geometry.FinslerComparisonGraphKernel
import OTSelector.Geometry.Finsler.PositionJacobianRank
import Mathlib.Topology.Instances.Matrix

/-!
# Geometry.Finsler.Hamiltonian.LengthHessianRegularity

* **Conditions:** Smooth strong convexity and a nonzero actual chart phase.
* **Objects:** Smooth dependence of the true fiber length Hessian on the original base and velocity.
* **Proof detail:** Differentiate the original slit-smooth length twice in velocity using joint smoothness and the chain rule.

Mathematical sources:
- [Zhongmin Shen, Landsberg Curvature, S-Curvature and Riemann Curvature, MSRI Publications 50 (2004)](https://library.slmath.org/books/Book50/files/08Sh.pdf#page=2): Section 2, pp. 304–305: positive homogeneity, slit smoothness, positive fundamental tensor gy=½∂²F² and F(y)²=gy(y,y).
- [Jiří Lebl, Basic Analysis II: Introduction to Real Analysis, Volume II](https://www.jirka.org/ra/realanal2.pdf): Sections 8.3–8.4, total derivative, chain rule and mean-value bounds; Section 8.6, higher derivatives.

Source relation (derived): Only this generic smoothness lemma is selected; the original intrinsic kernel positivity/continuity results are not added to this core.
-/

/-!
# Regularity of the actual intrinsic label kernel

The smooth comparison's true length Hessian varies continuously in any legal
chart, and chart independence gives one matrix along the original time interval.
Actual momentum normality and positive physical Jacobian make this matrix positive
definite; its inverse is therefore a continuous positive definite kernel.
-/

open Set Filter Matrix Module Manifold
open scoped Topology ContDiff Matrix.Norms.Operator

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OTSelector.Geometry

variable {E W ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup W] [NormedSpace ℝ W]

/-- A positive normalized Jacobian forces injectivity of the actual derivative. -/
theorem injective_fderiv_of_parameterizedJacobian_pos [FiniteDimensional ℝ E]
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {f : V → E} (ℓ : V ≃L[ℝ] E) {q : V}
    (h : 0 < parameterizedJacobian f ℓ q) : Function.Injective (fderiv ℝ f q) := by
  have hn : ((fderiv ℝ f q).comp ℓ.symm.toContinuousLinearMap).det ≠ 0 := abs_pos.mp h
  have hi : Function.Injective ((fderiv ℝ f q).comp ℓ.symm.toContinuousLinearMap) :=
    LinearMap.ker_eq_bot.mp (not_not.mp (mt LinearMap.det_eq_zero_iff_ker_ne_bot.mpr hn))
  intro x y hxy
  have hh : ℓ x = ℓ y := hi (by simpa using hxy)
  exact ℓ.injective hh

/-- A symmetric positive continuous bilinear form has a positive definite basis matrix. -/
theorem hamiltonianMatrixA_posDef [Fintype ι] (b : Basis ι ℝ W)
    {H : W →L[ℝ] W →L[ℝ] ℝ}
    (hsym : ∀ u v, H u v = H v u)
    (hpos : ∀ v : W, v ≠ 0 → 0 < H v v) : (hamiltonianMatrixA b H).PosDef := by
  classical
  apply Matrix.PosDef.of_dotProduct_mulVec_pos
  · simpa only [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial] using
      hamiltonianMatrixA_transpose b hsym
  intro x hx
  let v : W := ∑ j, x j • b j
  have hv : v ≠ 0 := by
    intro hz
    apply hx
    have hh := congrArg b.equivFun hz
    simpa only [v, ← b.equivFun_symm_apply, b.equivFun.apply_symm_apply, map_zero] using hh
  have he : star x ⬝ᵥ (hamiltonianMatrixA b H *ᵥ x) = H v v := by
    simp only [dotProduct, Matrix.mulVec, Pi.star_apply, star_trivial,
      hamiltonianMatrixA, v, map_sum, _root_.sum_apply, _root_.map_smul,
      _root_.smul_apply, smul_eq_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    rw [hsym (b i) (b j)]
    ring
  rw [he]
  exact hpos v hv

namespace ContinuousFinslerNorm.IsSmoothStronglyConvex

variable {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] {F : ContinuousFinslerNorm E M}



/-- Reading the true fiber Hessian on a C² position family gives a continuous matrix. -/
theorem continuousAt_chartFamilyLabelHessianMatrix (hF : F.IsSmoothStronglyConvex)
    (old : M) (bW : Basis ι ℝ W) {x : W × ℝ → E} {q : W × ℝ}
    (hx : ContDiffAt ℝ 2 x q)
    (hz : (x q, fderiv ℝ x q (0, 1)) ∈ chartEnergyDomain old) :
    ContinuousAt (F.chartFamilyLabelHessianMatrix old bW x) q := by
  have hD : ContinuousAt (fderiv ℝ x) q :=
    (hx.fderiv_right (m := 1) (by norm_num)).continuousAt
  have hstate : ContinuousAt (fun p ↦ (x p, fderiv ℝ x p (0, 1))) q :=
    hx.continuousAt.prodMk (hD.clm_apply continuousAt_const)
  have hH : ContinuousAt (fun p : W × ℝ ↦
      fderiv ℝ (fderiv ℝ (fun v ↦ (F.chartLength old (x p, v) : ℝ)))
        (fderiv ℝ x p (0, 1))) q :=
    (hF.contDiffAt_chartLength_fiberHessian old hz).continuousAt.comp
      (f := fun p : W × ℝ ↦ (x p, fderiv ℝ x p (0, 1))) hstate
  apply continuousAt_pi.mpr
  intro i
  apply continuousAt_pi.mpr
  intro j
  exact (hH.clm_apply (hD.clm_apply continuousAt_const)).clm_apply
    (hD.clm_apply continuousAt_const)

end ContinuousFinslerNorm.IsSmoothStronglyConvex

namespace ContinuousFinslerNorm.SmoothPhaseJetComparison

variable {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [FiniteDimensional ℝ E]
  {F : ContinuousFinslerNorm E M}
  {initial : M} {t₀ : ℝ} {w₀ : W} {z₀ : E × (E →L[ℝ] ℝ)}
  {R : W →L[ℝ] E} {Q : W →L[ℝ] E →L[ℝ] ℝ}
  (C : F.SmoothPhaseJetComparison initial t₀ w₀ z₀ R Q)

/-- The intrinsic label Hessian is continuous along the entire actual comparison. -/
theorem continuousAt_labelHessian (hF : F.IsSmoothStronglyConvex)
    (bW : Basis ι ℝ W) (t : ℝ) :
    ContinuousAt (fun r ↦ F.familyLabelHessianMatrix bW
      (fun q ↦ C.curve q.1 q.2) (w₀, r)) t := by
  let old := C.curve w₀ t
  have hx : C.curve w₀ t ∈ (extChartAt 𝓘(ℝ, E) old).source := mem_extChartAt_source old
  have hC2 : ContDiffAt ℝ 2 (C.chartReadout old) (w₀, t) :=
    (hF.contDiffAt_chartMomentumFamily_of_tangentFamily C.open_labels
      C.complete C.tangent_C2 C.anchor_mem old t hx).fst
  have ht : deriv (extChartAt 𝓘(ℝ, E) old ∘ C.curve w₀) t =
      fderiv ℝ (C.chartReadout old) (w₀, t) (0, 1) :=
    (hC2.differentiableAt (by norm_num)).hasFDerivAt.comp_hasDerivAt t
      ((hasDerivAt_const t w₀).prodMk (hasDerivAt_id t)) |>.deriv
  have hz := (hF.chartTangent_of_isEulerLagrangeAt
    (C.complete w₀ C.anchor_mem t (mem_univ _)) old hx).2
  rw [ht] at hz
  have hH := (hF.continuousAt_chartFamilyLabelHessianMatrix old bW hC2 hz).comp
    (f := fun r : ℝ ↦ (w₀, r)) (continuousAt_const.prodMk continuousAt_id)
  have hcurve : ContinuousAt (C.curve w₀) t :=
    (C.mdifferentiableAt_position C.anchor_mem t).continuousAt.comp
      (f := fun r : ℝ ↦ (w₀, r)) (continuousAt_const.prodMk continuousAt_id)
  have hlegal : ∀ᶠ r in 𝓝 t, C.curve w₀ r ∈ (extChartAt 𝓘(ℝ, E) old).source :=
    hcurve.eventually ((isOpen_extChartAt_source old).mem_nhds hx)
  apply hH.congr_of_eventuallyEq
  filter_upwards [hlegal] with r hr
  exact (C.chart_labelHessian_eq_intrinsic hF old bW C.anchor_mem r hr).symm

variable [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
/-- Positive actual physical Jacobian and the comparison's actual normality give
positive definiteness of the intrinsic length Hessian in the fixed label basis. -/
theorem labelHessian_posDef_of_jacobian_pos (hF : F.IsSmoothStronglyConvex)
    (bW : Basis ι ℝ W) (ℓ : (ℝ × W) ≃L[ℝ] E) (old : M) (t : ℝ)
    (hx : C.curve w₀ t ∈ (extChartAt 𝓘(ℝ, E) old).source)
    (hpos : 0 < parameterizedJacobian
      (fun q : ℝ × W ↦ extChartAt 𝓘(ℝ, E) old (C.curve q.2 q.1)) ℓ (t, w₀)) :
    (F.familyLabelHessianMatrix bW (fun q ↦ C.curve q.1 q.2) (w₀, t)).PosDef := by
  let x := C.chartReadout old
  let T := fderiv ℝ x (w₀, t)
  let L := T.comp (ContinuousLinearMap.inl ℝ W ℝ)
  let H := fderiv ℝ (fderiv ℝ (fun v ↦ (F.chartLength old (x (w₀, t), v) : ℝ)))
    (T (0, 1))
  have hd : DifferentiableAt ℝ x (w₀, t) :=
    (hF.contDiffAt_chartMomentumFamily_of_tangentFamily C.open_labels
      C.complete C.tangent_C2 C.anchor_mem old t hx).fst.differentiableAt (by norm_num)
  have htime : deriv (extChartAt 𝓘(ℝ, E) old ∘ C.curve w₀) t = T (0, 1) :=
    (hd.hasFDerivAt.comp_hasDerivAt t
      ((hasDerivAt_const t w₀).prodMk (hasDerivAt_id t))).deriv
  have hlabel : fderiv ℝ (fun w ↦ extChartAt 𝓘(ℝ, E) old (C.curve w t)) w₀ = L := by
    have hline : HasFDerivAt (fun w : W ↦ (w, t)) (ContinuousLinearMap.inl ℝ W ℝ) w₀ :=
      (hasFDerivAt_id (𝕜 := ℝ) w₀).prodMk (hasFDerivAt_const t w₀)
    have hh := hd.hasFDerivAt.comp w₀ hline
    exact hh.fderiv
  let swap := ContinuousLinearEquiv.prodComm ℝ ℝ W
  have hswap : fderiv ℝ (fun q : ℝ × W ↦ x (q.2, q.1)) (t, w₀) =
      T.comp swap.toContinuousLinearMap :=
    by
      have hh := hd.hasFDerivAt.comp (t, w₀) swap.hasFDerivAt
      exact hh.fderiv
  have hinj := injective_fderiv_of_parameterizedJacobian_pos ℓ hpos
  change Function.Injective (fderiv ℝ (fun q : ℝ × W ↦ x (q.2, q.1)) (t, w₀)) at hinj
  rw [hswap] at hinj
  have hLi : Function.Injective L := by
    intro ξ η heq
    have hh : ((0 : ℝ), ξ) = (0, η) := @hinj (0, ξ) (0, η)
      (show T (ξ, 0) = T (η, 0) from heq)
    exact congrArg Prod.snd hh
  have hz := (hF.chartTangent_of_isEulerLagrangeAt
    (C.complete w₀ C.anchor_mem t (mem_univ _)) old hx).2
  rw [htime] at hz
  have hnormal (ξ : W) : fiberLegendre (F.chartEnergy old) (x (w₀, t), T (0, 1))
      (L ξ) = 0 := by
    have hh := C.normal old t hx ξ
    rw [hlabel] at hh
    change fiberLegendre (F.chartEnergy old)
      ((extChartAt 𝓘(ℝ, E) old ∘ C.curve w₀) t,
        deriv (extChartAt 𝓘(ℝ, E) old ∘ C.curve w₀) t) (L ξ) = 0 at hh
    rwa [htime] at hh
  have hHpos : (hamiltonianMatrixA bW (H.bilinearComp L L)).PosDef :=
    hamiltonianMatrixA_posDef bW
      (fun ξ η ↦ hF.chartLength_hessian_symm old hz (L ξ) (L η))
      (fun ξ hξ ↦ hF.chartLength_hessian_pos_on_momentum_ker old hz
        (fun heq ↦ hξ (hLi (heq.trans (L.map_zero).symm))) (hnormal ξ))
  rw [← C.chart_labelHessian_eq_intrinsic hF old bW C.anchor_mem t hx]
  exact hHpos

/-- The intrinsic kernel uses the same fixed label basis and the original time. -/
def intrinsicKernel (bW : Basis ι ℝ W) (t : ℝ) : Matrix ι ι ℝ :=
  (F.familyLabelHessianMatrix bW (fun q ↦ C.curve q.1 q.2) (w₀, t))⁻¹

/-- On every set where the actual physical Jacobian is positive, the single intrinsic
kernel is continuous and positive definite, with no choice of a global graph chart. -/
theorem continuousOn_posDef_intrinsicKernel (hF : F.IsSmoothStronglyConvex)
    (bW : Basis ι ℝ W) (ℓ : (ℝ × W) ≃L[ℝ] E) {I : Set ℝ}
    (hpos : ∀ old t, t ∈ I → C.curve w₀ t ∈ (extChartAt 𝓘(ℝ, E) old).source →
      0 < parameterizedJacobian
        (fun q : ℝ × W ↦ extChartAt 𝓘(ℝ, E) old (C.curve q.2 q.1)) ℓ (t, w₀)) :
    ContinuousOn (C.intrinsicKernel bW) I ∧ ∀ t ∈ I, (C.intrinsicKernel bW t).PosDef := by
  have hp (t : ℝ) (ht : t ∈ I) :
      (F.familyLabelHessianMatrix bW (fun q ↦ C.curve q.1 q.2) (w₀, t)).PosDef :=
    C.labelHessian_posDef_of_jacobian_pos hF bW ℓ (C.curve w₀ t) t
      (mem_extChartAt_source _) (hpos _ t ht (mem_extChartAt_source _))
  refine ⟨?_, fun t ht ↦ (hp t ht).inv⟩
  intro t ht
  have hi := continuousAt_matrix_inv _
    (show ContinuousAt Ring.inverse
      (F.familyLabelHessianMatrix bW (fun q ↦ C.curve q.1 q.2) (w₀, t)).det from
      by simpa only [Ring.inverse_eq_inv'] using
        continuousAt_inv₀ ((Matrix.isUnit_iff_isUnit_det _).mp (hp t ht).isUnit).ne_zero)
  exact (hi.comp (f := fun r ↦ F.familyLabelHessianMatrix bW
    (fun q ↦ C.curve q.1 q.2) (w₀, r))
      (C.continuousAt_labelHessian hF bW t)).continuousWithinAt

end ContinuousFinslerNorm.SmoothPhaseJetComparison
end OTSelector.Geometry
