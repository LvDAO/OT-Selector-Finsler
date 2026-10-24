import OTSelector.Geometry.FinslerGraphLabelInverse
import OTSelector.Geometry.FinslerPhaseJetJacobianTransfer

/-!
# Original label Hessians from the same actual phase jet

The label length Hessian only uses the actual position and its joint first derivative.
Consequently the original rough family and its smooth comparison have exactly the same
matrix. The comparison's real graph inverse therefore computes the original kernel.
-/

open Set Filter Matrix Module Manifold
open scoped Topology ContDiff Matrix.Norms.Operator

noncomputable section
namespace OTSelector.Geometry.ContinuousFinslerNorm

set_option backward.isDefEq.respectTransparency false

variable {E W V M ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [Fintype ι] [DecidableEq ι] {F : ContinuousFinslerNorm E M}

omit [Fintype ι] [DecidableEq ι] in
/-- The original label Hessian depends only on the actual position and joint first jet. -/
theorem chartFamilyLabelHessianMatrix_eq_of_hasFDerivAt (F : ContinuousFinslerNorm E M)
    (old : M) (bW : Basis ι ℝ W) {x y : W × ℝ → E} {q : W × ℝ}
    {D : (W × ℝ) →L[ℝ] E} (hvalue : x q = y q)
    (hx : HasFDerivAt x D q) (hy : HasFDerivAt y D q) :
    F.chartFamilyLabelHessianMatrix old bW x q =
      F.chartFamilyLabelHessianMatrix old bW y q := by
  simp only [chartFamilyLabelHessianMatrix, hx.fderiv, hy.fderiv, hvalue]

omit [Fintype ι] [DecidableEq ι] in
/-- Matching actual phase jets and central positions identify the original and comparison
label Hessians in the same fixed manifold chart and label basis. -/
theorem chartFamilyLabelHessianMatrix_eq_of_chartMomentum_same_firstJet
    (F : ContinuousFinslerNorm E M) (old : M) (bW : Basis ι ℝ W)
    {Γ₁ Γ₂ : W → ℝ → M} {q : W × ℝ}
    {D : (W × ℝ) →L[ℝ] E × (E →L[ℝ] ℝ)}
    (hvalue : Γ₁ q.1 q.2 = Γ₂ q.1 q.2)
    (h₁ : HasFDerivAt (F.chartMomentumFamily old Γ₁) D q)
    (h₂ : HasFDerivAt (F.chartMomentumFamily old Γ₂) D q) :
    F.chartFamilyLabelHessianMatrix old bW
      (fun p ↦ extChartAt 𝓘(ℝ, E) old (Γ₁ p.1 p.2)) q =
      F.chartFamilyLabelHessianMatrix old bW
        (fun p ↦ extChartAt 𝓘(ℝ, E) old (Γ₂ p.1 p.2)) q :=
  F.chartFamilyLabelHessianMatrix_eq_of_hasFDerivAt old bW
    (congrArg (extChartAt 𝓘(ℝ, E) old) hvalue) h₁.fst h₂.fst

namespace IsSmoothStronglyConvex

variable [FiniteDimensional ℝ W] [FiniteDimensional ℝ V]

/-- The original family uses the smooth comparison's true graph inverse to compute its
actual inverse label length Hessian in the same Hamiltonian Jacobi frame. -/
theorem chartFamilyLabelHessian_inverse_eq_graph_blockC
    (hF : F.IsSmoothStronglyConvex) (old : M) (A : E ≃L[ℝ] (ℝ × V))
    (bW : Basis ι ℝ W) (bV : Basis ι ℝ V)
    {x y : W × ℝ → E} {w : W} {t : ℝ}
    (hvalue : x (w, t) = y (w, t))
    (hx : HasFDerivAt x (fderiv ℝ y (w, t)) (w, t))
    (hy : DifferentiableAt ℝ y (w, t))
    {e : OpenPartialHomeomorph (W × ℝ) (W × ℝ)}
    (he : (e : W × ℝ → W × ℝ) = curveGraphCoordinateMap (A ∘ y))
    (hz : (w, t) ∈ e.source)
    (hv : 0 < (fderiv ℝ (A ∘ y) (w, t) (0, 1)).1)
    {g : OpenPartialHomeomorph ((ℝ × V) × V) ((ℝ × V) × (V →L[ℝ] ℝ))}
    (hg : (g : ((ℝ × V) × V) → ((ℝ × V) × (V →L[ℝ] ℝ))) =
      parametricLegendre (F.adaptedGraphLagrangian old A))
    (hsub : g.source ⊆ (A.symm ⁻¹' (extChartAt 𝓘(ℝ, E) old).target) ×ˢ univ)
    (hG : ContDiffOn ℝ ∞ g.symm g.target)
    (hsource : graphVelocityPhase (fun z ↦ (curveGraphPosition (A ∘ y) e z).2)
      (w, (A (y (w, t))).1) ∈ g.source)
    (hJ : (vectorFamilyMatrix bV (fun j ↦ fderiv ℝ
      (fun z ↦ (curveGraphPosition (A ∘ y) e (z, (A (y (w, t))).1)).2) w (bW j))).det ≠ 0) :
    let s := (A (x (w, t))).1
    let Ψ := F.adaptedGraphPhase old A (A ∘ y) e
    let J := vectorFamilyMatrix bV (fun j ↦ fderiv ℝ
      (fun z ↦ (curveGraphPosition (A ∘ y) e (z, s)).2) w (bW j))
    let C := hamiltonianMatrixC bV
      (GraphHamiltonian.blockC (F.adaptedGraphLagrangian old A) g s (Ψ (w, s)))
    (F.chartFamilyLabelHessianMatrix old bW x (w, t))⁻¹ =
      (fderiv ℝ (A ∘ x) (w, t) (0, 1)).1 • (J⁻¹ * C * J⁻¹ᵀ) := by
  have hd : fderiv ℝ (A ∘ x) (w, t) = fderiv ℝ (A ∘ y) (w, t) :=
    (A.hasFDerivAt.comp (w, t) hx).fderiv.trans
      (A.hasFDerivAt.comp (w, t) hy.hasFDerivAt).fderiv.symm
  have hK := F.chartFamilyLabelHessianMatrix_eq_of_hasFDerivAt old bW hvalue hx hy.hasFDerivAt
  have hAy : DifferentiableAt ℝ (A ∘ y) (e.symm (e (w, t))) := by
    rw [e.left_inv hz]
    exact A.differentiableAt.comp (w, t) hy
  have hv' : 0 < (fderiv ℝ (A ∘ y) (e.symm (e (w, t))) (0, 1)).1 := by
    rwa [e.left_inv hz]
  have hi := differentiableAt_curveGraphInverse_of_regular he (e.map_source hz) hAy hv'.ne'
  have heq : e (w, t) = (w, (A (y (w, t))).1) := congrFun he (w, t)
  have hcancel : A.symm ∘ (A ∘ y) = y := by
    funext q
    exact A.symm_apply_apply (y q)
  have hmain := hF.adaptedGraphLength_label_inverse_eq_blockC old A bW bV he
    (e.map_source hz) hAy hi hv' hg hsub hG
    (by simpa only [heq] using hsource) (by simpa only [heq] using hJ)
  dsimp only at hmain ⊢
  rw [e.left_inv hz, hcancel, heq] at hmain
  rw [hvalue, hd, hK]
  exact hmain

end IsSmoothStronglyConvex
end OTSelector.Geometry.ContinuousFinslerNorm
