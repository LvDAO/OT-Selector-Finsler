import OTSelector.Geometry.Finsler.Jacobi.LabelHessian
import OTSelector.Geometry.FinslerGraphLabelHessian
import OTSelector.LinearAlgebra.Matrix.LabelHessianMatrix
import OTSelector.Geometry.Finsler.AdaptedGraphJacobi
import OTSelector.Analysis.Calculus.GraphVelocityPhase

/-!
# Geometry.Finsler.Jacobi.LabelHessian

* **Conditions:** An actual Finsler chart family and a transverse basis, with no regularity hypothesis needed to define its totalized derivative expression.
* **Objects:** The matrix obtained by evaluating the true fiber length Hessian on actual label derivatives at the actual time velocity.
* **Proof detail:** Define each matrix entry by the original Hessian and the two basis-generated family derivatives, retaining their exact index convention.

Mathematical sources:
- [Zhongmin Shen, Landsberg Curvature, S-Curvature and Riemann Curvature, MSRI Publications 50 (2004)](https://library.slmath.org/books/Book50/files/08Sh.pdf#page=2): Section 2, pp. 304–305: positive homogeneity, slit smoothness, positive fundamental tensor gy=½∂²F² and F(y)²=gy(y,y).
- [OT-Selector project authors, Project manuscript main.tex (local provenance)](/data/lyuwt/OT-Selector-smooth-length/main.tex): main.tex, proposition prop:rough-ray-quadratic, lines 1188–1205; equation eq:rough-ray-quadratic, integral inverse-Hessian coefficient.

Source relation (adapter): Only the generic matrix definition is selected. Its inverse/graph identities and the remaining source-file results are outside this extraction.
-/

/-!
# The original label inverse Hessian in the actual graph Jacobi frame

The original-time label length Hessian is defined from the actual position derivative.
Its inverse equals the graph Jacobi compliance integrand multiplied by the actual clock
speed. A genuine Legendre source point identifies this Hessian with the same Hamiltonian
coefficient, so neither a coefficient equality nor a separate quadratic form is assumed.
-/

open Set Filter Matrix Module Manifold
open scoped Topology ContDiff Matrix.Norms.Operator

noncomputable section
namespace OTSelector.Geometry.ContinuousFinslerNorm

set_option backward.isDefEq.respectTransparency false

variable {E W V M ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [Fintype ι] [DecidableEq ι] {F : ContinuousFinslerNorm E M}



namespace IsSmoothStronglyConvex

omit [FiniteDimensional ℝ W] in
/-- The inverse original label length Hessian is the actual positive graph Hessian
inverse pulled back through the same Jacobi matrix, with its precise clock speed. -/
theorem adaptedGraphLength_label_inverse
    (hF : F.IsSmoothStronglyConvex) (old : M) (A : E ≃L[ℝ] (ℝ × V))
    (bW : Basis ι ℝ W) (bV : Basis ι ℝ V)
    {γ : W × ℝ → ℝ × V} {e : OpenPartialHomeomorph (W × ℝ) (W × ℝ)}
    (he : (e : W × ℝ → W × ℝ) = curveGraphCoordinateMap γ)
    {q : W × ℝ} (hq : q ∈ e.target)
    (hγ : DifferentiableAt ℝ γ (e.symm q)) (hi : DifferentiableAt ℝ e.symm q)
    (hv : 0 < (fderiv ℝ γ (e.symm q) (0, 1)).1)
    (hx : A.symm (γ (e.symm q)) ∈ (extChartAt 𝓘(ℝ, E) old).target)
    (hJ : (vectorFamilyMatrix bV (fun j ↦
      fderiv ℝ (fun w ↦ (curveGraphPosition γ e (w, q.2)).2) q.1 (bW j))).det ≠ 0) :
    let y := curveGraphPosition γ e
    let J := vectorFamilyMatrix bV (fun j ↦
      fderiv ℝ (fun w ↦ (y (w, q.2)).2) q.1 (bW j))
    let H := GraphLegendre.verticalHessian (F.adaptedGraphLagrangian old A)
      (y q, deriv (fun s ↦ (y (q.1, s)).2) q.2)
    (F.chartFamilyLabelHessianMatrix old bW (A.symm ∘ γ) (e.symm q))⁻¹ =
      (fderiv ℝ γ (e.symm q) (0, 1)).1 •
        (J⁻¹ * hamiltonianMatrixC bV H.inverse * J⁻¹ᵀ) := by
  let y := curveGraphPosition γ e
  let R := fderiv ℝ (fun w ↦ (y (w, q.2)).2) q.1
  let H := GraphLegendre.verticalHessian (F.adaptedGraphLagrangian old A)
    (y q, deriv (fun s ↦ (y (q.1, s)).2) q.2)
  have hH : ∀ v : V, v ≠ 0 → 0 < H v v := fun v hv' ↦
    hF.adaptedGraphLagrangian_hessian_pos old A hx _ hv'
  have hd : fderiv ℝ (A.symm ∘ γ) (e.symm q) =
      A.symm.toContinuousLinearMap.comp (fderiv ℝ γ (e.symm q)) :=
    (A.symm.hasFDerivAt.comp (e.symm q) hγ.hasFDerivAt).fderiv
  apply inverse_labelHessian_of_graph_congruence bW bV H R hH hv.ne' _ hJ
  ext i j
  change H (R (bW j)) (R (bW i)) =
    (fderiv ℝ γ (e.symm q) (0, 1)).1 *
      F.chartFamilyLabelHessianMatrix old bW (A.symm ∘ γ) (e.symm q) i j
  simp only [chartFamilyLabelHessianMatrix, hd, ContinuousLinearMap.comp_apply,
    ContinuousLinearEquiv.coe_coe, Function.comp_apply]
  exact hF.adaptedGraphLength_label_hessian old A he hq hγ hi hv hx (bW j) (bW i)

omit [NormedSpace ℝ W] [FiniteDimensional ℝ W] [FiniteDimensional ℝ V]
  [Fintype ι] [DecidableEq ι] in
/-- The same graph Legendre branch recovers the actual graph velocity state. -/
theorem adaptedGraphPhase_inverse_state
    (old : M) (A : E ≃L[ℝ] (ℝ × V))
    {γ : W × ℝ → ℝ × V} {e : OpenPartialHomeomorph (W × ℝ) (W × ℝ)}
    (he : (e : W × ℝ → W × ℝ) = curveGraphCoordinateMap γ)
    {q : W × ℝ} (hq : q ∈ e.target)
    {g : OpenPartialHomeomorph ((ℝ × V) × V) ((ℝ × V) × (V →L[ℝ] ℝ))}
    (hg : (g : ((ℝ × V) × V) → ((ℝ × V) × (V →L[ℝ] ℝ))) =
      parametricLegendre (F.adaptedGraphLagrangian old A))
    (hsource : graphVelocityPhase (fun z ↦ (curveGraphPosition γ e z).2) q ∈ g.source) :
    g.symm ((q.2, (F.adaptedGraphPhase old A γ e q).1),
      (F.adaptedGraphPhase old A γ e q).2) =
      (curveGraphPosition γ e q,
        deriv (fun s ↦ (curveGraphPosition γ e (q.1, s)).2) q.2) := by
  have hi := g.left_inv hsource
  rw [hg] at hi
  change g.symm ((q.2, (F.adaptedGraphPhase old A γ e q).1),
    (F.adaptedGraphPhase old A γ e q).2) =
      ((q.2, (curveGraphPosition γ e q).2),
        deriv (fun s ↦ (curveGraphPosition γ e (q.1, s)).2) q.2) at hi
  rw [show (q.2, (curveGraphPosition γ e q).2) = curveGraphPosition γ e q from
    Prod.ext (curveGraph_inverse_components he hq).2.symm rfl] at hi
  exact hi

omit [FiniteDimensional ℝ W] in
/-- The inverse original label Hessian equals the integrand of the actual graph
Hamiltonian system on this same Legendre branch. -/
theorem adaptedGraphLength_label_inverse_eq_blockC
    (hF : F.IsSmoothStronglyConvex) (old : M) (A : E ≃L[ℝ] (ℝ × V))
    (bW : Basis ι ℝ W) (bV : Basis ι ℝ V)
    {γ : W × ℝ → ℝ × V} {e : OpenPartialHomeomorph (W × ℝ) (W × ℝ)}
    (he : (e : W × ℝ → W × ℝ) = curveGraphCoordinateMap γ)
    {q : W × ℝ} (hq : q ∈ e.target)
    (hγ : DifferentiableAt ℝ γ (e.symm q)) (hi : DifferentiableAt ℝ e.symm q)
    (hv : 0 < (fderiv ℝ γ (e.symm q) (0, 1)).1)
    {g : OpenPartialHomeomorph ((ℝ × V) × V) ((ℝ × V) × (V →L[ℝ] ℝ))}
    (hg : (g : ((ℝ × V) × V) → ((ℝ × V) × (V →L[ℝ] ℝ))) =
      parametricLegendre (F.adaptedGraphLagrangian old A))
    (hsub : g.source ⊆ (A.symm ⁻¹' (extChartAt 𝓘(ℝ, E) old).target) ×ˢ univ)
    (hG : ContDiffOn ℝ ∞ g.symm g.target)
    (hsource : graphVelocityPhase (fun z ↦ (curveGraphPosition γ e z).2) q ∈ g.source)
    (hJ : (vectorFamilyMatrix bV (fun j ↦
      fderiv ℝ (fun w ↦ (curveGraphPosition γ e (w, q.2)).2) q.1 (bW j))).det ≠ 0) :
    let Ψ := F.adaptedGraphPhase old A γ e
    let J := vectorFamilyMatrix bV (fun j ↦
      fderiv ℝ (fun w ↦ (curveGraphPosition γ e (w, q.2)).2) q.1 (bW j))
    let C := hamiltonianMatrixC bV
      (GraphHamiltonian.blockC (F.adaptedGraphLagrangian old A) g q.2 (Ψ q))
    (F.chartFamilyLabelHessianMatrix old bW (A.symm ∘ γ) (e.symm q))⁻¹ =
      (fderiv ℝ γ (e.symm q) (0, 1)).1 • (J⁻¹ * C * J⁻¹ᵀ) := by
  have hp : ((q.2, (F.adaptedGraphPhase old A γ e q).1),
      (F.adaptedGraphPhase old A γ e q).2) ∈ g.target := by
    simpa only [hg, graphVelocityPhase, parametricLegendre, adaptedGraphPhase] using!
      g.map_source hsource
  have hi' := adaptedGraphPhase_inverse_state old A he hq hg hsource
  have hx : A.symm (γ (e.symm q)) ∈ (extChartAt 𝓘(ℝ, E) old).target := by
    have hb := (hsub (g.map_target hp)).1
    rw [hi'] at hb
    exact hb
  have hC := (hF.adaptedGraphDynamics_blocks old A hg hsub hG hp).2.2.2.1
  rw [hi'] at hC
  dsimp only
  rw [hC]
  exact hF.adaptedGraphLength_label_inverse old A bW bV he hq hγ hi hv hx hJ

end IsSmoothStronglyConvex
end OTSelector.Geometry.ContinuousFinslerNorm
