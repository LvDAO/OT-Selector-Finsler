import OTSelector.Analysis.Convex.Legendre.Graph
import OTSelector.Analysis.Convex.Legendre.Parametric
import OTSelector.Analysis.ODE.Hamiltonian.GraphDynamics
import OTSelector.Geometry.Finsler.Basic
import OTSelector.Geometry.Finsler.Calibration.Chart
import OTSelector.Geometry.Finsler.Coordinates.GraphLength
import OTSelector.Geometry.Finsler.Energy.Basic
import OTSelector.Geometry.Finsler.Hamiltonian.Graph
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Geometry.FinslerGraphDynamics.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Geometry.FinslerGraphDynamics`; the selected original proof blocks follow. -/
section

/-!
# Geometry.Finsler.GraphDynamics

* **Conditions:** The original graph-length Lagrangian and a genuine partial Legendre inverse, constructed from smooth strong convexity for the existence theorem.
* **Objects:** A smooth nonautonomous graph Hamiltonian vector field and genuine A,B,C derivative blocks with positive C and Schur-complement formulas.
* **Proof detail:** Differentiate the same partial Hamiltonian and inverse branch, identify the inverse graph Hessian and mixed derivatives, then collect the exact canonical blocks.

Mathematical sources:
- [Gerald Teschl, Ordinary Differential Equations and Dynamical Systems (AMS 2012 author preliminary version)](https://www.mat.univie.ac.at/~gerald/ftp/book-ode/ode.pdf#page=249): Section 8.3, pp. 238–240, equations (8.33)–(8.47): first variation, Euler–Lagrange, Legendre transformation, Hamilton equations and energy conservation.
- [Jiří Lebl, Basic Analysis II: Introduction to Real Analysis, Volume II (version 6.3, 15 May 2026)](https://www.jirka.org/ra/realanal2.pdf#page=38): Section 8.3, Theorem 8.3.7, p. 38; Exercise 8.3.7, p. 45 (differentiate the inverse identity).
- [Zhongmin Shen, Landsberg Curvature, S-Curvature and Riemann Curvature, MSRI Publications 50 (2004)](https://library.slmath.org/books/Book50/files/08Sh.pdf#page=2): Section 2, pp. 304–305: positive homogeneity, slit smoothness, positive fundamental tensor gy=½∂²F² and F(y)²=gy(y,y).

Source relation (derived): The Schur-type formulas come from explicit block differentiation; this module does not yet identify a regraphed ambient solution or endpoint distance Hessian.
-/

/-!
# Actual reduced Hamiltonian dynamics of Finsler graph length

The original length integrand at velocity `(1, η)` constructs a genuine partial Legendre
chart and a smooth nonautonomous field on graph position and momentum. Its actual phase
derivative has canonical blocks. C is the inverse actual graph Hessian and strictly
positive; A and C are symmetric; B and A have the genuine mixed-Hessian and Schur-complement
expressions. All coefficients belong to the same constructed inverse branch.

This module constructs the local differential data. It does not identify a reparameterized
ambient flow, prove a whole-segment coordinate branch, or identify endpoint distance Hessians.
-/

open Set Manifold
open scoped ContDiff

namespace OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

variable {V M : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V] [TopologicalSpace M] [ChartedSpace (ℝ × V) M]
  [IsManifold 𝓘(ℝ, ℝ × V) ∞ M]
  {F : ContinuousFinslerNorm (ℝ × V) M} (hF : F.IsSmoothStronglyConvex)
include hF

/-- The same genuine graph inverse has actual canonical linearization with coefficients
identified from the original length derivatives, without any coefficient assumptions. -/
theorem chartGraphDynamics_blocks (x₀ : M)
    {e : OpenPartialHomeomorph ((ℝ × V) × V) ((ℝ × V) × (V →L[ℝ] ℝ))}
    (he : (e : ((ℝ × V) × V) → ((ℝ × V) × (V →L[ℝ] ℝ))) =
      parametricLegendre (F.chartGraphLagrangian x₀))
    (hsub : e.source ⊆ (extChartAt 𝓘(ℝ, ℝ × V) x₀).target ×ˢ univ)
    (hG : ContDiffOn ℝ ∞ e.symm e.target)
    {t : ℝ} {p : V × (V →L[ℝ] ℝ)} (hp : ((t, p.1), p.2) ∈ e.target) :
    let L := F.chartGraphLagrangian x₀
    let z := e.symm ((t, p.1), p.2)
    let A := GraphHamiltonian.blockA L e t p
    let B := GraphHamiltonian.blockB L e t p
    let C := GraphHamiltonian.blockC L e t p
    (∀ b q, fderiv ℝ (GraphHamiltonian.field L e t) p (b, q) =
      (B b + C q, -A b - q.comp B)) ∧
    (∀ b w, A b w = A w b) ∧
    (∀ q r : V →L[ℝ] ℝ, r (C q) = q (C r)) ∧
    C = ContinuousLinearMap.inverse (GraphLegendre.verticalHessian L z) ∧
    (∀ q : V →L[ℝ] ℝ, q ≠ 0 → 0 < q (C q)) ∧
    (∀ b, B b = -C (GraphHamiltonian.lagrangianMixed L z b)) ∧
    ∀ b w, A b w =
      GraphHamiltonian.lagrangianMixed L z w (C (GraphHamiltonian.lagrangianMixed L z b)) -
        GraphHamiltonian.lagrangianPositionHessian L z b w := by
  let L := F.chartGraphLagrangian x₀
  have hL : ContDiffOn ℝ ∞ L e.source := (hF.contDiffOn_chartGraphLength x₀).mono hsub
  have hpos : ∀ w : V, w ≠ 0 →
      0 < GraphLegendre.verticalHessian L (e.symm ((t, p.1), p.2)) w w := by
    intro w hw
    exact hF.chartGraphLength_hessian_pos x₀
      (hsub (e.map_target hp)).1 (e.symm ((t, p.1), p.2)).2 hw
  exact ⟨GraphHamiltonian.field_linearized_blocks he hL hG hp,
    GraphHamiltonian.blockA_symm he hL hG hp,
    GraphHamiltonian.blockC_symm he hL hG hp,
    GraphHamiltonian.blockC_eq_inverse he hL hG hp hpos,
    fun _ hq ↦ GraphHamiltonian.blockC_pos he hL hG hp hpos hq,
    GraphHamiltonian.blockB_eq_neg_inverse_mixed he hL hG hp hpos,
    GraphHamiltonian.blockA_eq_lagrangian_schur he hL hG hp hpos⟩

/-- Original smooth strongly convex Finsler data construct one actual graph Hamiltonian
field, its scalar canonical differential, and its true positive reduced blocks. -/
theorem exists_chartGraphDynamics (x₀ : M) {z : (ℝ × V) × V}
    (hz : z.1 ∈ (extChartAt 𝓘(ℝ, ℝ × V) x₀).target) :
    let L := F.chartGraphLagrangian x₀
    ∃ e : OpenPartialHomeomorph ((ℝ × V) × V) ((ℝ × V) × (V →L[ℝ] ℝ)),
      (e : ((ℝ × V) × V) → ((ℝ × V) × (V →L[ℝ] ℝ))) = parametricLegendre L ∧
      z ∈ e.source ∧ parametricLegendre L z ∈ e.target ∧
      e.source ⊆ (extChartAt 𝓘(ℝ, ℝ × V) x₀).target ×ˢ univ ∧
      ContDiffOn ℝ ∞ e.symm e.target ∧
      ContDiffOn ℝ ∞ (GraphLegendre.hamiltonian L e) e.target ∧
      ContDiffOn ℝ ∞
        (fun p : (ℝ × V) × (V →L[ℝ] ℝ) ↦ GraphHamiltonian.field L e p.1.1 (p.1.2, p.2))
        e.target ∧
      ∀ t p, ((t, p.1), p.2) ∈ e.target →
        let z' := e.symm ((t, p.1), p.2)
        let A := GraphHamiltonian.blockA L e t p
        let B := GraphHamiltonian.blockB L e t p
        let C := GraphHamiltonian.blockC L e t p
        (∀ u, fderiv ℝ (GraphHamiltonian.hamiltonian L e t) p u =
          u.2 (GraphHamiltonian.field L e t p).1 - (GraphHamiltonian.field L e t p).2 u.1) ∧
        (∀ b q, fderiv ℝ (GraphHamiltonian.field L e t) p (b, q) =
          (B b + C q, -A b - q.comp B)) ∧
        (∀ b w, A b w = A w b) ∧
        (∀ q r : V →L[ℝ] ℝ, r (C q) = q (C r)) ∧
        C = ContinuousLinearMap.inverse (GraphLegendre.verticalHessian L z') ∧
        (∀ q : V →L[ℝ] ℝ, q ≠ 0 → 0 < q (C q)) ∧
        (∀ b, B b = -C (GraphHamiltonian.lagrangianMixed L z' b)) ∧
        ∀ b w, A b w =
          GraphHamiltonian.lagrangianMixed L z' w
            (C (GraphHamiltonian.lagrangianMixed L z' b)) -
          GraphHamiltonian.lagrangianPositionHessian L z' b w := by
  dsimp only
  obtain ⟨e, he, hzs, hzt, hsub, _, hG, _, _⟩ :=
    hF.exists_smooth_chartGraphLegendre_local_inverse x₀ hz
  have hL : ContDiffOn ℝ ∞ (F.chartGraphLagrangian x₀) e.source :=
    (hF.contDiffOn_chartGraphLength x₀).mono hsub
  refine ⟨e, he, hzs, hzt, hsub, hG, GraphLegendre.contDiffOn_hamiltonian hL hG,
    GraphHamiltonian.contDiffOn_field hL hG, ?_⟩
  intro t p hp
  exact ⟨GraphHamiltonian.hamiltonian_fderiv_apply he hL hG hp,
    hF.chartGraphDynamics_blocks x₀ he hsub hG hp⟩

end OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

end
