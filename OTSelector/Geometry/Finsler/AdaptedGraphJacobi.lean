import OTSelector.Analysis.Convex.Legendre.Graph
import OTSelector.Analysis.Convex.Legendre.Parametric
import OTSelector.Analysis.ODE.Hamiltonian.GraphDynamics
import OTSelector.Geometry.Finsler.AdaptedGraphLagrangian
import OTSelector.Geometry.Finsler.Basic
import OTSelector.Geometry.Finsler.Energy.Basic
import OTSelector.Geometry.Finsler.GraphHamiltonianVariation

/-!
# Geometry.Finsler.AdaptedGraphJacobi

* **Conditions:** The adapted original graph integrand with a genuine inverse branch, and a jointly C2 actual nonautonomous solution family for its variation theorem.
* **Objects:** Actual adapted Hamiltonian blocks with symmetric A,C, positive inverse-Hessian C and reduced Jacobi equations.
* **Proof detail:** Differentiate the same partial transform and inverse identities, then differentiate its slice equation in the actual parameter.

Mathematical sources:
- [Gerald Teschl, Ordinary Differential Equations and Dynamical Systems (AMS 2012 author preliminary version)](https://www.mat.univie.ac.at/~gerald/ftp/book-ode/ode.pdf#page=249): Section 8.3, pp. 238–240, equations (8.33)–(8.47): first variation, Euler–Lagrange, Legendre transformation, Hamilton equations and energy conservation.
- [Gerald Teschl, Ordinary Differential Equations and Dynamical Systems (AMS 2012 author preliminary version)](https://www.mat.univie.ac.at/~gerald/ftp/book-ode/ode.pdf#page=56): Section 2.4, pp. 45–47, equations (2.46)–(2.50), Theorem 2.10.
- [Jiří Lebl, Basic Analysis II: Introduction to Real Analysis, Volume II (version 6.3, 15 May 2026)](https://www.jirka.org/ra/realanal2.pdf#page=38): Section 8.3, Theorem 8.3.7, p. 38; Exercise 8.3.7, p. 45 (differentiate the inverse identity).

Source relation (derived): The stated result is a derived local construction from the cited principles. The exact original family, branch, coordinate maps and hypotheses remain those in the full source telescope.
-/

/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Geometry.FinslerAdaptedGraphJacobi.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Geometry.FinslerAdaptedGraphJacobi`; the selected original proof blocks follow. -/
section

/-!
# Actual reduced Jacobi equations in adapted original Finsler coordinates

A genuine linear splitting of any model E pulls back the original length. Its actual
Legendre branch supplies smooth graph Hamiltonian dynamics and symmetric reduced
blocks, with positive inverse original graph Hessian. Differentiating a jointly C2
solution family gives the actual reduced Jacobi equations in the same coordinates.
No product-model Finsler structure or replacement geometric cost is introduced.
-/

open Set Manifold
open scoped ContDiff

namespace OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

variable {E V M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {F : ContinuousFinslerNorm E M} (hF : F.IsSmoothStronglyConvex)
include hF

/-- The same genuine graph inverse has actual canonical linearization with coefficients
identified from the original length derivatives, without any coefficient assumptions. -/
theorem adaptedGraphDynamics_blocks (old : M) (T : E ≃L[ℝ] (ℝ × V))
    {e : OpenPartialHomeomorph ((ℝ × V) × V) ((ℝ × V) × (V →L[ℝ] ℝ))}
    (he : (e : ((ℝ × V) × V) → ((ℝ × V) × (V →L[ℝ] ℝ))) =
      parametricLegendre (F.adaptedGraphLagrangian old T))
    (hsub : e.source ⊆ (T.symm ⁻¹' (extChartAt 𝓘(ℝ, E) old).target) ×ˢ univ)
    (hG : ContDiffOn ℝ ∞ e.symm e.target)
    {t : ℝ} {p : V × (V →L[ℝ] ℝ)} (hp : ((t, p.1), p.2) ∈ e.target) :
    let L := F.adaptedGraphLagrangian old T
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
  let L := F.adaptedGraphLagrangian old T
  have hL : ContDiffOn ℝ ∞ L e.source := (hF.contDiffOn_adaptedGraphLagrangian old T).mono hsub
  have hpos : ∀ w : V, w ≠ 0 →
      0 < GraphLegendre.verticalHessian L (e.symm ((t, p.1), p.2)) w w := by
    intro w hw
    exact hF.adaptedGraphLagrangian_hessian_pos old T
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
theorem exists_adaptedGraphDynamics (old : M) (T : E ≃L[ℝ] (ℝ × V)) {z : (ℝ × V) × V}
    (hz : z.1 ∈ (T.symm ⁻¹' (extChartAt 𝓘(ℝ, E) old).target)) :
    let L := F.adaptedGraphLagrangian old T
    ∃ e : OpenPartialHomeomorph ((ℝ × V) × V) ((ℝ × V) × (V →L[ℝ] ℝ)),
      (e : ((ℝ × V) × V) → ((ℝ × V) × (V →L[ℝ] ℝ))) = parametricLegendre L ∧
      z ∈ e.source ∧ parametricLegendre L z ∈ e.target ∧
      e.source ⊆ (T.symm ⁻¹' (extChartAt 𝓘(ℝ, E) old).target) ×ˢ univ ∧
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
    hF.exists_smooth_adaptedGraphLegendre_local_inverse old T hz
  have hL : ContDiffOn ℝ ∞ (F.adaptedGraphLagrangian old T) e.source :=
    (hF.contDiffOn_adaptedGraphLagrangian old T).mono hsub
  refine ⟨e, he, hzs, hzt, hsub, hG, GraphLegendre.contDiffOn_hamiltonian hL hG,
    GraphHamiltonian.contDiffOn_field hL hG, ?_⟩
  intro t p hp
  exact ⟨GraphHamiltonian.hamiltonian_fderiv_apply he hL hG hp,
    hF.adaptedGraphDynamics_blocks old T he hsub hG hp⟩

variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]

/-- Actual Finsler graph solution variations satisfy the same branch's true reduced system,
with positive inverse original graph Hessian and the original mixed-partial coefficients. -/
theorem adaptedGraph_parameterVariation (old : M) (T : E ≃L[ℝ] (ℝ × V))
    {g : OpenPartialHomeomorph ((ℝ × V) × V) ((ℝ × V) × (V →L[ℝ] ℝ))}
    (hg : (g : ((ℝ × V) × V) → ((ℝ × V) × (V →L[ℝ] ℝ))) =
      parametricLegendre (F.adaptedGraphLagrangian old T))
    (hsub : g.source ⊆ (T.symm ⁻¹' (extChartAt 𝓘(ℝ, E) old).target) ×ˢ univ)
    (hG : ContDiffOn ℝ ∞ g.symm g.target)
    {Ψ : W × ℝ → V × (V →L[ℝ] ℝ)} {D : Set (W × ℝ)}
    (hD : IsOpen D) (hΨ : ContDiffOn ℝ 2 Ψ D)
    (hODE : ∀ z ∈ D, HasDerivAt (fun s ↦ Ψ (z.1, s))
      (GraphHamiltonian.field (F.adaptedGraphLagrangian old T) g z.2 (Ψ z)) z.2)
    {w₀ : W} {t : ℝ} (hz : (w₀, t) ∈ D)
    (hp : ((t, (Ψ (w₀, t)).1), (Ψ (w₀, t)).2) ∈ g.target) (ξ : W) :
    let L := F.adaptedGraphLagrangian old T
    let Z := fun s ↦ fderiv ℝ (fun w ↦ Ψ (w, s)) w₀ ξ
    let z := g.symm ((t, (Ψ (w₀, t)).1), (Ψ (w₀, t)).2)
    let A := GraphHamiltonian.blockA L g t (Ψ (w₀, t))
    let B := GraphHamiltonian.blockB L g t (Ψ (w₀, t))
    let C := GraphHamiltonian.blockC L g t (Ψ (w₀, t))
    HasDerivAt (fun s ↦ (Z s).1) (B (Z t).1 + C (Z t).2) t ∧
      HasDerivAt (fun s ↦ (Z s).2) (-A (Z t).1 - (Z t).2.comp B) t ∧
      (∀ b w, A b w = A w b) ∧
      (∀ q r : V →L[ℝ] ℝ, r (C q) = q (C r)) ∧
      C = ContinuousLinearMap.inverse (GraphLegendre.verticalHessian L z) ∧
      (∀ q : V →L[ℝ] ℝ, q ≠ 0 → 0 < q (C q)) ∧
      (∀ b, B b = -C (GraphHamiltonian.lagrangianMixed L z b)) ∧
      ∀ b w, A b w =
        GraphHamiltonian.lagrangianMixed L z w (C (GraphHamiltonian.lagrangianMixed L z b)) -
          GraphHamiltonian.lagrangianPositionHessian L z b w := by
  have hL : ContDiffOn ℝ ∞ (F.adaptedGraphLagrangian old T) g.source :=
    (hF.contDiffOn_adaptedGraphLagrangian old T).mono hsub
  have hv := hasDerivAt_graphHamiltonian_parameterVariation hg hL hG hD hΨ hODE hz hp ξ
  have hb := hF.adaptedGraphDynamics_blocks old T hg hsub hG hp
  exact ⟨hv.1, hv.2, hb.2⟩


end OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

end
