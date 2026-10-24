import OTSelector.Analysis.Convex.Legendre.Graph
import OTSelector.Analysis.Convex.Legendre.Parametric
import OTSelector.Analysis.ODE.Flow.NonautonomousVariation
import OTSelector.Analysis.ODE.Hamiltonian.GraphDynamics
import OTSelector.Geometry.Finsler.Basic
import OTSelector.Geometry.Finsler.Calibration.Chart
import OTSelector.Geometry.Finsler.Coordinates.GraphLength
import OTSelector.Geometry.Finsler.Energy.Basic
import OTSelector.Geometry.Finsler.GraphDynamics
import OTSelector.Geometry.Finsler.Hamiltonian.Graph
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Geometry.GraphHamiltonianVariation.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Geometry.GraphHamiltonianVariation`; the selected original proof blocks follow. -/
section

/-!
# Geometry.Finsler.GraphHamiltonianVariation

* **Conditions:** A jointly C2 nonautonomous phase family satisfying its actual graph Hamiltonian equation on an open product domain.
* **Objects:** Actual parameter variations solving the genuine reduced Hamiltonian A,B,C blocks; Finsler specialization identifies their original-length partials.
* **Proof detail:** Exchange mixed derivatives of the same C2 family, differentiate the slice ODE in the parameter, and expand the actual vector-field derivative.

Mathematical sources:
- [Gerald Teschl, Ordinary Differential Equations and Dynamical Systems (AMS 2012 author preliminary version)](https://www.mat.univie.ac.at/~gerald/ftp/book-ode/ode.pdf#page=56): Section 2.4, pp. 45–47, equations (2.46)–(2.50), Theorem 2.10.
- [Gerald Teschl, Ordinary Differential Equations and Dynamical Systems (AMS 2012 author preliminary version)](https://www.mat.univie.ac.at/~gerald/ftp/book-ode/ode.pdf#page=249): Section 8.3, pp. 238–240, equations (8.33)–(8.47): first variation, Euler–Lagrange, Legendre transformation, Hamilton equations and energy conservation.
- [Jiří Lebl, Basic Analysis II: Introduction to Real Analysis, Volume II](https://www.jirka.org/ra/realanal2.pdf): Sections 8.3–8.4, total derivative, chain rule and mean-value bounds; Section 8.6, higher derivatives.

Source relation (derived): A nonautonomous parameter-variation derivation, not a reduced subsystem obtained by deleting coordinates from an ambient equation.
-/

/-!
# Actual parameter variations of graph Hamiltonian solution families

The original nonautonomous slice equation of one jointly C2 phase family is differentiated
in its actual parameter direction. The same partial Legendre branch supplies the field and
all coefficients. The derived position and momentum variations solve the genuine reduced
Hamiltonian blocks, rather than a subsystem obtained by deleting ambient coordinates.
The Finsler consumer identifies the same coefficients with actual original-length partials.
-/

open Set Filter Manifold
open scoped Topology ContDiff

namespace OTSelector.Geometry

variable {W E : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A genuine graph solution family's actual parameter derivative solves the same branch's
Hamiltonian variation equations; no mixed equality or variational ODE is supplied. -/
theorem hasDerivAt_graphHamiltonian_parameterVariation
    {L : (ℝ × E) × E → ℝ}
    {g : OpenPartialHomeomorph ((ℝ × E) × E) ((ℝ × E) × (E →L[ℝ] ℝ))}
    (hg : (g : ((ℝ × E) × E) → ((ℝ × E) × (E →L[ℝ] ℝ))) = parametricLegendre L)
    (hL : ContDiffOn ℝ ∞ L g.source) (hG : ContDiffOn ℝ ∞ g.symm g.target)
    {Ψ : W × ℝ → E × (E →L[ℝ] ℝ)} {D : Set (W × ℝ)}
    (hD : IsOpen D) (hΨ : ContDiffOn ℝ 2 Ψ D)
    (hODE : ∀ z ∈ D, HasDerivAt (fun s ↦ Ψ (z.1, s))
      (GraphHamiltonian.field L g z.2 (Ψ z)) z.2)
    {w₀ : W} {t : ℝ} (hz : (w₀, t) ∈ D)
    (hp : ((t, (Ψ (w₀, t)).1), (Ψ (w₀, t)).2) ∈ g.target) (ξ : W) :
    let Z := fun s ↦ fderiv ℝ (fun w ↦ Ψ (w, s)) w₀ ξ
    let A := GraphHamiltonian.blockA L g t (Ψ (w₀, t))
    let B := GraphHamiltonian.blockB L g t (Ψ (w₀, t))
    let C := GraphHamiltonian.blockC L g t (Ψ (w₀, t))
    HasDerivAt (fun s ↦ (Z s).1) (B (Z t).1 + C (Z t).2) t ∧
      HasDerivAt (fun s ↦ (Z s).2) (-A (Z t).1 - (Z t).2.comp B) t := by
  have hj := (GraphHamiltonian.contDiffOn_field hL hG).contDiffAt
    (g.open_target.mem_nhds hp)
  have hX : DifferentiableAt ℝ (GraphHamiltonian.field L g t) (Ψ (w₀, t)) :=
    (hj.comp (Ψ (w₀, t))
      ((contDiffAt_const.prodMk contDiffAt_fst).prodMk contDiffAt_snd)).differentiableAt (by simp)
  have hv := hasDerivAt_parameterVariation_of_nonautonomousODE hD hΨ hODE hz hX ξ
  rw [GraphHamiltonian.field_linearized_blocks hg hL hG hp] at hv
  exact ⟨hv.fst, hv.snd⟩

namespace ContinuousFinslerNorm.IsSmoothStronglyConvex

variable {M : Type*} [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace (ℝ × E) M]
  [IsManifold 𝓘(ℝ, ℝ × E) ∞ M]
  {F : ContinuousFinslerNorm (ℝ × E) M}

/-- Actual Finsler graph solution variations satisfy the same branch's true reduced system,
with positive inverse original graph Hessian and the original mixed-partial coefficients. -/
theorem chartGraph_parameterVariation (hF : F.IsSmoothStronglyConvex) (x₀ : M)
    {g : OpenPartialHomeomorph ((ℝ × E) × E) ((ℝ × E) × (E →L[ℝ] ℝ))}
    (hg : (g : ((ℝ × E) × E) → ((ℝ × E) × (E →L[ℝ] ℝ))) =
      parametricLegendre (F.chartGraphLagrangian x₀))
    (hsub : g.source ⊆ (extChartAt 𝓘(ℝ, ℝ × E) x₀).target ×ˢ univ)
    (hG : ContDiffOn ℝ ∞ g.symm g.target)
    {Ψ : W × ℝ → E × (E →L[ℝ] ℝ)} {D : Set (W × ℝ)}
    (hD : IsOpen D) (hΨ : ContDiffOn ℝ 2 Ψ D)
    (hODE : ∀ z ∈ D, HasDerivAt (fun s ↦ Ψ (z.1, s))
      (GraphHamiltonian.field (F.chartGraphLagrangian x₀) g z.2 (Ψ z)) z.2)
    {w₀ : W} {t : ℝ} (hz : (w₀, t) ∈ D)
    (hp : ((t, (Ψ (w₀, t)).1), (Ψ (w₀, t)).2) ∈ g.target) (ξ : W) :
    let L := F.chartGraphLagrangian x₀
    let Z := fun s ↦ fderiv ℝ (fun w ↦ Ψ (w, s)) w₀ ξ
    let z := g.symm ((t, (Ψ (w₀, t)).1), (Ψ (w₀, t)).2)
    let A := GraphHamiltonian.blockA L g t (Ψ (w₀, t))
    let B := GraphHamiltonian.blockB L g t (Ψ (w₀, t))
    let C := GraphHamiltonian.blockC L g t (Ψ (w₀, t))
    HasDerivAt (fun s ↦ (Z s).1) (B (Z t).1 + C (Z t).2) t ∧
      HasDerivAt (fun s ↦ (Z s).2) (-A (Z t).1 - (Z t).2.comp B) t ∧
      (∀ b w, A b w = A w b) ∧
      (∀ q r : E →L[ℝ] ℝ, r (C q) = q (C r)) ∧
      C = ContinuousLinearMap.inverse (GraphLegendre.verticalHessian L z) ∧
      (∀ q : E →L[ℝ] ℝ, q ≠ 0 → 0 < q (C q)) ∧
      (∀ b, B b = -C (GraphHamiltonian.lagrangianMixed L z b)) ∧
      ∀ b w, A b w =
        GraphHamiltonian.lagrangianMixed L z w (C (GraphHamiltonian.lagrangianMixed L z b)) -
          GraphHamiltonian.lagrangianPositionHessian L z b w := by
  have hL : ContDiffOn ℝ ∞ (F.chartGraphLagrangian x₀) g.source :=
    (hF.contDiffOn_chartGraphLength x₀).mono hsub
  have hv := hasDerivAt_graphHamiltonian_parameterVariation hg hL hG hD hΨ hODE hz hp ξ
  have hb := hF.chartGraphDynamics_blocks x₀ hg hsub hG hp
  exact ⟨hv.1, hv.2, hb.2⟩

end ContinuousFinslerNorm.IsSmoothStronglyConvex
end OTSelector.Geometry

end
