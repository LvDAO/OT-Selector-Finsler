import OTSelector.Analysis.Convex.Legendre.Graph
import OTSelector.Analysis.Convex.Legendre.Parametric
import OTSelector.Geometry.Finsler.Basic
import OTSelector.Geometry.Finsler.Calibration.Chart
import OTSelector.Geometry.Finsler.Coordinates.GraphLength
import OTSelector.Geometry.Finsler.Energy.Basic
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Geometry.FinslerGraphHamiltonian.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Geometry.FinslerGraphHamiltonian`; the selected original proof blocks follow. -/
section

/-!
# Geometry.Finsler.Hamiltonian.Graph

* **Conditions:** The original graph-length integrand and its proved positive vertical Hessian at a legal chart base.
* **Objects:** A smooth partial Legendre inverse, its actual inverse-Hessian momentum block and the corresponding partial Hamiltonian.
* **Proof detail:** Apply the parametric inverse function theorem, differentiate its inverse identity and the Legendre cancellation formula, and use Hessian symmetry/positivity.

Mathematical sources:
- [Jiří Lebl, Basic Analysis II: Introduction to Real Analysis, Volume II (version 6.3, 15 May 2026)](https://www.jirka.org/ra/realanal2.pdf#page=51): Section 8.5, Theorem 8.5.1, pp. 51–52; Remark 8.5.8, p. 57.
- [Jiří Lebl, Basic Analysis II: Introduction to Real Analysis, Volume II (version 6.3, 15 May 2026)](https://www.jirka.org/ra/realanal2.pdf#page=38): Section 8.3, Theorem 8.3.7, p. 38; Exercise 8.3.7, p. 45 (differentiate the inverse identity).
- [Gerald Teschl, Ordinary Differential Equations and Dynamical Systems (AMS 2012 author preliminary version)](https://www.mat.univie.ac.at/~gerald/ftp/book-ode/ode.pdf#page=249): Section 8.3, pp. 238–240, equations (8.33)–(8.47): first variation, Euler–Lagrange, Legendre transformation, Hamilton equations and energy conservation.

Source relation (derived): The graph base and velocity spaces have different dimensions; the local partial transform is derived explicitly rather than assuming a phase-space inverse.
-/

/-!
# Actual partial Legendre transforms of Finsler graph length

The scalar Lagrangian is the original chart length evaluated at `(1, η)`, with base
`(t, y)` and velocity `η`. The actual base and velocity dimensions differ. Its proved
smoothness and positive Hessian construct a genuine jointly smooth partial Legendre
inverse. The actual inverse-velocity momentum derivative is symmetric, positive, and
equals the inverse original graph Hessian. It is also the actual momentum Hessian of
the partial Hamiltonian under canonical vector-covector evaluation.

No inverse, Hessian, or positivity condition is supplied beyond the original smooth
strongly convex Finsler data and an admissible chart base. These are local scalar and
inverse-function statements; graph-time reparameterization, Euler-Lagrange dynamics,
and the time-dependent reduced Jacobi system remain separate constructions.
-/

open Set Manifold
open scoped ContDiff NNReal

namespace OTSelector.Geometry.ContinuousFinslerNorm

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  {M : Type*} [TopologicalSpace M] [ChartedSpace (ℝ × V) M]
  [IsManifold 𝓘(ℝ, ℝ × V) ∞ M]

/-- The original Finsler length integrand for graphs in the given chart. -/
noncomputable def chartGraphLagrangian (F : ContinuousFinslerNorm (ℝ × V) M)
    (x₀ : M) (z : (ℝ × V) × V) : ℝ :=
  F.chartLength x₀ (z.1, (1, z.2))

namespace IsSmoothStronglyConvex

variable {F : ContinuousFinslerNorm (ℝ × V) M} (hF : F.IsSmoothStronglyConvex)
include hF

/-- Genuine Finsler graph length constructs a jointly smooth partial Legendre inverse. -/
theorem exists_smooth_chartGraphLegendre_local_inverse [FiniteDimensional ℝ V]
    (x₀ : M) {z : (ℝ × V) × V}
    (hz : z.1 ∈ (extChartAt 𝓘(ℝ, ℝ × V) x₀).target) :
    ∃ e : OpenPartialHomeomorph ((ℝ × V) × V) ((ℝ × V) × (V →L[ℝ] ℝ)),
      (e : ((ℝ × V) × V) → ((ℝ × V) × (V →L[ℝ] ℝ))) =
        parametricLegendre (F.chartGraphLagrangian x₀) ∧
      z ∈ e.source ∧ parametricLegendre (F.chartGraphLagrangian x₀) z ∈ e.target ∧
      e.source ⊆ (extChartAt 𝓘(ℝ, ℝ × V) x₀).target ×ˢ univ ∧
      ContDiffOn ℝ ∞ (parametricLegendre (F.chartGraphLagrangian x₀)) e.source ∧
      ContDiffOn ℝ ∞ e.symm e.target ∧
      (∀ p ∈ e.target, (e.symm p).1 = p.1) ∧
      ∀ p ∈ e.target, HasFDerivAt e.symm
        (ContinuousLinearMap.inverse
          (fderiv ℝ (parametricLegendre (F.chartGraphLagrangian x₀)) (e.symm p))) p := by
  apply exists_smooth_parametricLegendre_local_inverse
    ((isOpen_extChartAt_target x₀).prod isOpen_univ)
    (hF.contDiffOn_chartGraphLength x₀)
  · intro y hy w hw
    exact hF.chartGraphLength_hessian_pos x₀ hy.1 y.2 hw
  · exact ⟨hz, mem_univ _⟩

/-- The actual inverse block is the inverse graph Hessian and the true Hamiltonian
momentum Hessian; its positivity and symmetry require no additional geometric input. -/
theorem chartGraphHamiltonian_momentum_block [FiniteDimensional ℝ V]
    (x₀ : M)
    {e : OpenPartialHomeomorph ((ℝ × V) × V) ((ℝ × V) × (V →L[ℝ] ℝ))}
    (he : (e : ((ℝ × V) × V) → ((ℝ × V) × (V →L[ℝ] ℝ))) =
      parametricLegendre (F.chartGraphLagrangian x₀))
    (hsub : e.source ⊆ (extChartAt 𝓘(ℝ, ℝ × V) x₀).target ×ˢ univ)
    (hG : ContDiffOn ℝ ∞ e.symm e.target)
    {p : (ℝ × V) × (V →L[ℝ] ℝ)} (hp : p ∈ e.target) :
    let L := F.chartGraphLagrangian x₀
    let C := GraphLegendre.inverseMomentumDerivative e p
    C = ContinuousLinearMap.inverse
        (fderiv ℝ (fderiv ℝ (fun η ↦ L ((e.symm p).1, η))) (e.symm p).2) ∧
      (∀ q : V →L[ℝ] ℝ, q ≠ 0 → 0 < q (C q)) ∧
      (∀ q r : V →L[ℝ] ℝ, r (C q) = q (C r)) ∧
      ∀ q r : V →L[ℝ] ℝ,
        fderiv ℝ (fderiv ℝ (GraphLegendre.hamiltonian L e)) p (0, q) (0, r) = r (C q) := by
  let L := F.chartGraphLagrangian x₀
  have hL : ContDiffOn ℝ ∞ L e.source := (hF.contDiffOn_chartGraphLength x₀).mono hsub
  have hLa := hL.contDiffAt (e.open_source.mem_nhds (e.map_target hp))
  have hGi := (hG.contDiffAt (e.open_target.mem_nhds hp)).differentiableAt (by simp)
  have hpos : ∀ w : V, w ≠ 0 → 0 < GraphLegendre.verticalHessian L (e.symm p) w w := by
    intro w hw
    exact hF.chartGraphLength_hessian_pos x₀ (hsub (e.map_target hp)).1 (e.symm p).2 hw
  exact ⟨GraphLegendre.inverseMomentumDerivative_eq_inverse he hp hLa hGi hpos,
    fun _ hq ↦ GraphLegendre.inverseMomentumDerivative_pos he hp hLa hGi hpos hq,
    GraphLegendre.inverseMomentumDerivative_symm he hp hLa hGi,
    GraphLegendre.hamiltonian_momentum_hessian_apply he hL hG hp⟩

/-- From the original Finsler data alone, construct the actual local partial Hamiltonian
and identify its positive momentum block everywhere on the constructed target. -/
theorem exists_smooth_chartGraphHamiltonian [FiniteDimensional ℝ V]
    (x₀ : M) {z : (ℝ × V) × V}
    (hz : z.1 ∈ (extChartAt 𝓘(ℝ, ℝ × V) x₀).target) :
    let L := F.chartGraphLagrangian x₀
    ∃ e : OpenPartialHomeomorph ((ℝ × V) × V) ((ℝ × V) × (V →L[ℝ] ℝ)),
      (e : ((ℝ × V) × V) → ((ℝ × V) × (V →L[ℝ] ℝ))) = parametricLegendre L ∧
      z ∈ e.source ∧ e.source ⊆ (extChartAt 𝓘(ℝ, ℝ × V) x₀).target ×ˢ univ ∧
      ContDiffOn ℝ ∞ e.symm e.target ∧
      ContDiffOn ℝ ∞ (GraphLegendre.hamiltonian L e) e.target ∧
      (∀ p ∈ e.target, (e.symm p).1 = p.1 ∧ fiberLegendre L (e.symm p) = p.2) ∧
      (∀ p ∈ e.target, ∀ dq : (ℝ × V) × (V →L[ℝ] ℝ),
        fderiv ℝ (GraphLegendre.hamiltonian L e) p dq =
          dq.2 (e.symm p).2 - GraphLegendre.baseDifferential L (e.symm p) dq.1) ∧
      ∀ p ∈ e.target,
        let C := GraphLegendre.inverseMomentumDerivative e p
        C = ContinuousLinearMap.inverse
            (fderiv ℝ (fderiv ℝ (fun η ↦ L ((e.symm p).1, η))) (e.symm p).2) ∧
          (∀ q : V →L[ℝ] ℝ, q ≠ 0 → 0 < q (C q)) ∧
          (∀ q r : V →L[ℝ] ℝ, r (C q) = q (C r)) ∧
          ∀ q r : V →L[ℝ] ℝ,
            fderiv ℝ (fderiv ℝ (GraphLegendre.hamiltonian L e)) p (0, q) (0, r) =
              r (C q) := by
  dsimp only
  obtain ⟨e, he, hzs, _, hsub, _, hG, _, _⟩ :=
    hF.exists_smooth_chartGraphLegendre_local_inverse x₀ hz
  have hL : ContDiffOn ℝ ∞ (F.chartGraphLagrangian x₀) e.source :=
    (hF.contDiffOn_chartGraphLength x₀).mono hsub
  refine ⟨e, he, hzs, hsub, hG, GraphLegendre.contDiffOn_hamiltonian hL hG,
    fun _ hp ↦ GraphLegendre.inverse_components he hp, ?_, ?_⟩
  · intro p hp dq
    exact GraphLegendre.hamiltonian_fderiv_apply he hp
      ((hL.contDiffAt (e.open_source.mem_nhds (e.map_target hp))).differentiableAt (by simp))
      ((hG.contDiffAt (e.open_target.mem_nhds hp)).differentiableAt (by simp)) dq
  · intro p hp
    exact hF.chartGraphHamiltonian_momentum_block x₀ he hsub hG hp

end IsSmoothStronglyConvex
end OTSelector.Geometry.ContinuousFinslerNorm

end
