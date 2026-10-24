import OTSelector.Analysis.Convex.Legendre.Parametric
import OTSelector.Analysis.ODE.Hamiltonian.GraphDynamics
import OTSelector.Geometry.Finsler.Hamiltonian.Basic
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Geometry.GraphEulerLagrange.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Geometry.GraphEulerLagrange`; the selected original proof blocks follow. -/
section

/-!
Conditions: An actual differentiable ambient Lagrangian and a differentiable graph curve whose ambient momentum satisfies Euler–Lagrange on an open interval.

Objects: Fiber and position derivatives of the graph restriction, and the projected Euler–Lagrange equation.

Proof detail: Apply the chain rule to velocity insertion (1,η), restrict both covectors to the position directions, and compose the given derivative identity with that restriction.

Sources: Gerald Teschl, Section 8.3, pp. 238–240, equations (8.33)–(8.36) (action and Euler–Lagrange), (8.39)–(8.43) (Legendre transform and Hamilton equations), (8.47) (energy conservation) (https://www.mat.univie.ac.at/~gerald/ftp/book-ode/ode.pdf#page=249); Jiří Lebl, Section 8.3, Theorem 8.3.7, p. 38; Exercise 8.3.7, p. 45 (differentiate the inverse identity) (https://www.jirka.org/ra/realanal2.pdf#page=38).
Relation: Direct coordinate restriction of the classical Euler–Lagrange equation; the normed-space statement is proved locally.
-/

/-!
# Euler--Lagrange equations for actual graph restrictions

Restrict an ambient scalar Lagrangian to velocities `(1, eta)`. The true graph momentum
is the ambient momentum restricted to the position directions. The graph position
partial has the same restriction of the actual ambient base differential. Projecting
the actual Euler--Lagrange equation for the graph curve `(s, y(s))` therefore gives the
genuine graph equation. No separate projected momentum or equation is assumed.
-/

open Set Filter
open scoped Topology

noncomputable section
namespace OTSelector.Geometry

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- Graph momentum is the restriction of the true ambient momentum to spatial directions. -/
theorem fiberLegendre_graphRestriction {L : (ℝ × V) × (ℝ × V) → ℝ}
    {z : (ℝ × V) × V} (hL : DifferentiableAt ℝ L (z.1, (1, z.2))) :
    fiberLegendre (fun z : (ℝ × V) × V ↦ L (z.1, (1, z.2))) z =
      (fiberLegendre L (z.1, (1, z.2))).comp (ContinuousLinearMap.inr ℝ ℝ V) := by
  have hi : DifferentiableAt ℝ (fun v : ℝ × V ↦ (z.1, v)) (1, z.2) :=
    (differentiableAt_const z.1).prodMk differentiableAt_id
  have hd : DifferentiableAt ℝ (fun v : ℝ × V ↦ L (z.1, v)) (1, z.2) := by
    simpa only [Function.comp_def] using! hL.comp (1, z.2) hi
  exact (hd.hasFDerivAt.comp z.2 (hasFDerivAt_prodMk_right (𝕜 := ℝ) 1 z.2)).fderiv

/-- The graph position partial is the true ambient base differential restricted to space. -/
theorem positionDifferential_graphRestriction (L : (ℝ × V) × (ℝ × V) → ℝ)
    (z : (ℝ × V) × V) :
    GraphHamiltonian.positionDifferential (fun z : (ℝ × V) × V ↦ L (z.1, (1, z.2))) z =
      (baseEnergyDifferential L (z.1, (1, z.2))).comp
        (ContinuousLinearMap.inr ℝ ℝ V) := rfl

/-- The actual ambient equation along a graph curve projects to its genuine graph equation. -/
theorem eulerLagrange_graphRestriction {L : (ℝ × V) × (ℝ × V) → ℝ}
    {y : ℝ → V} {I : Set ℝ} (hI : IsOpen I)
    (hy : ∀ s ∈ I, DifferentiableAt ℝ y s)
    (hL : ∀ s ∈ I, DifferentiableAt ℝ L ((s, y s), (1, deriv y s)))
    (hEL : ∀ t ∈ I, HasDerivAt
      (fun s ↦ fiberLegendre L ((s, y s), deriv (fun u ↦ (u, y u)) s))
      (baseEnergyDifferential L ((t, y t), deriv (fun u ↦ (u, y u)) t)) t) :
    ∀ t ∈ I, HasDerivAt
      (fun s ↦ fiberLegendre (fun z : (ℝ × V) × V ↦ L (z.1, (1, z.2)))
        ((s, y s), deriv y s))
      (GraphHamiltonian.positionDifferential
        (fun z : (ℝ × V) × V ↦ L (z.1, (1, z.2))) ((t, y t), deriv y t)) t := by
  have hγ (s : ℝ) (hs : s ∈ I) : deriv (fun u ↦ (u, y u)) s = (1, deriv y s) :=
    ((hasDerivAt_id s).prodMk (hy s hs).hasDerivAt).deriv
  intro t ht
  have hd := (hEL t ht).clm_comp
    (hasDerivAt_const t (ContinuousLinearMap.inr ℝ ℝ V))
  simp only [ContinuousLinearMap.comp_zero, add_zero, hγ t ht] at hd
  rw [positionDifferential_graphRestriction]
  apply hd.congr_of_eventuallyEq
  filter_upwards [hI.mem_nhds ht] with s hs
  rw [fiberLegendre_graphRestriction (hL s hs), hγ s hs]

end OTSelector.Geometry

end
end
