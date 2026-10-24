import OTSelector.Analysis.Convex.Legendre.Parametric
import OTSelector.Geometry.Finsler.Hamiltonian.Basic
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Geometry.EulerLagrangeReparam.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Geometry.EulerLagrangeReparam`; the selected original proof blocks follow. -/
section

/-!
Conditions: A positive derivative of the time change, degree-zero momentum and degree-one base derivative under positive velocity scaling, and an actual Euler–Lagrange curve.

Objects: Euler–Lagrange germs and interval equations after reparametrization.

Proof detail: Differentiate the composed momentum, use the positive homogeneity identities and cancel the time derivative in the base term.

Sources: Gerald Teschl, Section 8.3, pp. 238–240, equations (8.33)–(8.36) (action and Euler–Lagrange), (8.39)–(8.43) (Legendre transform and Hamilton equations), (8.47) (energy conservation) (https://www.mat.univie.ac.at/~gerald/ftp/book-ode/ode.pdf#page=249); Matias Dahl, Section 1, Proposition 1.1, p. 3; Section 1.1, Definition 1.2 and Remarks 1.3(4), pp. 4–5 (https://math.aalto.fi/~fdahl/finsler/finsler.pdf#page=3); Jiří Lebl, Section 8.3, Theorem 8.3.7, p. 38; Exercise 8.3.7, p. 45 (differentiate the inverse identity) (https://www.jirka.org/ra/realanal2.pdf#page=38).
Relation: Derived reparametrization identities; the homogeneity assumptions are explicit rather than silently inferred for arbitrary Lagrangians.
-/

/-!
# Positive time changes of length Euler--Lagrange equations

A degree-zero momentum and degree-one base differential give invariance under a
positive differentiable change of time. The proof differentiates the same momentum
along the original curve and identifies both new differentials by homogeneity.
The local version uses germs, so actual local graph inverses can supply the time change.
-/

open Set Filter
open scoped Topology

noncomputable section
namespace OTSelector.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Curves agreeing near a time have the same actual Euler--Lagrange equation there. -/
theorem hasDerivAt_eulerLagrange_congr {L : E × E → ℝ} {x y : ℝ → E} {t : ℝ}
    (hxy : x =ᶠ[𝓝 t] y)
    (hEL : HasDerivAt (fun s ↦ fiberLegendre L (x s, deriv x s))
      (baseEnergyDifferential L (x t, deriv x t)) t) :
    HasDerivAt (fun s ↦ fiberLegendre L (y s, deriv y s))
      (baseEnergyDifferential L (y t, deriv y t)) t := by
  rw [← hxy.eq_of_nhds, ← hxy.deriv_eq]
  apply hEL.congr_of_eventuallyEq
  filter_upwards [hxy, hxy.deriv] with s hs hds
  rw [hs, hds]

/-- Actual Euler--Lagrange equations survive a positive time change on a local germ. -/
theorem hasDerivAt_eulerLagrange_reparam {L : E × E → ℝ} {O : Set (E × E)}
    (hp : ∀ z ∈ O, ∀ a : ℝ, 0 < a →
      fiberLegendre L (z.1, a • z.2) = fiberLegendre L z)
    (hb : ∀ z ∈ O, ∀ a : ℝ, 0 < a →
      baseEnergyDifferential L (z.1, a • z.2) = a • baseEnergyDifferential L z)
    {x : ℝ → E} {τ : ℝ → ℝ} {t : ℝ}
    (hreg : ∀ᶠ s in 𝓝 t, DifferentiableAt ℝ x (τ s) ∧ DifferentiableAt ℝ τ s ∧
      0 < deriv τ s ∧ (x (τ s), deriv x (τ s)) ∈ O)
    (hEL : HasDerivAt (fun s ↦ fiberLegendre L (x s, deriv x s))
      (baseEnergyDifferential L (x (τ t), deriv x (τ t))) (τ t)) :
    HasDerivAt (fun s ↦ fiberLegendre L ((x ∘ τ) s, deriv (x ∘ τ) s))
      (baseEnergyDifferential L ((x ∘ τ) t, deriv (x ∘ τ) t)) t := by
  obtain ⟨hx, hτ, hpos, hphase⟩ := hreg.self_of_nhds
  have hd := hEL.scomp t hτ.hasDerivAt
  have hforce : baseEnergyDifferential L ((x ∘ τ) t, deriv (x ∘ τ) t) =
      deriv τ t • baseEnergyDifferential L (x (τ t), deriv x (τ t)) := by
    rw [deriv.scomp t hx hτ]
    exact hb (x (τ t), deriv x (τ t)) hphase (deriv τ t) hpos
  rw [hforce]
  apply hd.congr_of_eventuallyEq
  filter_upwards [hreg] with s hs
  rw [deriv.scomp s hs.1 hs.2.1]
  exact hp (x (τ s), deriv x (τ s)) hs.2.2.2 (deriv τ s) hs.2.2.1

/-- A positive differentiable reparameterization preserves the actual equations
on open time sets. -/
theorem eulerLagrange_reparam_on {L : E × E → ℝ} {O : Set (E × E)}
    (hp : ∀ z ∈ O, ∀ a : ℝ, 0 < a →
      fiberLegendre L (z.1, a • z.2) = fiberLegendre L z)
    (hb : ∀ z ∈ O, ∀ a : ℝ, 0 < a →
      baseEnergyDifferential L (z.1, a • z.2) = a • baseEnergyDifferential L z)
    {x : ℝ → E} {τ : ℝ → ℝ} {I J : Set ℝ} (hJ : IsOpen J)
    (hx : ∀ s ∈ I, DifferentiableAt ℝ x s)
    (hτ : ∀ s ∈ J, DifferentiableAt ℝ τ s)
    (hpos : ∀ s ∈ J, 0 < deriv τ s) (hmap : MapsTo τ J I)
    (hphase : ∀ s ∈ I, (x s, deriv x s) ∈ O)
    (hEL : ∀ s ∈ I, HasDerivAt (fun r ↦ fiberLegendre L (x r, deriv x r))
      (baseEnergyDifferential L (x s, deriv x s)) s) :
    ∀ t ∈ J, HasDerivAt (fun s ↦ fiberLegendre L ((x ∘ τ) s, deriv (x ∘ τ) s))
      (baseEnergyDifferential L ((x ∘ τ) t, deriv (x ∘ τ) t)) t := by
  intro t ht
  apply hasDerivAt_eulerLagrange_reparam hp hb _ (hEL (τ t) (hmap ht))
  filter_upwards [hJ.mem_nhds ht] with s hs
  exact ⟨hx _ (hmap hs), hτ s hs, hpos s hs, hphase _ (hmap hs)⟩

end OTSelector.Geometry

end
end
