import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import OTSelector.Analysis.Convex.Legendre.Parametric
import OTSelector.Geometry.Finsler.Hamiltonian.Basic

/-!
## Lemma skeleton

* **Conditions:** Two energies equal on a neighborhood or on an open phase domain containing the curve.
* **Objects:** Fiber/base derivatives and the Euler–Lagrange equation determined by an energy germ.
* **Proof detail:** Use locality of derivatives and transfer the momentum curve equality along the phase.

## Mathematical sources

* Jiří Lebl, *Basic Analysis II: Introduction to Real Analysis, Volume II*, Sections 8.3–8.4, total derivative, chain rule and mean-value bounds; Section 8.6, higher derivatives.
  https://www.jirka.org/ra/realanal2.pdf
* Gerald Teschl, *Ordinary Differential Equations and Dynamical Systems (AMS 2012 author preliminary version)*, Section 8.3, pp. 238–240, equations (8.33)–(8.36) (action and Euler–Lagrange), (8.39)–(8.43) (Legendre transform and Hamilton equations), (8.47) (energy conservation).
  https://www.mat.univie.ac.at/~gerald/ftp/book-ode/ode.pdf#page=249

**Relationship to the sources:** These are implementation adapters for the locality of differentiation; they do not require an extra invariance theorem.
-/

/-!
# Locality of the actual Euler--Lagrange equation

The partial differentials of a scalar energy depend only on its local germ. Consequently,
equality of two energies on an open phase domain identifies their Euler--Lagrange equations
on every open time interval whose actual position-velocity graph stays in that domain.
No differentiability of either energy is needed for this locality statement: the actual
`fderiv` values and the actual `HasDerivAt` assertions are compared on equal germs.

This supplies the overlap step when a Finsler chart energy equals the pullback of another
chart energy only locally. Coordinate covariance itself is a separate calculus theorem.
-/

open Set Filter
open scoped Topology ContDiff

namespace OTSelector.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The actual fiber differential only depends on the germ of the energy. -/
theorem fiberLegendre_eq_of_eventuallyEq {L K : E × E → ℝ} {z : E × E}
    (h : L =ᶠ[𝓝 z] K) : fiberLegendre L z = fiberLegendre K z := by
  have he : (fun w : E ↦ L (z.1, w)) =ᶠ[𝓝 z.2] (fun w : E ↦ K (z.1, w)) :=
    h.comp_tendsto (continuousAt_const.prodMk continuousAt_id)
  exact he.fderiv_eq

/-- The actual base differential only depends on the germ of the energy. -/
theorem baseEnergyDifferential_eq_of_eventuallyEq {L K : E × E → ℝ} {z : E × E}
    (h : L =ᶠ[𝓝 z] K) : baseEnergyDifferential L z = baseEnergyDifferential K z := by
  have he : (fun u : E ↦ L (u, z.2)) =ᶠ[𝓝 z.1] (fun u : E ↦ K (u, z.2)) :=
    h.comp_tendsto (continuousAt_id.prodMk continuousAt_const)
  exact he.fderiv_eq

/-- Equality of energies on an open phase domain identifies both actual partial differentials. -/
theorem energyDifferentials_eq_of_eqOn {L K : E × E → ℝ} {U : Set (E × E)}
    (hU : IsOpen U) (h : EqOn L K U) {z : E × E} (hz : z ∈ U) :
    fiberLegendre L z = fiberLegendre K z ∧
      baseEnergyDifferential L z = baseEnergyDifferential K z := by
  have he := h.eventuallyEq_of_mem (hU.mem_nhds hz)
  exact ⟨fiberLegendre_eq_of_eventuallyEq he, baseEnergyDifferential_eq_of_eventuallyEq he⟩

/-- Local equality of energies preserves the Euler--Lagrange equation along a curve.
Only membership of its actual position-velocity graph in the open energy domain is needed. -/
theorem eulerLagrange_congr_of_eqOn {L K : E × E → ℝ} {U : Set (E × E)}
    {I : Set ℝ} {x : ℝ → E} (hU : IsOpen U) (hI : IsOpen I) (h : EqOn L K U)
    (hphase : ∀ t ∈ I, (x t, deriv x t) ∈ U) :
    (∀ t ∈ I, HasDerivAt (fun s ↦ fiberLegendre L (x s, deriv x s))
      (baseEnergyDifferential L (x t, deriv x t)) t) ↔
    (∀ t ∈ I, HasDerivAt (fun s ↦ fiberLegendre K (x s, deriv x s))
      (baseEnergyDifferential K (x t, deriv x t)) t) := by
  have he (t : ℝ) (ht : t ∈ I) := energyDifferentials_eq_of_eqOn hU h (hphase t ht)
  have hp (t : ℝ) (ht : t ∈ I) :
      (fun s ↦ fiberLegendre L (x s, deriv x s)) =ᶠ[𝓝 t]
        (fun s ↦ fiberLegendre K (x s, deriv x s)) := by
    filter_upwards [hI.mem_nhds ht] with s hs
    exact (he s hs).1
  constructor
  · intro hEL t ht
    rw [← (he t ht).2]
    exact (hp t ht).hasDerivAt_iff.mp (hEL t ht)
  · intro hEL t ht
    rw [(he t ht).2]
    exact (hp t ht).hasDerivAt_iff.mpr (hEL t ht)

end OTSelector.Geometry
