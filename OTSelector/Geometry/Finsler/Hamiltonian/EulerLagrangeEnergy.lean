import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.AffineMap
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Module.RCLike.Basic
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.MFDeriv.Atlas
import Mathlib.Geometry.Manifold.MFDeriv.FDeriv
import Mathlib.Geometry.Manifold.Riemannian.PathELength
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Order.Compact
import OTSelector.Analysis.Convex.Legendre.Parametric
import OTSelector.Geometry.Finsler.Basic
import OTSelector.Geometry.Finsler.Calibration.Chart
import OTSelector.Geometry.Finsler.Energy.Basic
import OTSelector.Geometry.Finsler.Energy.Chart
import OTSelector.Geometry.Finsler.Geodesic.Proofs.LocalEquation
import OTSelector.Geometry.Finsler.Hamiltonian.Basic

/-!
## Lemma skeleton

* **Conditions:** An autonomous differentiable Lagrangian and a C2 Euler–Lagrange curve; positive smooth Finsler energy only for the specialization.
* **Objects:** The energy p(v)−L, then the quadratic Finsler energy and speed.
* **Proof detail:** Differentiate p(v)−L, cancel the Euler–Lagrange terms, and use two-homogeneous Euler identity to identify it with L.

## Mathematical sources

* Gerald Teschl, *Ordinary Differential Equations and Dynamical Systems (AMS 2012 author preliminary version)*, Section 8.3, pp. 238–240, equations (8.33)–(8.36) (action and Euler–Lagrange), (8.39)–(8.43) (Legendre transform and Hamilton equations), (8.47) (energy conservation).
  https://www.mat.univie.ac.at/~gerald/ftp/book-ode/ode.pdf#page=249
* Zhongmin Shen, *Landsberg Curvature, S-Curvature and Riemann Curvature, MSRI Publications 50 (2004)*, Section 2, pp. 304–305 (Minkowski norms and Finsler metrics), p. 308 (Legendre duality, equation (2–12)).
  https://library.slmath.org/books/Book50/files/08Sh.pdf#page=2

**Relationship to the sources:** Energy conservation is classical; the connected-open-interval and chart-speed equality APIs are proved corollaries.
-/

/-!
# Energy conservation for actual Euler--Lagrange curves

The energy of an autonomous Lagrangian is its momentum paired with velocity minus
the Lagrangian. Differentiating along an actual Euler--Lagrange solution cancels the
two terms. For the genuine two-homogeneous Finsler energy this conserved quantity
is the original energy itself, so the original speed is constant on every connected
open solution interval. No chosen Legendre branch or prescribed constant speed is needed.
-/

open Set Filter Manifold
open scoped Topology ContDiff

noncomputable section
namespace OTSelector.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The energy associated with the actual autonomous scalar Lagrangian. -/
def lagrangianEnergy (L : E × E → ℝ) (z : E × E) : ℝ :=
  fiberLegendre L z z.2 - L z

/-- The actual Euler--Lagrange equation makes the energy derivative vanish. -/
theorem hasDerivAt_lagrangianEnergy_zero {L : E × E → ℝ} {x : ℝ → E} {t : ℝ}
    (hL : DifferentiableAt ℝ L (x t, deriv x t))
    (hx : DifferentiableAt ℝ x t) (hv : DifferentiableAt ℝ (deriv x) t)
    (hEL : HasDerivAt (fun s ↦ fiberLegendre L (x s, deriv x s))
      (baseEnergyDifferential L (x t, deriv x t)) t) :
    HasDerivAt (fun s ↦ lagrangianEnergy L (x s, deriv x s)) 0 t := by
  have hderiv := hL.hasFDerivAt.comp_hasDerivAt t (hx.hasDerivAt.prodMk hv.hasDerivAt)
  rw [fderiv_energy_split hL] at hderiv
  simpa only [lagrangianEnergy, sub_self] using! (hEL.clm_apply hv.hasDerivAt).sub hderiv

/-- Autonomous Lagrangian energy is constant on a connected open interval of C2 solutions. -/
theorem lagrangianEnergy_eq_of_eulerLagrange {L : E × E → ℝ} {x : ℝ → E} {I : Set ℝ}
    (hI : IsOpen I) (hconn : IsPreconnected I) (hx : ContDiffOn ℝ 2 x I)
    (hL : ∀ t ∈ I, DifferentiableAt ℝ L (x t, deriv x t))
    (hEL : ∀ t ∈ I, HasDerivAt (fun s ↦ fiberLegendre L (x s, deriv x s))
      (baseEnergyDifferential L (x t, deriv x t)) t)
    {s t : ℝ} (hs : s ∈ I) (ht : t ∈ I) :
    lagrangianEnergy L (x s, deriv x s) = lagrangianEnergy L (x t, deriv x t) := by
  have hd u hu := hasDerivAt_lagrangianEnergy_zero (hL u hu)
    ((hx.contDiffAt (hI.mem_nhds hu)).differentiableAt (by norm_num))
    (((hx.deriv_of_isOpen hI (m := 1) (by norm_num)).contDiffAt
      (hI.mem_nhds hu)).differentiableAt (by norm_num)) (hEL u hu)
  exact hI.is_const_of_deriv_eq_zero hconn
    (fun u hu ↦ (hd u hu).differentiableAt.differentiableWithinAt)
    (fun u hu ↦ (hd u hu).deriv) hs ht

namespace ContinuousFinslerNorm.IsSmoothStronglyConvex

variable {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] {F : ContinuousFinslerNorm E M}

/-- Two-homogeneity identifies autonomous energy with the original Finsler chart energy. -/
theorem lagrangianEnergy_chartEnergy (hF : F.IsSmoothStronglyConvex) (x₀ : M)
    {z : E × E} (hz : z ∈ ContinuousFinslerNorm.chartEnergyDomain x₀) :
    lagrangianEnergy (F.chartEnergy x₀) z = F.chartEnergy x₀ z := by
  rw [lagrangianEnergy, hF.chartEnergy_euler x₀ hz]
  ring

/-- Every actual C2 slit Euler--Lagrange solution conserves the original Finsler energy. -/
theorem chartEnergy_eq_of_eulerLagrange (hF : F.IsSmoothStronglyConvex) (x₀ : M)
    {x : ℝ → E} {I : Set ℝ} (hI : IsOpen I) (hconn : IsPreconnected I)
    (hx : ContDiffOn ℝ 2 x I)
    (hphase : ∀ t ∈ I, (x t, deriv x t) ∈ ContinuousFinslerNorm.chartEnergyDomain x₀)
    (hEL : ∀ t ∈ I, HasDerivAt
      (fun s ↦ fiberLegendre (F.chartEnergy x₀) (x s, deriv x s))
      (baseEnergyDifferential (F.chartEnergy x₀) (x t, deriv x t)) t)
    {s t : ℝ} (hs : s ∈ I) (ht : t ∈ I) :
    F.chartEnergy x₀ (x s, deriv x s) = F.chartEnergy x₀ (x t, deriv x t) := by
  rw [← hF.lagrangianEnergy_chartEnergy x₀ (hphase s hs),
    ← hF.lagrangianEnergy_chartEnergy x₀ (hphase t ht)]
  exact lagrangianEnergy_eq_of_eulerLagrange hI hconn hx
    (fun u hu ↦ ((hF.contDiffOn_chartEnergy x₀).contDiffAt
      ((ContinuousFinslerNorm.isOpen_chartEnergyDomain x₀).mem_nhds (hphase u hu))).differentiableAt
        (by simp)) hEL hs ht

/-- The original chart speed of every actual C2 slit Euler--Lagrange solution is constant. -/
theorem chartLength_eq_of_eulerLagrange (hF : F.IsSmoothStronglyConvex) (x₀ : M)
    {x : ℝ → E} {I : Set ℝ} (hI : IsOpen I) (hconn : IsPreconnected I)
    (hx : ContDiffOn ℝ 2 x I)
    (hphase : ∀ t ∈ I, (x t, deriv x t) ∈ ContinuousFinslerNorm.chartEnergyDomain x₀)
    (hEL : ∀ t ∈ I, HasDerivAt
      (fun s ↦ fiberLegendre (F.chartEnergy x₀) (x s, deriv x s))
      (baseEnergyDifferential (F.chartEnergy x₀) (x t, deriv x t)) t)
    {s t : ℝ} (hs : s ∈ I) (ht : t ∈ I) :
    F.chartLength x₀ (x s, deriv x s) = F.chartLength x₀ (x t, deriv x t) :=
  F.chartLength_eq_of_chartEnergy_eq x₀
    (hF.chartEnergy_eq_of_eulerLagrange x₀ hI hconn hx hphase hEL hs ht)

end ContinuousFinslerNorm.IsSmoothStronglyConvex
end OTSelector.Geometry
