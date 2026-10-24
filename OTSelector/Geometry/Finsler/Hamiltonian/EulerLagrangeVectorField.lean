import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Module.RCLike.Basic
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Geometry.Manifold.MFDeriv.Atlas
import Mathlib.Geometry.Manifold.Riemannian.PathELength
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Order.Compact
import OTSelector.Analysis.Convex.Legendre.Parametric
import OTSelector.Geometry.Finsler.Basic
import OTSelector.Geometry.Finsler.Energy.Basic
import OTSelector.Geometry.Finsler.Energy.Chart
import OTSelector.Geometry.Finsler.Hamiltonian.Basic

/-!
## Lemma skeleton

* **Conditions:** Smooth finite-dimensional Lagrangian with positive-definite velocity Hessian on an open phase domain.
* **Objects:** A position/velocity Euler–Lagrange vector field.
* **Proof detail:** Invert the derivative of the parametric Legendre map on the pair (velocity,base differential); read off the position and momentum equations.

## Mathematical sources

* Gerald Teschl, *Ordinary Differential Equations and Dynamical Systems (AMS 2012 author preliminary version)*, Section 8.3, pp. 238–240, equations (8.33)–(8.36) (action and Euler–Lagrange), (8.39)–(8.43) (Legendre transform and Hamilton equations), (8.47) (energy conservation).
  https://www.mat.univie.ac.at/~gerald/ftp/book-ode/ode.pdf#page=249
* Jiří Lebl, *Basic Analysis II: Introduction to Real Analysis, Volume II*, Sections 8.3–8.4, total derivative, chain rule and mean-value bounds; Section 8.6, higher derivatives.
  https://www.jirka.org/ra/realanal2.pdf

**Relationship to the sources:** This is the local coordinate form of the regular Euler–Lagrange ODE, with explicit invertibility and Fréchet identities derived from the Hessian.
-/

/-!
# The actual Euler--Lagrange vector field on position and velocity

Pull the canonical position-momentum derivative back by the inverse of the actual
joint Legendre differential. This defines a position-velocity vector field without
choosing a nonlinear Legendre inverse branch. Positive actual vertical Hessians make
that differential invertible; smooth inversion makes the field smooth throughout the
given open energy domain. Its first component is the actual velocity.

Differentiating a C2 position curve and its actual momentum shows that the genuine
Euler--Lagrange equation is precisely the resulting first-order phase equation. The
final wrappers use the original Finsler chart energy on its full slit chart domain.
No inverse branch, trajectory, normal chart, or differential identity is assumed.
-/

open Set Filter Manifold
open scoped Topology ContDiff

noncomputable section
namespace OTSelector.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The actual position-velocity field defined by inversion of the joint Legendre differential. -/
def eulerLagrangeVectorField (L : E × E → ℝ) (z : E × E) : E × E :=
  ContinuousLinearMap.inverse (fderiv ℝ (parametricLegendre L) z)
    (z.2, baseEnergyDifferential L z)

variable [FiniteDimensional ℝ E]

/-- A positive actual vertical Hessian makes the joint Legendre differential invertible. -/
theorem isInvertible_fderiv_parametricLegendre {L : E × E → ℝ} {z : E × E}
    (hL : ContDiffAt ℝ ∞ L z)
    (hpos : ∀ w : E, w ≠ 0 →
      0 < fderiv ℝ (fderiv ℝ (fun u ↦ L (z.1, u))) z.2 w w) :
    (fderiv ℝ (parametricLegendre L) z).IsInvertible := by
  let d := (LinearEquiv.ofBijective (fderiv ℝ (parametricLegendre L) z).toLinearMap
    (parametricLegendre_fderiv_bijective hL hpos)).toContinuousLinearEquiv
  exact ⟨d, rfl⟩

/-- Applying the actual joint Legendre differential recovers the canonical momentum equation. -/
theorem fderiv_parametricLegendre_eulerLagrangeVectorField
    {L : E × E → ℝ} {z : E × E} (hL : ContDiffAt ℝ ∞ L z)
    (hpos : ∀ w : E, w ≠ 0 →
      0 < fderiv ℝ (fderiv ℝ (fun u ↦ L (z.1, u))) z.2 w w) :
    fderiv ℝ (parametricLegendre L) z (eulerLagrangeVectorField L z) =
      (z.2, baseEnergyDifferential L z) := by
  obtain ⟨d, hd⟩ := isInvertible_fderiv_parametricLegendre hL hpos
  rw [eulerLagrangeVectorField, ← hd, ContinuousLinearMap.inverse_equiv]
  exact d.apply_symm_apply _

/-- The base component of the actual Euler--Lagrange field is the supplied velocity. -/
theorem eulerLagrangeVectorField_fst {L : E × E → ℝ} {z : E × E}
    (hL : ContDiffAt ℝ ∞ L z)
    (hpos : ∀ w : E, w ≠ 0 →
      0 < fderiv ℝ (fderiv ℝ (fun u ↦ L (z.1, u))) z.2 w w) :
    (eulerLagrangeVectorField L z).1 = z.2 := by
  have h := congrArg Prod.fst (fderiv_parametricLegendre_eulerLagrangeVectorField hL hpos)
  rw [parametricLegendre_fderiv_eq hL] at h
  exact h

/-- Smooth energy and its positive actual vertical Hessian give a smooth branch-free field. -/
theorem contDiffAt_eulerLagrangeVectorField {L : E × E → ℝ} {z : E × E}
    (hL : ContDiffAt ℝ ∞ L z)
    (hpos : ∀ w : E, w ≠ 0 →
      0 < fderiv ℝ (fderiv ℝ (fun u ↦ L (z.1, u))) z.2 w w) :
    ContDiffAt ℝ ∞ (eulerLagrangeVectorField L) z := by
  have hD : ContDiffAt ℝ ∞ (fderiv ℝ (parametricLegendre L)) z :=
    (contDiffAt_parametricLegendre hL).fderiv_right (by simp)
  have hi := (isInvertible_fderiv_parametricLegendre hL hpos).contDiffAt_map_inverse (n := ∞)
  exact (hi.comp z hD).clm_apply (contDiffAt_snd.prodMk (contDiffAt_baseEnergyDifferential hL))

/-- The actual Euler--Lagrange field is smooth on the entire regular energy domain. -/
theorem contDiffOn_eulerLagrangeVectorField {L : E × E → ℝ} {U : Set (E × E)}
    (hU : IsOpen U) (hL : ContDiffOn ℝ ∞ L U)
    (hpos : ∀ z ∈ U, ∀ w : E, w ≠ 0 →
      0 < fderiv ℝ (fderiv ℝ (fun u ↦ L (z.1, u))) z.2 w w) :
    ContDiffOn ℝ ∞ (eulerLagrangeVectorField L) U := by
  intro z hz
  exact (contDiffAt_eulerLagrangeVectorField
    (hL.contDiffAt (hU.mem_nhds hz)) (hpos z hz)).contDiffWithinAt

/-- A C2 position curve satisfying the actual momentum equation satisfies the branch-free
position-velocity ODE at the same time. -/
theorem hasDerivAt_positionVelocity_of_eulerLagrange
    {L : E × E → ℝ} {x : ℝ → E} {t : ℝ}
    (hL : ContDiffAt ℝ ∞ L (x t, deriv x t))
    (hpos : ∀ w : E, w ≠ 0 →
      0 < fderiv ℝ (fderiv ℝ (fun u ↦ L (x t, u))) (deriv x t) w w)
    (hx : ContDiffAt ℝ 2 x t)
    (hEL : HasDerivAt (fun s ↦ fiberLegendre L (x s, deriv x s))
      (baseEnergyDifferential L (x t, deriv x t)) t) :
    HasDerivAt (fun s ↦ (x s, deriv x s))
      (eulerLagrangeVectorField L (x t, deriv x t)) t := by
  have hd : HasDerivAt (fun s ↦ (x s, deriv x s))
      (deriv x t, deriv (deriv x) t) t :=
    (hx.differentiableAt (by norm_num)).hasDerivAt.prodMk
      ((hx.derivWithin (m := 1) (by norm_num)).differentiableAt_one).hasDerivAt
  have hm : HasDerivAt (fun s ↦ fiberLegendre L (x s, deriv x s))
      (fderiv ℝ (fiberLegendre L) (x t, deriv x t)
        (deriv x t, deriv (deriv x) t)) t := by
    simpa only [Function.comp_def] using
      ((contDiffAt_fiberLegendre hL).differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt t hd
  apply hd.congr_deriv
  apply (parametricLegendre_fderiv_bijective hL hpos).1
  rw [fderiv_parametricLegendre_eulerLagrangeVectorField hL hpos,
    parametricLegendre_fderiv_eq hL]
  exact Prod.ext rfl (hm.unique hEL)

/-- On an open time domain, every genuine C2 Euler--Lagrange curve obeys the actual
position-velocity field throughout its admissible phase trace. -/
theorem hasDerivAt_positionVelocity_of_eulerLagrange_on
    {L : E × E → ℝ} {U : Set (E × E)} (hU : IsOpen U)
    (hL : ContDiffOn ℝ ∞ L U)
    (hpos : ∀ z ∈ U, ∀ w : E, w ≠ 0 →
      0 < fderiv ℝ (fderiv ℝ (fun u ↦ L (z.1, u))) z.2 w w)
    {x : ℝ → E} {I : Set ℝ} (hI : IsOpen I) (hx : ContDiffOn ℝ 2 x I)
    (hphase : ∀ t ∈ I, (x t, deriv x t) ∈ U)
    (hEL : ∀ t ∈ I, HasDerivAt (fun s ↦ fiberLegendre L (x s, deriv x s))
      (baseEnergyDifferential L (x t, deriv x t)) t) :
    ∀ t ∈ I, HasDerivAt (fun s ↦ (x s, deriv x s))
      (eulerLagrangeVectorField L (x t, deriv x t)) t := by
  intro t ht
  exact hasDerivAt_positionVelocity_of_eulerLagrange
    (hL.contDiffAt (hU.mem_nhds (hphase t ht))) (hpos _ (hphase t ht))
    (hx.contDiffAt (hI.mem_nhds ht)) (hEL t ht)

/-- An actual phase solution has its velocity component as the true position derivative. -/
theorem hasDerivAt_position_of_eulerLagrangeVectorField
    {L : E × E → ℝ} {y : ℝ → E × E} {t : ℝ}
    (hL : ContDiffAt ℝ ∞ L (y t))
    (hpos : ∀ w : E, w ≠ 0 →
      0 < fderiv ℝ (fderiv ℝ (fun u ↦ L ((y t).1, u))) (y t).2 w w)
    (hy : HasDerivAt y (eulerLagrangeVectorField L (y t)) t) :
    HasDerivAt (fun s ↦ (y s).1) (y t).2 t := by
  have hd : HasDerivAt (fun s ↦ (y s).1) (eulerLagrangeVectorField L (y t)).1 t := hy.fst
  rwa [eulerLagrangeVectorField_fst hL hpos] at hd

/-- The actual momentum of a phase solution differentiates to the actual base differential. -/
theorem hasDerivAt_momentum_of_eulerLagrangeVectorField
    {L : E × E → ℝ} {y : ℝ → E × E} {t : ℝ}
    (hL : ContDiffAt ℝ ∞ L (y t))
    (hpos : ∀ w : E, w ≠ 0 →
      0 < fderiv ℝ (fderiv ℝ (fun u ↦ L ((y t).1, u))) (y t).2 w w)
    (hy : HasDerivAt y (eulerLagrangeVectorField L (y t)) t) :
    HasDerivAt (fun s ↦ fiberLegendre L (y s)) (baseEnergyDifferential L (y t)) t := by
  have h := ((contDiffAt_parametricLegendre hL).differentiableAt (by simp)).hasFDerivAt
    |>.comp_hasDerivAt t hy
  rw [fderiv_parametricLegendre_eulerLagrangeVectorField hL hpos] at h
  have hs : HasDerivAt (fun s ↦ (parametricLegendre L (y s)).2)
      (baseEnergyDifferential L (y t)) t := h.snd
  exact hs

/-- A solution of the actual position-velocity ODE on an open domain satisfies the true
Euler--Lagrange equation for its position projection and its actual time derivative. -/
theorem hasDerivAt_eulerLagrange_of_positionVelocity
    {L : E × E → ℝ} {U : Set (E × E)} (hU : IsOpen U)
    (hL : ContDiffOn ℝ ∞ L U)
    (hpos : ∀ z ∈ U, ∀ w : E, w ≠ 0 →
      0 < fderiv ℝ (fderiv ℝ (fun u ↦ L (z.1, u))) z.2 w w)
    {y : ℝ → E × E} {I : Set ℝ} (hI : IsOpen I) (hphase : MapsTo y I U)
    (hy : ∀ t ∈ I, HasDerivAt y (eulerLagrangeVectorField L (y t)) t)
    {t : ℝ} (ht : t ∈ I) :
    HasDerivAt
      (fun s ↦ fiberLegendre L ((y s).1, deriv (fun u ↦ (y u).1) s))
      (baseEnergyDifferential L ((y t).1, deriv (fun u ↦ (y u).1) t)) t := by
  have hLat : ∀ s ∈ I, ContDiffAt ℝ ∞ L (y s) :=
    fun s hs ↦ hL.contDiffAt (hU.mem_nhds (hphase hs))
  have hactual : ∀ s ∈ I, ((y s).1, deriv (fun u ↦ (y u).1) s) = y s := by
    intro s hs
    rw [(hasDerivAt_position_of_eulerLagrangeVectorField
      (hLat s hs) (hpos _ (hphase hs)) (hy s hs)).deriv]
  rw [hactual t ht]
  apply (hasDerivAt_momentum_of_eulerLagrangeVectorField
    (hLat t ht) (hpos _ (hphase ht)) (hy t ht)).congr_of_eventuallyEq
  filter_upwards [hI.mem_nhds ht] with s hs
  rw [hactual s hs]

namespace ContinuousFinslerNorm.IsSmoothStronglyConvex

variable {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] {F : ContinuousFinslerNorm E M}

/-- The original Finsler energy has a smooth actual phase field on its full slit chart domain. -/
theorem contDiffOn_chartEulerLagrangeVectorField (hF : F.IsSmoothStronglyConvex) (x₀ : M) :
    ContDiffOn ℝ ∞ (eulerLagrangeVectorField (F.chartEnergy x₀)) (chartEnergyDomain x₀) :=
  contDiffOn_eulerLagrangeVectorField (isOpen_chartEnergyDomain x₀)
    (hF.contDiffOn_chartEnergy x₀) (fun _ hz _ hw ↦ hF.chartEnergy_hessian_pos x₀ hz hw)

/-- The original Finsler phase field retains the prescribed velocity as its base derivative. -/
theorem chartEulerLagrangeVectorField_fst (hF : F.IsSmoothStronglyConvex) (x₀ : M)
    {z : E × E} (hz : z ∈ chartEnergyDomain x₀) :
    (eulerLagrangeVectorField (F.chartEnergy x₀) z).1 = z.2 :=
  eulerLagrangeVectorField_fst
    ((hF.contDiffOn_chartEnergy x₀).contDiffAt ((isOpen_chartEnergyDomain x₀).mem_nhds hz))
    (fun _ hw ↦ hF.chartEnergy_hessian_pos x₀ hz hw)

/-- Every actual admissible C2 Finsler Euler--Lagrange curve solves the full slit-chart
position-velocity ODE, without a chosen Legendre inverse branch. -/
theorem hasDerivAt_chartEulerLagrange_positionVelocity (hF : F.IsSmoothStronglyConvex)
    (x₀ : M) {x : ℝ → E} {I : Set ℝ} (hI : IsOpen I) (hx : ContDiffOn ℝ 2 x I)
    (hphase : ∀ t ∈ I, (x t, deriv x t) ∈ chartEnergyDomain x₀)
    (hEL : ∀ t ∈ I,
      HasDerivAt (fun s ↦ fiberLegendre (F.chartEnergy x₀) (x s, deriv x s))
        (baseEnergyDifferential (F.chartEnergy x₀) (x t, deriv x t)) t) :
    ∀ t ∈ I, HasDerivAt (fun s ↦ (x s, deriv x s))
      (eulerLagrangeVectorField (F.chartEnergy x₀) (x t, deriv x t)) t :=
  hasDerivAt_positionVelocity_of_eulerLagrange_on (isOpen_chartEnergyDomain x₀)
    (hF.contDiffOn_chartEnergy x₀) (fun _ hz _ hw ↦ hF.chartEnergy_hessian_pos x₀ hz hw)
    hI hx hphase hEL

/-- Every admissible actual Finsler phase-field solution recovers the genuine chart
Euler--Lagrange equation for its position, using its true time velocity. -/
theorem hasDerivAt_chartEulerLagrange_of_positionVelocity (hF : F.IsSmoothStronglyConvex)
    (x₀ : M) {y : ℝ → E × E} {I : Set ℝ} (hI : IsOpen I)
    (hphase : MapsTo y I (chartEnergyDomain x₀))
    (hy : ∀ t ∈ I,
      HasDerivAt y (eulerLagrangeVectorField (F.chartEnergy x₀) (y t)) t)
    {t : ℝ} (ht : t ∈ I) :
    HasDerivAt
      (fun s ↦ fiberLegendre (F.chartEnergy x₀) ((y s).1, deriv (fun u ↦ (y u).1) s))
      (baseEnergyDifferential (F.chartEnergy x₀) ((y t).1, deriv (fun u ↦ (y u).1) t)) t :=
  hasDerivAt_eulerLagrange_of_positionVelocity (isOpen_chartEnergyDomain x₀)
    (hF.contDiffOn_chartEnergy x₀) (fun _ hz _ hw ↦ hF.chartEnergy_hessian_pos x₀ hz hw)
    hI hphase hy ht

end ContinuousFinslerNorm.IsSmoothStronglyConvex
end OTSelector.Geometry
