import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Module.RCLike.Basic
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Geometry.Manifold.MFDeriv.Atlas
import Mathlib.Geometry.Manifold.MFDeriv.FDeriv
import Mathlib.Geometry.Manifold.Riemannian.PathELength
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Order.Compact
import OTSelector.Analysis.Convex.HomogeneousEnergy
import OTSelector.Analysis.Convex.Legendre.Parametric
import OTSelector.Geometry.Finsler.Basic
import OTSelector.Geometry.Finsler.Energy.Basic
import OTSelector.Geometry.Finsler.Energy.Chart
import OTSelector.Geometry.Finsler.Energy.Transition
import OTSelector.Geometry.Finsler.Hamiltonian.Basic
import OTSelector.Geometry.Finsler.Hamiltonian.EulerLagrangeCovariance
import OTSelector.Geometry.Finsler.Hamiltonian.EulerLagrangeLocality
import OTSelector.Geometry.Finsler.Hamiltonian.IntegralCurve
import OTSelector.Geometry.Manifold.TangentChartCurve

/-!
# Local coordinate construction and uniqueness of Finsler geodesics

Main declarations: exists_localEulerLagrange; exists_localEulerLagrange_constantSpeed; manifoldEulerLagrange_eventuallyEq_of_same_initial_data.

This file contains the original declarations and their proofs. The source-unit
sections below preserve each unit's conditions, objects, proof details and
book or paper locations.
-/

/-! Source unit: `OTSelector.Geometry.Finsler.Geodesic.Covariance`. Its original mathematical documentation follows. -/
section

/-!
## Lemma skeleton

* **Conditions:** An EL curve in an old chart whose phase remains in a smooth chart overlap.
* **Objects:** The Euler–Lagrange equation after recharting.
* **Proof detail:** Combine energy pullback identity, derivative invertibility of chart transition and the general EL covariance theorem.

## Mathematical sources

* Gerald Teschl, *Ordinary Differential Equations and Dynamical Systems (AMS 2012 author preliminary version)*, Section 8.3, pp. 238–240, equations (8.33)–(8.36) (action and Euler–Lagrange), (8.39)–(8.43) (Legendre transform and Hamilton equations), (8.47) (energy conservation).
  https://www.mat.univie.ac.at/~gerald/ftp/book-ode/ode.pdf#page=249
* John M. Lee, *Introduction to Smooth Manifolds, second edition (2013)*, Chapter 3, sections “The Differential of a Smooth Map” pp. 55–59, “Computations in Coordinates” pp. 60–64, “The Tangent Bundle” pp. 65–67, “Velocity Vectors of Curves” pp. 68–70.
  https://sites.math.washington.edu/~lee/Books/ISM/front-matter.pdf#page=10
* Jiří Lebl, *Basic Analysis II: Introduction to Real Analysis, Volume II*, Sections 8.3–8.4, total derivative, chain rule and mean-value bounds; Section 8.6, higher derivatives.
  https://www.jirka.org/ra/realanal2.pdf

**Relationship to the sources:** An implementation specialization of the covariant local Lagrangian calculation; no OT or selector input is used.
-/

/-!
# Coordinate covariance of the genuine Finsler Euler--Lagrange equation

The general C2 pullback theorem is applied to the actual transition of the manifold atlas.
Its derivative is invertible by the atlas, and its tangent lift preserves the original
energy. Local equality of energies transfers the actual partial differentials on the
overlap. Thus the original Finsler Euler--Lagrange equation is equivalent in the two
charts along any C2 curve with nonzero velocity staying in their overlap.

Overlap membership is the domain of this coordinate statement; no global chart,
curvature condition, or extra nondegeneracy of the geometry is imposed. This theorem
establishes covariance of the equation, not length minimization or global continuation.
-/

open Set Filter
open scoped Topology ContDiff Manifold

namespace OTSelector.Geometry
namespace ContinuousFinslerNorm.IsSmoothStronglyConvex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] {F : ContinuousFinslerNorm E M}

/-- The actual Finsler Euler--Lagrange equation is equivalent in two overlapping charts.
Invertibility of the coordinate derivative and equality of the energies are derived from
the atlas; they are not additional geometric hypotheses. -/
theorem chartEulerLagrange_iff_chartTransition (hF : F.IsSmoothStronglyConvex)
    (old new : M) {I : Set ℝ} (hI : IsOpen I) {y : ℝ → E}
    (hy : ContDiffOn ℝ 2 y I)
    (hphase : ∀ t ∈ I,
      (y t, deriv y t) ∈ chartTransitionDomain old new ×ˢ {w : E | w ≠ 0}) :
    (∀ t ∈ I, HasDerivAt (fun s ↦ fiberLegendre (F.chartEnergy new) (y s, deriv y s))
      (baseEnergyDifferential (F.chartEnergy new) (y t, deriv y t)) t) ↔
    (∀ t ∈ I,
      HasDerivAt
        (fun s ↦ fiberLegendre (F.chartEnergy old)
          ((chartTransition old new ∘ y) s, deriv (chartTransition old new ∘ y) s))
        (baseEnergyDifferential (F.chartEnergy old)
          ((chartTransition old new ∘ y) t, deriv (chartTransition old new ∘ y) t)) t) := by
  have he : EqOn (F.chartEnergy new)
      (pullbackEnergy (chartTransition old new) (F.chartEnergy old))
      (chartTransitionDomain old new ×ˢ (univ : Set E)) := by
    intro z hz
    exact F.chartEnergy_chartTransition old new hz.1 z.2
  have heq := eulerLagrange_congr_of_eqOn
    ((isOpen_chartTransitionDomain old new).prod isOpen_univ) hI he
    (fun t ht ↦ ⟨(hphase t ht).1, mem_univ _⟩)
  refine heq.trans (eulerLagrange_pullback_iff
    (isOpen_chartTransitionDomain old new) (ContinuousFinslerNorm.isOpen_chartEnergyDomain old)
    ((contDiffOn_chartTransition old new).of_le (by simp))
    ((hF.contDiffOn_chartEnergy old).of_le (by simp)) hI hy
    (fun t ht ↦ (hphase t ht).1) ?_ ?_)
  · intro t ht
    exact mapsTo_chartTransition_energyDomain old new (hphase t ht)
  · intro t ht
    exact fderiv_chartTransition_surjective old new (hphase t ht).1

end ContinuousFinslerNorm.IsSmoothStronglyConvex
end OTSelector.Geometry

end

/-! Source unit: `OTSelector.Geometry.Finsler.Geodesic.LocalExistence`. Its original mathematical documentation follows. -/
section

/-!
## Lemma skeleton

* **Conditions:** Smooth strongly convex Finsler energy at a nonzero chart phase.
* **Objects:** A smooth local Euler–Lagrange curve with prescribed position and velocity, first in coordinates and then on the manifold.
* **Proof detail:** Construct a local Hamiltonian integral curve, invert Legendre coordinates, and identify its velocity and Euler–Lagrange momentum equation.

## Mathematical sources

* Gerald Teschl, *Ordinary Differential Equations and Dynamical Systems (AMS 2012 author preliminary version)*, Section 2.2, Theorem 2.2 and Lemma 2.3, pp. 38–39; Section 2.3, Theorem 2.5, pp. 40–41.
  https://www.mat.univie.ac.at/~gerald/ftp/book-ode/ode.pdf#page=49
* Gerald Teschl, *Ordinary Differential Equations and Dynamical Systems (AMS 2012 author preliminary version)*, Section 8.3, pp. 238–240, equations (8.33)–(8.36) (action and Euler–Lagrange), (8.39)–(8.43) (Legendre transform and Hamilton equations), (8.47) (energy conservation).
  https://www.mat.univie.ac.at/~gerald/ftp/book-ode/ode.pdf#page=249
* Zhongmin Shen, *Landsberg Curvature, S-Curvature and Riemann Curvature, MSRI Publications 50 (2004)*, Section 4, pp. 313–314, length distance, Definition 4.1 and Lemma 4.2, equations (4–1)–(4–4).
  https://library.slmath.org/books/Book50/files/08Sh.pdf#page=11

**Relationship to the sources:** The source supplies the standard regular geodesic/EL ODE. The chart-domain and tangent-bundle data are explicit formal constructors rather than an assumed geodesic existence oracle.
-/

/-!
# Actual local Finsler Euler--Lagrange curves

The local Hamiltonian integral curve gives a position curve whose derivative is the
actual inverse Legendre velocity. Its momentum equation is therefore the Euler--Lagrange
equation for the original coordinate energy. Differentiating the actual Hamiltonian
proves conservation; degree-two homogeneity identifies it with the original Finsler
energy. The inverse tangent chart identifies coordinate velocity with the genuine
manifold tangent velocity, so the original Finsler speed is constant.

Every nonzero initial tangent vector has such a local smooth curve, constructed from
the given smooth strongly convex Finsler energy. These results neither assume an ODE
solution nor replace the norm by an inner product. Coordinate independence of the
Euler--Lagrange equation, minimizing length, variation with initial data and global
geodesic continuation remain separate results.
-/

open Set Filter Bundle Manifold
open scoped Topology ContDiff

noncomputable section
namespace OTSelector.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The position component of an actual Hamiltonian solution differentiates to inverse velocity. -/
theorem hasDerivAt_hamiltonian_position
    {L : E × E → ℝ} {e : OpenPartialHomeomorph (E × E) (E × (E →L[ℝ] ℝ))}
    {γ : ℝ → E × (E →L[ℝ] ℝ)} {t : ℝ}
    (hγ : HasDerivAt γ (localHamiltonianVectorField L e (γ t)) t) :
    HasDerivAt (fun s ↦ (γ s).1) (e.symm (γ t)).2 t := hγ.fst

/-- Along an actual solution the inverse Legendre point is the position and its true derivative. -/
theorem hamiltonian_inverse_eq_position_deriv
    {L : E × E → ℝ} {e : OpenPartialHomeomorph (E × E) (E × (E →L[ℝ] ℝ))}
    (he : (e : (E × E) → (E × (E →L[ℝ] ℝ))) = parametricLegendre L)
    {γ : ℝ → E × (E →L[ℝ] ℝ)} {t : ℝ} (ht : γ t ∈ e.target)
    (hγ : HasDerivAt γ (localHamiltonianVectorField L e (γ t)) t) :
    e.symm (γ t) = ((γ t).1, deriv (fun s ↦ (γ s).1) t) := by
  exact Prod.ext (parametricLegendre_inverse_components he ht).1
    (hasDerivAt_hamiltonian_position hγ).deriv.symm

/-- The actual Euler--Lagrange momentum equation follows from the constructed Hamiltonian field. -/
theorem hasDerivAt_eulerLagrange_of_hamiltonian
    {L : E × E → ℝ} {e : OpenPartialHomeomorph (E × E) (E × (E →L[ℝ] ℝ))}
    (he : (e : (E × E) → (E × (E →L[ℝ] ℝ))) = parametricLegendre L)
    {γ : ℝ → E × (E →L[ℝ] ℝ)} {I : Set ℝ} (hI : IsOpen I)
    (hmem : MapsTo γ I e.target)
    (hγ : ∀ t ∈ I, HasDerivAt γ (localHamiltonianVectorField L e (γ t)) t)
    {t : ℝ} (ht : t ∈ I) :
    HasDerivAt
      (fun s ↦ fiberLegendre L ((γ s).1, deriv (fun r ↦ (γ r).1) s))
      (baseEnergyDifferential L ((γ t).1, deriv (fun r ↦ (γ r).1) t)) t := by
  have h := (hγ t ht).snd
  change HasDerivAt (fun s ↦ (γ s).2) (baseEnergyDifferential L (e.symm (γ t))) t at h
  rw [hamiltonian_inverse_eq_position_deriv he (hmem ht) (hγ t ht)] at h
  apply h.congr_of_eventuallyEq
  filter_upwards [hI.mem_nhds ht] with s hs
  rw [← hamiltonian_inverse_eq_position_deriv he (hmem hs) (hγ s hs)]
  exact (parametricLegendre_inverse_components he (hmem hs)).2

/-- The actual Hamiltonian has zero time derivative along its constructed vector field. -/
theorem hasDerivAt_localHamiltonian_zero
    {L : E × E → ℝ} {e : OpenPartialHomeomorph (E × E) (E × (E →L[ℝ] ℝ))}
    (he : (e : (E × E) → (E × (E →L[ℝ] ℝ))) = parametricLegendre L)
    (hL : ContDiffOn ℝ ∞ L e.source) (hG : ContDiffOn ℝ ∞ e.symm e.target)
    {γ : ℝ → E × (E →L[ℝ] ℝ)} {t : ℝ} (ht : γ t ∈ e.target)
    (hγ : HasDerivAt γ (localHamiltonianVectorField L e (γ t)) t) :
    HasDerivAt (fun s ↦ localHamiltonian L e (γ s)) 0 t := by
  have hdL := (hL.contDiffAt (e.open_source.mem_nhds (e.map_target ht))).differentiableAt
    (by simp)
  have hdG := (hG.contDiffAt (e.open_target.mem_nhds ht)).differentiableAt
    (by simp)
  have hdH := ((contDiffOn_localHamiltonian hL hG).contDiffAt
    (e.open_target.mem_nhds ht)).differentiableAt (by simp)
  have h := hdH.hasFDerivAt.comp_hasDerivAt t hγ
  rw [localHamiltonianVectorField_energy_identity he ht hdL hdG] at h
  exact h

/-- Conservation holds throughout every connected open solution interval. -/
theorem localHamiltonian_eq_of_integralCurve
    {L : E × E → ℝ} {e : OpenPartialHomeomorph (E × E) (E × (E →L[ℝ] ℝ))}
    (he : (e : (E × E) → (E × (E →L[ℝ] ℝ))) = parametricLegendre L)
    (hL : ContDiffOn ℝ ∞ L e.source) (hG : ContDiffOn ℝ ∞ e.symm e.target)
    {γ : ℝ → E × (E →L[ℝ] ℝ)} {I : Set ℝ} (hI : IsOpen I)
    (hc : IsPreconnected I) (hmem : MapsTo γ I e.target)
    (hγ : ∀ t ∈ I, HasDerivAt γ (localHamiltonianVectorField L e (γ t)) t)
    {s t : ℝ} (hs : s ∈ I) (ht : t ∈ I) :
    localHamiltonian L e (γ s) = localHamiltonian L e (γ t) := by
  have hd u hu := hasDerivAt_localHamiltonian_zero he hL hG (hmem hu) (hγ u hu)
  exact hI.is_const_of_deriv_eq_zero hc
    (fun u hu ↦ (hd u hu).differentiableAt.differentiableWithinAt)
    (fun u hu ↦ (hd u hu).deriv) hs ht

variable {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

namespace ContinuousFinslerNorm

/-- Coordinate energy is the original energy of the genuine manifold curve velocity. -/
theorem energy_tangentMap_chart_curve (F : ContinuousFinslerNorm E M) (x₀ : M)
    {x : ℝ → E} {t : ℝ} {v : E}
    (ht : x t ∈ (extChartAt 𝓘(ℝ, E) x₀).target) (hd : HasDerivAt x v t) :
    F.energy (tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E)
      ((extChartAt 𝓘(ℝ, E) x₀).symm ∘ x) ⟨t, (1 : ℝ)⟩) =
      F.chartEnergy x₀ (x t, v) := by
  rw [tangentMap_chart_symm_curve x₀ ht hd]
  rfl

/-- Equal actual energies give equal original tangent lengths. -/
theorem toFun_eq_of_energy_eq (F : ContinuousFinslerNorm E M)
    {p q : TangentBundle 𝓘(ℝ, E) M} (h : F.energy p = F.energy q) :
    F.toFun p = F.toFun q := by
  apply NNReal.coe_injective
  apply (sq_eq_sq₀ (NNReal.coe_nonneg _) (NNReal.coe_nonneg _)).mp
  dsimp only [energy] at h
  linarith

end ContinuousFinslerNorm

namespace ContinuousFinslerNorm.IsSmoothStronglyConvex
variable {F : ContinuousFinslerNorm E M} (hF : F.IsSmoothStronglyConvex)
include hF

/-- Euler's identity holds for the actual fixed-chart Finsler energy. -/
theorem chartEnergy_euler (x₀ : M) {z : E × E}
    (hz : z ∈ ContinuousFinslerNorm.chartEnergyDomain x₀) :
    fiberLegendre (F.chartEnergy x₀) z z.2 = 2 * F.chartEnergy x₀ z := by
  have hdL : DifferentiableAt ℝ (F.chartEnergy x₀) z := ((hF.contDiffOn_chartEnergy x₀).contDiffAt
    ((ContinuousFinslerNorm.isOpen_chartEnergyDomain x₀).mem_nhds hz)).differentiableAt
      (by simp)
  have hd : DifferentiableAt ℝ (fun v ↦ F.chartEnergy x₀ (z.1, v)) z.2 := by
    simpa only [Function.comp_def] using!
      (hdL.hasFDerivAt.comp z.2 (hasFDerivAt_prodMk_right (𝕜 := ℝ) z.1 z.2)).differentiableAt
  exact twoHomogeneous_fderiv_euler (fun r _ ↦ F.chartEnergy_smul x₀ hz.1 r z.2) hd

/-- Degree-two homogeneity identifies the actual local Hamiltonian with the original energy. -/
theorem localHamiltonian_chartEnergy_eq (x₀ : M)
    {e : OpenPartialHomeomorph (E × E) (E × (E →L[ℝ] ℝ))}
    (he : (e : (E × E) → (E × (E →L[ℝ] ℝ))) = parametricLegendre (F.chartEnergy x₀))
    (hsource : e.source ⊆ ContinuousFinslerNorm.chartEnergyDomain x₀)
    {p : E × (E →L[ℝ] ℝ)} (hp : p ∈ e.target) :
    localHamiltonian (F.chartEnergy x₀) e p = F.chartEnergy x₀ (e.symm p) := by
  have hEuler := hF.chartEnergy_euler x₀ (hsource (e.map_target hp))
  rw [(parametricLegendre_inverse_components he hp).2] at hEuler
  dsimp only [localHamiltonian]
  linarith

/-- The actual Finsler chart energy is conserved along every connected local solution. -/
theorem chartEnergy_eq_of_integralCurve (x₀ : M)
    {e : OpenPartialHomeomorph (E × E) (E × (E →L[ℝ] ℝ))}
    (he : (e : (E × E) → (E × (E →L[ℝ] ℝ))) = parametricLegendre (F.chartEnergy x₀))
    (hsource : e.source ⊆ ContinuousFinslerNorm.chartEnergyDomain x₀)
    (hG : ContDiffOn ℝ ∞ e.symm e.target)
    {γ : ℝ → E × (E →L[ℝ] ℝ)} {I : Set ℝ} (hI : IsOpen I)
    (hc : IsPreconnected I) (hmem : MapsTo γ I e.target)
    (hγ : ∀ t ∈ I,
      HasDerivAt γ (localHamiltonianVectorField (F.chartEnergy x₀) e (γ t)) t)
    {s t : ℝ} (hs : s ∈ I) (ht : t ∈ I) :
    F.chartEnergy x₀ ((γ s).1, deriv (fun u ↦ (γ u).1) s) =
      F.chartEnergy x₀ ((γ t).1, deriv (fun u ↦ (γ u).1) t) := by
  rw [← hamiltonian_inverse_eq_position_deriv he (hmem hs) (hγ s hs),
    ← hamiltonian_inverse_eq_position_deriv he (hmem ht) (hγ t ht),
    ← hF.localHamiltonian_chartEnergy_eq x₀ he hsource (hmem hs),
    ← hF.localHamiltonian_chartEnergy_eq x₀ he hsource (hmem ht)]
  exact localHamiltonian_eq_of_integralCurve he ((hF.contDiffOn_chartEnergy x₀).mono hsource)
    hG hI hc hmem hγ hs ht

/-- Every nonzero Finsler coordinate velocity initiates a smooth local Euler--Lagrange
curve, with its actual initial velocity and conserved original energy. -/
theorem exists_chartEulerLagrange [FiniteDimensional ℝ E] (x₀ : M) {z : E × E}
    (hz : z ∈ ContinuousFinslerNorm.chartEnergyDomain x₀) (t₀ : ℝ) :
    ∃ ε > (0 : ℝ), ∃ x : ℝ → E,
      x t₀ = z.1 ∧ deriv x t₀ = z.2 ∧
      ContDiffOn ℝ ∞ x (Ioo (t₀ - ε) (t₀ + ε)) ∧
      (∀ t ∈ Ioo (t₀ - ε) (t₀ + ε),
        (x t, deriv x t) ∈ ContinuousFinslerNorm.chartEnergyDomain x₀) ∧
      (∀ t ∈ Ioo (t₀ - ε) (t₀ + ε),
        HasDerivAt (fun s ↦ fiberLegendre (F.chartEnergy x₀) (x s, deriv x s))
          (baseEnergyDifferential (F.chartEnergy x₀) (x t, deriv x t)) t) ∧
      ∀ t ∈ Ioo (t₀ - ε) (t₀ + ε),
        F.chartEnergy x₀ (x t, deriv x t) = F.chartEnergy x₀ z := by
  obtain ⟨e, he, hzsource, htarget, hsource, hG, _, _, _⟩ :=
    hF.exists_smooth_chartHamiltonian x₀ hz
  obtain ⟨ε, hε, γ, hγ₀, hmem, hγ, hsmooth, _⟩ :=
    exists_localHamiltonian_integralCurve ((hF.contDiffOn_chartEnergy x₀).mono hsource)
      hG htarget t₀
  have ht₀ : t₀ ∈ Ioo (t₀ - ε) (t₀ + ε) := ⟨by linarith, by linarith⟩
  have hstart : e.symm (γ t₀) = z := by
    rw [hγ₀, ← he]
    exact e.left_inv hzsource
  have hx₀ : (γ t₀).1 = z.1 := by rw [hγ₀]; rfl
  have hv₀ : deriv (fun t ↦ (γ t).1) t₀ = z.2 := by
    rw [(hasDerivAt_hamiltonian_position (hγ t₀ ht₀)).deriv, hstart]
  refine ⟨ε, hε, fun t ↦ (γ t).1, hx₀, hv₀, hsmooth.fst, ?_, ?_, ?_⟩
  · intro t ht
    rw [← hamiltonian_inverse_eq_position_deriv he (hmem ht) (hγ t ht)]
    exact hsource (e.map_target (hmem ht))
  · exact fun t ht ↦ hasDerivAt_eulerLagrange_of_hamiltonian he isOpen_Ioo hmem hγ ht
  · intro t ht
    have h := hF.chartEnergy_eq_of_integralCurve x₀ he hsource hG
      isOpen_Ioo (convex_Ioo (t₀ - ε) (t₀ + ε)).isPreconnected hmem hγ ht ht₀
    simpa only [hx₀, hv₀] using h

/-- The local Euler--Lagrange solution represents a genuine smooth manifold curve whose
original Finsler tangent speed is constant, with the prescribed coordinate initial data. -/
theorem exists_localEulerLagrange_constantSpeed [FiniteDimensional ℝ E] (x₀ : M)
    {z : E × E} (hz : z ∈ ContinuousFinslerNorm.chartEnergyDomain x₀) (t₀ : ℝ) :
    ∃ ε > (0 : ℝ), ∃ x : ℝ → E,
      x t₀ = z.1 ∧ deriv x t₀ = z.2 ∧
      ContDiffOn ℝ ∞ x (Ioo (t₀ - ε) (t₀ + ε)) ∧
      ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞
        ((extChartAt 𝓘(ℝ, E) x₀).symm ∘ x) (Ioo (t₀ - ε) (t₀ + ε)) ∧
      (∀ t ∈ Ioo (t₀ - ε) (t₀ + ε),
        (x t, deriv x t) ∈ ContinuousFinslerNorm.chartEnergyDomain x₀) ∧
      (∀ t ∈ Ioo (t₀ - ε) (t₀ + ε),
        HasDerivAt (fun s ↦ fiberLegendre (F.chartEnergy x₀) (x s, deriv x s))
          (baseEnergyDifferential (F.chartEnergy x₀) (x t, deriv x t)) t) ∧
      ∀ t ∈ Ioo (t₀ - ε) (t₀ + ε),
        F.toFun (tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E)
          ((extChartAt 𝓘(ℝ, E) x₀).symm ∘ x) ⟨t, (1 : ℝ)⟩) =
        F.toFun ((extChartAt (𝓘(ℝ, E).prod 𝓘(ℝ, E))
          (⟨x₀, 0⟩ : TangentBundle 𝓘(ℝ, E) M)).symm z) := by
  obtain ⟨ε, hε, x, hx₀, hv₀, hsmooth, hmem, hEL, henergy⟩ :=
    hF.exists_chartEulerLagrange x₀ hz t₀
  have hpath : ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞
      ((extChartAt 𝓘(ℝ, E) x₀).symm ∘ x) (Ioo (t₀ - ε) (t₀ + ε)) :=
    (contMDiffOn_extChartAt_symm x₀).comp hsmooth.contMDiffOn (fun t ht ↦ (hmem t ht).1)
  refine ⟨ε, hε, x, hx₀, hv₀, hsmooth, hpath, hmem, hEL, ?_⟩
  intro t ht
  have hd := (hsmooth.contDiffAt (isOpen_Ioo.mem_nhds ht)).differentiableAt (by simp)
  apply F.toFun_eq_of_energy_eq
  rw [F.energy_tangentMap_chart_curve x₀ (hmem t ht).1 hd.hasDerivAt]
  exact henergy t ht

/-- A prescribed nonzero initial tangent vector admits a genuine local smooth manifold
curve with constant original Finsler speed, satisfying the actual local Euler--Lagrange equation. -/
theorem exists_localEulerLagrange [FiniteDimensional ℝ E] (x₀ : M) {v : E}
    (hv : v ≠ 0) (t₀ : ℝ) :
    ∃ ε > (0 : ℝ), ∃ c : ℝ → M,
      c t₀ = x₀ ∧
      tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) c ⟨t₀, (1 : ℝ)⟩ =
        (⟨x₀, tangentFiberModelEquiv x₀ v⟩ : TangentBundle 𝓘(ℝ, E) M) ∧
      ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞ c (Ioo (t₀ - ε) (t₀ + ε)) ∧
      (∀ t ∈ Ioo (t₀ - ε) (t₀ + ε),
        F.toFun (tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) c ⟨t, (1 : ℝ)⟩) =
          F.toFun ⟨x₀, tangentFiberModelEquiv x₀ v⟩) ∧
      ∃ x : ℝ → E, c = (extChartAt 𝓘(ℝ, E) x₀).symm ∘ x ∧
        ContDiffOn ℝ ∞ x (Ioo (t₀ - ε) (t₀ + ε)) ∧
        ∀ t ∈ Ioo (t₀ - ε) (t₀ + ε),
          (x t, deriv x t) ∈ ContinuousFinslerNorm.chartEnergyDomain x₀ ∧
          HasDerivAt (fun s ↦ fiberLegendre (F.chartEnergy x₀) (x s, deriv x s))
            (baseEnergyDifferential (F.chartEnergy x₀) (x t, deriv x t)) t := by
  obtain ⟨ε, hε, x, hx₀, hv₀, hsmooth, hpath, hmem, hEL, hspeed⟩ :=
    hF.exists_localEulerLagrange_constantSpeed x₀
      (z := (extChartAt 𝓘(ℝ, E) x₀ x₀, v)) ⟨mem_extChartAt_target x₀, hv⟩ t₀
  have ht₀ : t₀ ∈ Ioo (t₀ - ε) (t₀ + ε) := ⟨by linarith, by linarith⟩
  have hd := (hsmooth.contDiffAt (isOpen_Ioo.mem_nhds ht₀)).differentiableAt (by simp)
  refine ⟨ε, hε, (extChartAt 𝓘(ℝ, E) x₀).symm ∘ x, ?_, ?_, hpath, ?_,
    x, rfl, hsmooth, fun t ht ↦ ⟨hmem t ht, hEL t ht⟩⟩
  · change (extChartAt 𝓘(ℝ, E) x₀).symm (x t₀) = x₀
    rw [hx₀]
    exact (extChartAt 𝓘(ℝ, E) x₀).left_inv (mem_extChartAt_source x₀)
  · rw [tangentMap_chart_symm_curve x₀ (hmem t₀ ht₀).1 hd.hasDerivAt,
      hx₀, hv₀, tangentChart_symm_self]
    rfl
  · intro t ht
    change _ = F.toFun ⟨x₀, v⟩
    simpa only [tangentChart_symm_self] using hspeed t ht

end ContinuousFinslerNorm.IsSmoothStronglyConvex

end OTSelector.Geometry

end
end

/-! Source unit: `OTSelector.Geometry.Finsler.Hamiltonian.EulerLagrangeUniqueness`. Its original mathematical documentation follows. -/
section

/-!
## Lemma skeleton

* **Conditions:** A smooth energy with positive-definite fiber Hessian on an open finite-dimensional phase domain; two smooth EL curves have the same initial position and velocity.
* **Objects:** The phase lift into position/covector space and uniqueness of its germ.
* **Proof detail:** Construct the local Legendre inverse, lift both curves to one Hamiltonian vector field, and apply local ODE uniqueness.

## Mathematical sources

* Gerald Teschl, *Ordinary Differential Equations and Dynamical Systems (AMS 2012 author preliminary version)*, Section 2.2, Theorem 2.2 and Lemma 2.3, pp. 38–39; Section 2.3, Theorem 2.5, pp. 40–41.
  https://www.mat.univie.ac.at/~gerald/ftp/book-ode/ode.pdf#page=49
* Gerald Teschl, *Ordinary Differential Equations and Dynamical Systems (AMS 2012 author preliminary version)*, Section 8.3, pp. 238–240, equations (8.33)–(8.36) (action and Euler–Lagrange), (8.39)–(8.43) (Legendre transform and Hamilton equations), (8.47) (energy conservation).
  https://www.mat.univie.ac.at/~gerald/ftp/book-ode/ode.pdf#page=249

**Relationship to the sources:** A derived local regular-Lagrangian theorem; strong convexity supplies the invertible fiber Hessian. The statement constructs its inverse rather than assuming a preexisting Hamiltonian flow.
-/

/-!
# Germ uniqueness for actual Euler--Lagrange position curves

The phase lift of a position curve is `(x(t), D_v L(x(t), x'(t)))`, with the true derivative
of the given scalar coordinate energy. Its genuine Euler--Lagrange momentum equation,
together with differentiability of position, implies the Hamiltonian ODE for the locally
constructed Legendre Hamiltonian field. This compatibility is proved rather than assumed.

Smoothness of position makes position and velocity continuous. Thus two curves with the
same initial position and velocity enter one common Legendre chart on a time neighborhood.
The proved local uniqueness of integral-curve germs gives equality of their phase lifts,
and therefore equality of their positions near the initial time. The time neighborhoods of
the two competitors may differ. Only the common initial state is required in the original
open energy domain; staying in a smaller chart is derived from continuity.

The final result applies to the actual chart energy of a smooth strongly convex Finsler
structure. It is a fixed-coordinate germ uniqueness theorem; coordinate invariance and
minimizing length remain separate geometric results.
-/

open Set Filter Manifold
open scoped Topology ContDiff

namespace OTSelector.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The actual position-momentum lift of a position curve, using its true derivative. -/
noncomputable def eulerLagrangePhaseLift (L : E × E → ℝ) (x : ℝ → E)
    (t : ℝ) : E × (E →L[ℝ] ℝ) :=
  (x t, fiberLegendre L (x t, deriv x t))

/-- The true Euler--Lagrange equation implies the Hamiltonian ODE for the actual phase lift. -/
theorem hasDerivAt_eulerLagrangePhaseLift
    {L : E × E → ℝ} {e : OpenPartialHomeomorph (E × E) (E × (E →L[ℝ] ℝ))}
    (he : (e : (E × E) → (E × (E →L[ℝ] ℝ))) = parametricLegendre L)
    {x : ℝ → E} {t : ℝ} (hx : DifferentiableAt ℝ x t)
    (hsource : (x t, deriv x t) ∈ e.source)
    (hEL : HasDerivAt (fun s ↦ fiberLegendre L (x s, deriv x s))
      (baseEnergyDifferential L (x t, deriv x t)) t) :
    HasDerivAt (eulerLagrangePhaseLift L x)
      (localHamiltonianVectorField L e (eulerLagrangePhaseLift L x t)) t := by
  have hinv : e.symm (eulerLagrangePhaseLift L x t) = (x t, deriv x t) := by
    change e.symm (parametricLegendre L (x t, deriv x t)) = _
    rw [← he]
    exact e.left_inv hsource
  change HasDerivAt (eulerLagrangePhaseLift L x)
    ((e.symm (eulerLagrangePhaseLift L x t)).2,
      baseEnergyDifferential L (e.symm (eulerLagrangePhaseLift L x t))) t
  rw [hinv]
  exact hx.hasDerivAt.prodMk hEL

/-- Smooth position curves remain in the chosen Legendre source near their initial state,
so their true Euler--Lagrange equation supplies the Hamiltonian ODE on a time neighborhood. -/
theorem eventually_hasDerivAt_eulerLagrangePhaseLift
    {L : E × E → ℝ} {e : OpenPartialHomeomorph (E × E) (E × (E →L[ℝ] ℝ))}
    (he : (e : (E × E) → (E × (E →L[ℝ] ℝ))) = parametricLegendre L)
    {x : ℝ → E} {I : Set ℝ} {t₀ : ℝ} (hI : IsOpen I) (ht₀ : t₀ ∈ I)
    (hx : ContDiffOn ℝ ∞ x I) (hsource : (x t₀, deriv x t₀) ∈ e.source)
    (hEL : ∀ t ∈ I, HasDerivAt (fun s ↦ fiberLegendre L (x s, deriv x s))
      (baseEnergyDifferential L (x t, deriv x t)) t) :
    ∀ᶠ t in 𝓝 t₀, HasDerivAt (eulerLagrangePhaseLift L x)
      (localHamiltonianVectorField L e (eulerLagrangePhaseLift L x t)) t := by
  have hxc := (hx.contDiffAt (hI.mem_nhds ht₀)).continuousAt
  have hvc := ((hx.deriv_of_isOpen hI (m := ∞) (by simp)).contDiffAt
    (hI.mem_nhds ht₀)).continuousAt
  have hstay : ∀ᶠ t in 𝓝 t₀, (x t, deriv x t) ∈ e.source :=
    (hxc.prodMk hvc).preimage_mem_nhds (e.open_source.mem_nhds hsource)
  filter_upwards [hstay, hI.mem_nhds ht₀] with t hst ht
  exact hasDerivAt_eulerLagrangePhaseLift he
    ((hx.contDiffAt (hI.mem_nhds ht)).differentiableAt (by simp)) hst (hEL t ht)

/-- Two actual smooth Euler--Lagrange position curves with the same initial position and
velocity have the same germ. Only the common initial state need be specified in the energy
domain: continuity places both state curves in one constructed Legendre chart locally. -/
theorem eulerLagrange_eventuallyEq_of_same_initial_data [FiniteDimensional ℝ E]
    {L : E × E → ℝ} {U : Set (E × E)} (hU : IsOpen U)
    (hL : ContDiffOn ℝ ∞ L U)
    (hpos : ∀ z ∈ U, ∀ w : E, w ≠ 0 →
      0 < fderiv ℝ (fderiv ℝ (fun v ↦ L (z.1, v))) z.2 w w)
    {x y : ℝ → E} {I J : Set ℝ} {t₀ : ℝ}
    (hI : IsOpen I) (hJ : IsOpen J) (htI : t₀ ∈ I) (htJ : t₀ ∈ J)
    (hx : ContDiffOn ℝ ∞ x I) (hy : ContDiffOn ℝ ∞ y J)
    (hELx : ∀ t ∈ I, HasDerivAt (fun s ↦ fiberLegendre L (x s, deriv x s))
      (baseEnergyDifferential L (x t, deriv x t)) t)
    (hELy : ∀ t ∈ J, HasDerivAt (fun s ↦ fiberLegendre L (y s, deriv y s))
      (baseEnergyDifferential L (y t, deriv y t)) t)
    (hx₀ : (x t₀, deriv x t₀) ∈ U)
    (hposition : x t₀ = y t₀) (hvelocity : deriv x t₀ = deriv y t₀) :
    x =ᶠ[𝓝 t₀] y := by
  obtain ⟨e, he, hsource, htarget, hsub, hG, _, hX, _⟩ :=
    exists_smooth_localHamiltonian hU hL hpos hx₀
  have hsourceY : (y t₀, deriv y t₀) ∈ e.source := by
    simpa only [← hposition, ← hvelocity] using hsource
  have hODEX := eventually_hasDerivAt_eulerLagrangePhaseLift he hI htI hx hsource hELx
  have hODEY := eventually_hasDerivAt_eulerLagrangePhaseLift he hJ htJ hy hsourceY hELy
  have hinitial : eulerLagrangePhaseLift L y t₀ = eulerLagrangePhaseLift L x t₀ := by
    simp only [eulerLagrangePhaseLift, hposition, hvelocity]
  have hfield : ContDiffAt ℝ 1 (localHamiltonianVectorField L e)
      (eulerLagrangePhaseLift L x t₀) :=
    (hX.contDiffAt (e.open_target.mem_nhds htarget)).of_le (by simp)
  have hphase := integralCurve_eventuallyEq_of_contDiffAt hfield rfl hinitial hODEX hODEY
  filter_upwards [hphase] with t ht
  exact congrArg Prod.fst ht

namespace ContinuousFinslerNorm.IsSmoothStronglyConvex

variable {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [FiniteDimensional ℝ E]
  {F : ContinuousFinslerNorm E M}

/-- In a fixed genuine Finsler tangent chart, the true Euler--Lagrange position curve
has a unique germ for each nonzero initial position-velocity state. -/
theorem chartEulerLagrange_eventuallyEq_of_same_initial_data (hF : F.IsSmoothStronglyConvex)
    (x₀ : M) {x y : ℝ → E} {I J : Set ℝ} {t₀ : ℝ}
    (hI : IsOpen I) (hJ : IsOpen J) (htI : t₀ ∈ I) (htJ : t₀ ∈ J)
    (hx : ContDiffOn ℝ ∞ x I) (hy : ContDiffOn ℝ ∞ y J)
    (hELx : ∀ t ∈ I,
      HasDerivAt (fun s ↦ fiberLegendre (F.chartEnergy x₀) (x s, deriv x s))
        (baseEnergyDifferential (F.chartEnergy x₀) (x t, deriv x t)) t)
    (hELy : ∀ t ∈ J,
      HasDerivAt (fun s ↦ fiberLegendre (F.chartEnergy x₀) (y s, deriv y s))
        (baseEnergyDifferential (F.chartEnergy x₀) (y t, deriv y t)) t)
    (hx₀ : (x t₀, deriv x t₀) ∈ chartEnergyDomain x₀)
    (hposition : x t₀ = y t₀) (hvelocity : deriv x t₀ = deriv y t₀) :
    x =ᶠ[𝓝 t₀] y := by
  exact eulerLagrange_eventuallyEq_of_same_initial_data (isOpen_chartEnergyDomain x₀)
    (hF.contDiffOn_chartEnergy x₀)
    (fun _ hz _ hw ↦ hF.chartEnergy_hessian_pos x₀ hz hw)
    hI hJ htI htJ hx hy hELx hELy hx₀ hposition hvelocity

end ContinuousFinslerNorm.IsSmoothStronglyConvex

end OTSelector.Geometry

end

/-! Source unit: `OTSelector.Geometry.Finsler.Geodesic.Regularity`. Its original mathematical documentation follows. -/
section

/-!
## Lemma skeleton

* **Conditions:** A C2 coordinate EL solution in the slit domain of a smooth strongly convex Finsler energy.
* **Objects:** Smoothness of the same curve.
* **Proof detail:** Lift to the smooth Hamiltonian ODE, bootstrap integral-curve regularity, and project back through the smooth inverse.

## Mathematical sources

* Gerald Teschl, *Ordinary Differential Equations and Dynamical Systems (AMS 2012 author preliminary version)*, Section 2.2, Theorem 2.2 and Lemma 2.3, pp. 38–39; Section 2.3, Theorem 2.5, pp. 40–41.
  https://www.mat.univie.ac.at/~gerald/ftp/book-ode/ode.pdf#page=49
* Gerald Teschl, *Ordinary Differential Equations and Dynamical Systems (AMS 2012 author preliminary version)*, Section 8.3, pp. 238–240, equations (8.33)–(8.36) (action and Euler–Lagrange), (8.39)–(8.43) (Legendre transform and Hamilton equations), (8.47) (energy conservation).
  https://www.mat.univie.ac.at/~gerald/ftp/book-ode/ode.pdf#page=249

**Relationship to the sources:** This is smooth ODE regularity applied to a regular Lagrangian; the hypothesis is C2, not already a smooth solution.
-/

/-!
# Smoothness of actual Finsler Euler--Lagrange curves

A C2 coordinate position curve with nonzero admissible velocity and the true
Euler--Lagrange momentum equation is automatically smooth on its open time domain.
Continuity of position and velocity puts each local piece into a genuine Legendre
chart constructed from the original Finsler structure. Its actual phase lift then
solves the smooth Hamiltonian equation, whose time regularity bootstraps to all orders.
Projection and locality recover smoothness of the given position curve.
-/

open Set Filter Manifold
open scoped Topology ContDiff

namespace OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [FiniteDimensional ℝ E]
  {F : ContinuousFinslerNorm E M}

/-- A C2 actual Euler--Lagrange curve for the original smooth strongly convex Finsler
energy is smooth wherever its position and nonzero velocity lie in the tangent chart. -/
theorem contDiffOn_chartEulerLagrange_of_contDiffOn_two (hF : F.IsSmoothStronglyConvex)
    (x₀ : M) {x : ℝ → E} {I : Set ℝ} (hI : IsOpen I) (hx : ContDiffOn ℝ 2 x I)
    (hphase : ∀ t ∈ I, (x t, deriv x t) ∈ chartEnergyDomain x₀)
    (hEL : ∀ t ∈ I,
      HasDerivAt (fun s ↦ fiberLegendre (F.chartEnergy x₀) (x s, deriv x s))
        (baseEnergyDifferential (F.chartEnergy x₀) (x t, deriv x t)) t) :
    ContDiffOn ℝ ∞ x I := by
  intro t ht
  obtain ⟨e, he, hs, _, _, _, _, hX, _⟩ :=
    hF.exists_smooth_chartHamiltonian x₀ (hphase t ht)
  have hxc : ContinuousAt x t := (hx.contDiffAt (hI.mem_nhds ht)).continuousAt
  have hvc : ContinuousAt (deriv x) t :=
    (hx.continuousOn_deriv_of_isOpen hI (by norm_num)).continuousAt (hI.mem_nhds ht)
  have hstay : ∀ᶠ u in 𝓝 t, (x u, deriv x u) ∈ e.source :=
    (hxc.prodMk hvc).preimage_mem_nhds (e.open_source.mem_nhds hs)
  have hneighborhood : I ∩ {u | (x u, deriv x u) ∈ e.source} ∈ 𝓝 t :=
    inter_mem (hI.mem_nhds ht) hstay
  obtain ⟨J, hJsub, hJ, htJ⟩ := mem_nhds_iff.mp hneighborhood
  have hlift : ContDiffOn ℝ ∞ (eulerLagrangePhaseLift (F.chartEnergy x₀) x) J := by
    apply contDiffOn_integralCurve_of_isOpen hX hJ
    · intro u hu
      change parametricLegendre (F.chartEnergy x₀) (x u, deriv x u) ∈ e.target
      rw [← he]
      exact e.map_source (hJsub hu).2
    · intro u hu
      exact hasDerivAt_eulerLagrangePhaseLift he
        ((hx.contDiffAt (hI.mem_nhds (hJsub hu).1)).differentiableAt (by norm_num))
        (hJsub hu).2 (hEL u (hJsub hu).1)
  exact (hlift.fst.contDiffAt (hJ.mem_nhds htJ)).contDiffWithinAt

end OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

end

/-! Source unit: `OTSelector.Geometry.Finsler.Geodesic.LocalUniqueness`. Its original mathematical documentation follows. -/
section

/-!
## Lemma skeleton

* **Conditions:** Two local chart EL curves with the same actual manifold tangent initial data, in possibly different charts.
* **Objects:** Coordinate and manifold equality on a neighborhood of the initial time.
* **Proof detail:** Choose a common overlap, rechart one solution, identify initial chart velocity and use Hamiltonian local uniqueness.

## Mathematical sources

* Gerald Teschl, *Ordinary Differential Equations and Dynamical Systems (AMS 2012 author preliminary version)*, Section 2.2, Theorem 2.2 and Lemma 2.3, pp. 38–39; Section 2.3, Theorem 2.5, pp. 40–41.
  https://www.mat.univie.ac.at/~gerald/ftp/book-ode/ode.pdf#page=49
* Gerald Teschl, *Ordinary Differential Equations and Dynamical Systems (AMS 2012 author preliminary version)*, Section 8.3, pp. 238–240, equations (8.33)–(8.36) (action and Euler–Lagrange), (8.39)–(8.43) (Legendre transform and Hamilton equations), (8.47) (energy conservation).
  https://www.mat.univie.ac.at/~gerald/ftp/book-ode/ode.pdf#page=249
* John M. Lee, *Introduction to Smooth Manifolds, second edition (2013)*, Chapter 3, sections “The Differential of a Smooth Map” pp. 55–59, “Computations in Coordinates” pp. 60–64, “The Tangent Bundle” pp. 65–67, “Velocity Vectors of Curves” pp. 68–70.
  https://sites.math.washington.edu/~lee/Books/ISM/front-matter.pdf#page=10

**Relationship to the sources:** The cross-chart germ formulation is a derived manifold adapter to the standard ODE uniqueness theorem.
-/

/-!
# Germ uniqueness for genuine manifold Euler--Lagrange curves

The two smooth manifold curves may be expressed in different atlas charts and on different
open time domains. Their common initial point lies in both charts. Continuity constructs
an open time neighborhood where the second curve also lies in the first chart; the proved
Finsler coordinate covariance then transfers its actual Euler--Lagrange equation there.

Equality of total tangent velocities is carried through the tangent map of that common
chart. The chain rule identifies the resulting vectors with the ordinary coordinate
velocities. Fixed-coordinate Euler--Lagrange uniqueness therefore gives equal coordinate
germs, and chart injectivity gives equal manifold germs.

The geometric assumptions are a finite-dimensional real model, a smooth boundaryless atlas,
and the given smooth strongly convex Finsler norm. The curve assumptions use the actual
coordinate energy and actual derivatives, with nonzero coordinate velocities. No common
chart, smaller time domain, inverse Legendre map, or flow is assumed for the competitors.
This is local uniqueness; global continuation and length minimization are separate results.
-/

open Set Filter Manifold
open scoped Topology ContDiff

namespace OTSelector.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]

set_option backward.isDefEq.respectTransparency false in
/-- Equal manifold velocities have equal ordinary velocities in a common chart. -/
theorem deriv_extChartAt_comp_eq_of_tangentMap_eq
    {c d : ℝ → M} {t₀ : ℝ} (a : M)
    (hc : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) c t₀)
    (hd : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) d t₀)
    (hca : c t₀ ∈ (extChartAt 𝓘(ℝ, E) a).source)
    (hda : d t₀ ∈ (extChartAt 𝓘(ℝ, E) a).source)
    (hv : tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) c ⟨t₀, (1 : ℝ)⟩ =
      tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) d ⟨t₀, (1 : ℝ)⟩) :
    deriv ((extChartAt 𝓘(ℝ, E) a) ∘ c) t₀ =
      deriv ((extChartAt 𝓘(ℝ, E) a) ∘ d) t₀ := by
  have hχc : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, E)
      (extChartAt 𝓘(ℝ, E) a) (c t₀) :=
    mdifferentiableAt_extChartAt (by simpa only [extChartAt_source] using hca)
  have hχd : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, E)
      (extChartAt 𝓘(ℝ, E) a) (d t₀) :=
    mdifferentiableAt_extChartAt (by simpa only [extChartAt_source] using hda)
  have ht := congrArg (tangentMap 𝓘(ℝ, E) 𝓘(ℝ, E) (extChartAt 𝓘(ℝ, E) a)) hv
  rw [← tangentMap_comp_at ⟨t₀, (1 : ℝ)⟩ hχc hc,
    ← tangentMap_comp_at ⟨t₀, (1 : ℝ)⟩ hχd hd] at ht
  have hs := congrArg (fun v : TangentBundle 𝓘(ℝ, E) E ↦ v.2) ht
  simp only [tangentMap, mfderiv_eq_fderiv] at hs
  exact (fderiv_apply_one_eq_deriv (𝕜 := ℝ)).symm.trans
    (hs.trans (fderiv_apply_one_eq_deriv (𝕜 := ℝ)))

/-- Smooth manifold curves have smooth coordinates in every chart containing their image. -/
theorem contDiffOn_chart_curve (a : M) {c : ℝ → M} {I : Set ℝ}
    (hc : ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞ c I)
    (hmap : MapsTo c I (extChartAt 𝓘(ℝ, E) a).source) :
    ContDiffOn ℝ ∞ (extChartAt 𝓘(ℝ, E) a ∘ c) I := by
  apply ContMDiffOn.contDiffOn
  exact contMDiffOn_extChartAt.comp hc (fun t ht ↦ by
    change c t ∈ (chartAt E a).source
    simpa only [extChartAt_source] using hmap ht)

namespace ContinuousFinslerNorm.IsSmoothStronglyConvex

variable [FiniteDimensional ℝ E] {F : ContinuousFinslerNorm E M}

/-- Smooth Finsler Euler--Lagrange curves expressed in possibly different charts
have the same manifold germ when their initial point and actual tangent velocity agree. -/
theorem manifoldEulerLagrange_eventuallyEq_of_same_initial_data
    (hF : F.IsSmoothStronglyConvex) (a b : M)
    {c d : ℝ → M} {I J : Set ℝ} {t₀ : ℝ}
    (hI : IsOpen I) (hJ : IsOpen J) (htI : t₀ ∈ I) (htJ : t₀ ∈ J)
    (hc : ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞ c I)
    (hd : ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞ d J)
    (hcmap : MapsTo c I (extChartAt 𝓘(ℝ, E) a).source)
    (hdmap : MapsTo d J (extChartAt 𝓘(ℝ, E) b).source)
    (hcvel : ∀ t ∈ I, deriv (extChartAt 𝓘(ℝ, E) a ∘ c) t ≠ 0)
    (hdvel : ∀ t ∈ J, deriv (extChartAt 𝓘(ℝ, E) b ∘ d) t ≠ 0)
    (hELc : ∀ t ∈ I, HasDerivAt
      (fun s ↦ fiberLegendre (F.chartEnergy a)
        ((extChartAt 𝓘(ℝ, E) a ∘ c) s, deriv (extChartAt 𝓘(ℝ, E) a ∘ c) s))
      (baseEnergyDifferential (F.chartEnergy a)
        ((extChartAt 𝓘(ℝ, E) a ∘ c) t, deriv (extChartAt 𝓘(ℝ, E) a ∘ c) t)) t)
    (hELd : ∀ t ∈ J, HasDerivAt
      (fun s ↦ fiberLegendre (F.chartEnergy b)
        ((extChartAt 𝓘(ℝ, E) b ∘ d) s, deriv (extChartAt 𝓘(ℝ, E) b ∘ d) s))
      (baseEnergyDifferential (F.chartEnergy b)
        ((extChartAt 𝓘(ℝ, E) b ∘ d) t, deriv (extChartAt 𝓘(ℝ, E) b ∘ d) t)) t)
    (hposition : c t₀ = d t₀)
    (htangent : tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) c ⟨t₀, (1 : ℝ)⟩ =
      tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) d ⟨t₀, (1 : ℝ)⟩) :
    c =ᶠ[𝓝 t₀] d := by
  let K := J ∩ d ⁻¹' (extChartAt 𝓘(ℝ, E) a).source
  have hK : IsOpen K := hd.continuousOn.isOpen_inter_preimage hJ
    (isOpen_extChartAt_source a)
  have htK : t₀ ∈ K := ⟨htJ, by
    change d t₀ ∈ (extChartAt 𝓘(ℝ, E) a).source
    rw [← hposition]
    exact hcmap htI⟩
  have hvelocity := deriv_extChartAt_comp_eq_of_tangentMap_eq a
    ((hc.contMDiffAt (hI.mem_nhds htI)).mdifferentiableAt (by simp))
    ((hd.contMDiffAt (hJ.mem_nhds htJ)).mdifferentiableAt (by simp))
    (hcmap htI) htK.2 htangent
  let x := extChartAt 𝓘(ℝ, E) a ∘ c
  let y := extChartAt 𝓘(ℝ, E) b ∘ d
  let z := chartTransition a b ∘ y
  have hx : ContDiffOn ℝ ∞ x I := contDiffOn_chart_curve a hc hcmap
  have hy : ContDiffOn ℝ ∞ y J := contDiffOn_chart_curve b hd hdmap
  have hymap : MapsTo y K (chartTransitionDomain a b) := by
    intro t ht
    refine ⟨(extChartAt 𝓘(ℝ, E) b).map_source (hdmap ht.1), ?_⟩
    change (extChartAt 𝓘(ℝ, E) b).symm (extChartAt 𝓘(ℝ, E) b (d t)) ∈
      (extChartAt 𝓘(ℝ, E) a).source
    rw [(extChartAt 𝓘(ℝ, E) b).left_inv (hdmap ht.1)]
    exact ht.2
  have hz : ContDiffOn ℝ ∞ z K :=
    (contDiffOn_chartTransition a b).comp (hy.mono inter_subset_left) hymap
  have hzeq : EqOn z (extChartAt 𝓘(ℝ, E) a ∘ d) K := by
    intro t ht
    change extChartAt 𝓘(ℝ, E) a
      ((extChartAt 𝓘(ℝ, E) b).symm (extChartAt 𝓘(ℝ, E) b (d t))) = _
    rw [(extChartAt 𝓘(ℝ, E) b).left_inv (hdmap ht.1)]
    rfl
  have hzevent : z =ᶠ[𝓝 t₀] (extChartAt 𝓘(ℝ, E) a ∘ d) :=
    Filter.eventually_of_mem (hK.mem_nhds htK) (fun _ ht ↦ hzeq ht)
  have hELz := (hF.chartEulerLagrange_iff_chartTransition a b hK
    ((hy.mono inter_subset_left).of_le (by simp))
    (fun t ht ↦ ⟨hymap ht, hdvel t ht.1⟩)).mp (fun t ht ↦ hELd t ht.1)
  have hcoord := hF.chartEulerLagrange_eventuallyEq_of_same_initial_data a
    hI hK htI htK hx hz hELc hELz
    ⟨(extChartAt 𝓘(ℝ, E) a).map_source (hcmap htI), hcvel t₀ htI⟩
    (by
      change extChartAt 𝓘(ℝ, E) a (c t₀) = z t₀
      rw [hzeq htK]
      exact congrArg (extChartAt 𝓘(ℝ, E) a) hposition)
    (hvelocity.trans hzevent.deriv_eq.symm)
  filter_upwards [hcoord, hI.mem_nhds htI, hK.mem_nhds htK] with t hct htI htK
  apply (extChartAt 𝓘(ℝ, E) a).injOn (hcmap htI) htK.2
  exact hct.trans (hzeq htK)

end ContinuousFinslerNorm.IsSmoothStronglyConvex
end OTSelector.Geometry

end
