import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import OTSelector.Analysis.Convex.Legendre.Parametric
import OTSelector.Geometry.Finsler.Hamiltonian.Basic

/-!
## Lemma skeleton

* **Conditions:** A C2 coordinate map, a C2 energy on the relevant open phase domain and a C2 curve; derivative surjectivity for the converse.
* **Objects:** Pullback Lagrangian, transformed momentum and base differential.
* **Proof detail:** Use the chain/product rules; mixed Hessian symmetry cancels the coordinate-acceleration terms in the Euler–Lagrange residual.

## Mathematical sources

* Gerald Teschl, *Ordinary Differential Equations and Dynamical Systems (AMS 2012 author preliminary version)*, Section 8.3, pp. 238–240, equations (8.33)–(8.36) (action and Euler–Lagrange), (8.39)–(8.43) (Legendre transform and Hamilton equations), (8.47) (energy conservation).
  https://www.mat.univie.ac.at/~gerald/ftp/book-ode/ode.pdf#page=249
* Jiří Lebl, *Basic Analysis II: Introduction to Real Analysis, Volume II*, Sections 8.3–8.4, total derivative, chain rule and mean-value bounds; Section 8.6, higher derivatives.
  https://www.jirka.org/ra/realanal2.pdf

**Relationship to the sources:** This proves the local change-of-coordinates rule in Fréchet/covector notation. The exact surjective-map and germ versions are local calculus consequences, not a textbook theorem with the same signature.
-/

/-!
# Euler--Lagrange covariance under a change of coordinates

The actual tangent lift of `φ : E → F` sends `(y,w)` to `(φ y, Dφ(y) w)`, and
`pullbackEnergy φ L` is composition of the scalar energy with that lift. Chain rules give
the exact vertical and horizontal energy differentials. Along a curve, symmetry of the
actual second derivative of `φ` cancels the extra product-rule term in its momentum.

The resulting Euler--Lagrange equation pulls back without an inverse assumption. With
surjectivity of the actual coordinate derivative along the curve, the equations are
equivalent on the whole open time domain. The theorem uses arbitrary real normed spaces
and C2 coordinate map, energy, and position curve. It assumes neither an inner product,
finite dimensionality, a nonlinear inverse, nor a momentum differentiability oracle.
It does not require the pulled-back energy to be C2 or the coordinate map to be C3.
-/

open Set Filter Function
open scoped Topology ContDiff

noncomputable section
namespace OTSelector.Geometry

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The actual tangent lift of a coordinate map. -/
def tangentLift (φ : E → F) (z : E × E) : F × F :=
  (φ z.1, fderiv ℝ φ z.1 z.2)

/-- Pull back a scalar energy by the actual tangent lift. -/
def pullbackEnergy (φ : E → F) (L : F × F → ℝ) (z : E × E) : ℝ :=
  L (tangentLift φ z)

/-- A C2 energy has a C1 actual vertical differential. -/
theorem contDiffAt_fiberLegendre_one_of_two {L : F × F → ℝ} {z : F × F}
    (hL : ContDiffAt ℝ 2 L z) : ContDiffAt ℝ 1 (fiberLegendre L) z := by
  have h : ContDiffAt ℝ 2 (fun p : (F × F) × F ↦ L (p.1.1, p.2)) (z, z.2) :=
    hL.comp (z, z.2) (contDiffAt_fst.fst.prodMk contDiffAt_snd)
  exact h.fderiv contDiffAt_snd (by norm_num)

/-- The actual momentum along a C2 curve in a C2 energy domain is differentiable. -/
theorem differentiableAt_fiberLegendre_curve
    {L : F × F → ℝ} {O : Set (F × F)} (hO : IsOpen O)
    (hL : ContDiffOn ℝ 2 L O) {I : Set ℝ} (hI : IsOpen I) {x : ℝ → F}
    (hx : ContDiffOn ℝ 2 x I) (hphase : ∀ t ∈ I, (x t, deriv x t) ∈ O)
    {t : ℝ} (ht : t ∈ I) :
    DifferentiableAt ℝ (fun s ↦ fiberLegendre L (x s, deriv x s)) t := by
  have hx₁ : ContDiffAt ℝ 1 x t := (hx.contDiffAt (hI.mem_nhds ht)).of_le (by norm_num)
  have hv₁ : ContDiffAt ℝ 1 (deriv x) t :=
    (hx.deriv_of_isOpen hI (by norm_num : (1 : ℕ∞ω) + 1 ≤ 2)).contDiffAt (hI.mem_nhds ht)
  have hP := contDiffAt_fiberLegendre_one_of_two (hL.contDiffAt (hO.mem_nhds (hphase t ht)))
  exact (hP.comp t (hx₁.prodMk hv₁)).differentiableAt one_ne_zero

/-- The vertical energy differential transforms by covector pullback. -/
theorem fiberLegendre_pullbackEnergy {φ : E → F} {L : F × F → ℝ} {z : E × E}
    (hL : DifferentiableAt ℝ L (tangentLift φ z)) :
    fiberLegendre (pullbackEnergy φ L) z =
      (fiberLegendre L (tangentLift φ z)).comp (fderiv ℝ φ z.1) := by
  have hs := hL.hasFDerivAt.comp (fderiv ℝ φ z.1 z.2)
    (hasFDerivAt_prodMk_right (𝕜 := ℝ) (φ z.1) (fderiv ℝ φ z.1 z.2))
  have hs' : HasFDerivAt (fun v : F ↦ L (φ z.1, v))
      (fiberLegendre L (tangentLift φ z)) (fderiv ℝ φ z.1 z.2) :=
    hs.differentiableAt.hasFDerivAt
  exact (hs'.comp z.2 (fderiv ℝ φ z.1).hasFDerivAt).fderiv

/-- The base differential of the pullback contains the second derivative of the coordinate map. -/
theorem baseEnergyDifferential_pullbackEnergy_apply
    {φ : E → F} {L : F × F → ℝ} {y w : E}
    (hφ : ContDiffAt ℝ 2 φ y) (hL : DifferentiableAt ℝ L (tangentLift φ (y, w)))
    (η : E) :
    baseEnergyDifferential (pullbackEnergy φ L) (y, w) η =
      baseEnergyDifferential L (tangentLift φ (y, w)) (fderiv ℝ φ y η) +
        fiberLegendre L (tangentLift φ (y, w))
          (fderiv ℝ (fderiv ℝ φ) y η w) := by
  have hφD := (hφ.differentiableAt (by norm_num)).hasFDerivAt
  have hD := (hφ.fderiv_right (m := 1) (by norm_num)).differentiableAt_one.hasFDerivAt
  have hDw : HasFDerivAt (fun x ↦ fderiv ℝ φ x w)
      ((fderiv ℝ (fderiv ℝ φ) y).flip w) y := by
    simpa using hD.clm_apply (hasFDerivAt_const w y)
  have hcomp := hL.hasFDerivAt.comp y (hφD.prodMk hDw)
  change fderiv ℝ (fun x ↦ L (φ x, fderiv ℝ φ x w)) y η = _
  have heq := congrArg (fun A : E →L[ℝ] ℝ ↦ A η) hcomp.fderiv
  change fderiv ℝ (fun x ↦ L (φ x, fderiv ℝ φ x w)) y η = _ at heq
  rw [heq]
  exact fderiv_energy_split hL (fderiv ℝ φ y η) (fderiv ℝ (fderiv ℝ φ) y η w)

/-- The horizontal differential in the symmetric form used along a curve. -/
theorem baseEnergyDifferential_pullbackEnergy
    {φ : E → F} {L : F × F → ℝ} {y w : E}
    (hφ : ContDiffAt ℝ 2 φ y) (hL : DifferentiableAt ℝ L (tangentLift φ (y, w))) :
    baseEnergyDifferential (pullbackEnergy φ L) (y, w) =
      (baseEnergyDifferential L (tangentLift φ (y, w))).comp (fderiv ℝ φ y) +
        (fiberLegendre L (tangentLift φ (y, w))).comp
          (fderiv ℝ (fderiv ℝ φ) y w) := by
  apply ContinuousLinearMap.ext
  intro η
  rw [baseEnergyDifferential_pullbackEnergy_apply hφ hL]
  simp only [add_apply, ContinuousLinearMap.comp_apply]
  rw [(hφ.isSymmSndFDerivAt (by simp)).eq η w]

/-- The tangent lift uses the actual derivative of the composed position curve. -/
theorem tangentLift_curve_eq {φ : E → F} {y : ℝ → E} {t : ℝ}
    (hφ : DifferentiableAt ℝ φ (y t)) (hy : DifferentiableAt ℝ y t) :
    tangentLift φ (y t, deriv y t) = ((φ ∘ y) t, deriv (φ ∘ y) t) := by
  refine Prod.ext rfl ?_
  exact (hφ.hasFDerivAt.comp_hasDerivAt t hy.hasDerivAt).deriv.symm

/-- Product-rule formula for the actual momentum of the pulled-back energy.
The input is an actual derivative of the old momentum along the lifted curve. -/
theorem hasDerivAt_fiberLegendre_pullbackEnergy
    {φ : E → F} {L : F × F → ℝ} {y : ℝ → E} {t : ℝ} {P' : F →L[ℝ] ℝ}
    (hφ : ContDiffAt ℝ 2 φ (y t)) (hy : DifferentiableAt ℝ y t)
    (hL : ∀ᶠ s in 𝓝 t, DifferentiableAt ℝ L (tangentLift φ (y s, deriv y s)))
    (hP : HasDerivAt (fun s ↦ fiberLegendre L (tangentLift φ (y s, deriv y s))) P' t) :
    HasDerivAt (fun s ↦ fiberLegendre (pullbackEnergy φ L) (y s, deriv y s))
      (P'.comp (fderiv ℝ φ (y t)) +
        (fiberLegendre L (tangentLift φ (y t, deriv y t))).comp
          (fderiv ℝ (fderiv ℝ φ) (y t) (deriv y t))) t := by
  have hD := (hφ.fderiv_right (m := 1) (by norm_num)).differentiableAt_one.hasFDerivAt
  have hA := hD.comp_hasDerivAt t hy.hasDerivAt
  apply (hP.clm_comp hA).congr_of_eventuallyEq
  filter_upwards [hL] with s hs
  exact fiberLegendre_pullbackEnergy hs

/-- Euler--Lagrange equations pull back along a C2 coordinate map without an inverse assumption. -/
theorem hasDerivAt_eulerLagrange_pullback
    {φ : E → F} {L : F × F → ℝ} {U : Set E} {O : Set (F × F)}
    (hU : IsOpen U) (hO : IsOpen O)
    (hφ : ContDiffOn ℝ 2 φ U) (hL : ContDiffOn ℝ 2 L O)
    {I : Set ℝ} (hI : IsOpen I) {y : ℝ → E}
    (hy : ContDiffOn ℝ 2 y I) (hbase : MapsTo y I U)
    (hphase : ∀ s ∈ I, tangentLift φ (y s, deriv y s) ∈ O)
    {t : ℝ} (ht : t ∈ I)
    (hEL : HasDerivAt
      (fun s ↦ fiberLegendre L ((φ ∘ y) s, deriv (φ ∘ y) s))
      (baseEnergyDifferential L ((φ ∘ y) t, deriv (φ ∘ y) t)) t) :
    HasDerivAt (fun s ↦ fiberLegendre (pullbackEnergy φ L) (y s, deriv y s))
      (baseEnergyDifferential (pullbackEnergy φ L) (y t, deriv y t)) t := by
  have hyD (s : ℝ) (hs : s ∈ I) :=
    (hy.contDiffAt (hI.mem_nhds hs)).differentiableAt (by norm_num)
  have hφD (s : ℝ) (hs : s ∈ I) :=
    (hφ.contDiffAt (hU.mem_nhds (hbase hs))).differentiableAt (by norm_num)
  have hlift (s : ℝ) (hs : s ∈ I) := tangentLift_curve_eq (hφD s hs) (hyD s hs)
  have hLD (s : ℝ) (hs : s ∈ I) :=
    (hL.contDiffAt (hO.mem_nhds (hphase s hs))).differentiableAt (by norm_num)
  have heq : (fun s ↦ fiberLegendre L (tangentLift φ (y s, deriv y s))) =ᶠ[𝓝 t]
      (fun s ↦ fiberLegendre L ((φ ∘ y) s, deriv (φ ∘ y) s)) := by
    filter_upwards [hI.mem_nhds ht] with s hs
    rw [hlift s hs]
  have h := hasDerivAt_fiberLegendre_pullbackEnergy
    (hφ.contDiffAt (hU.mem_nhds (hbase ht))) (hyD t ht)
    (Filter.eventually_of_mem (hI.mem_nhds ht) hLD) (hEL.congr_of_eventuallyEq heq)
  apply h.congr_deriv
  rw [baseEnergyDifferential_pullbackEnergy
    (hφ.contDiffAt (hU.mem_nhds (hbase ht))) (hLD t ht), hlift t ht]

/-- On an open time domain, Euler--Lagrange equations are equivalent under a C2
coordinate map whose actual derivative is surjective along the curve. No inverse
map or differentiability of the pulled-back momentum is assumed. -/
theorem eulerLagrange_pullback_iff
    {φ : E → F} {L : F × F → ℝ} {U : Set E} {O : Set (F × F)}
    (hU : IsOpen U) (hO : IsOpen O)
    (hφ : ContDiffOn ℝ 2 φ U) (hL : ContDiffOn ℝ 2 L O)
    {I : Set ℝ} (hI : IsOpen I) {y : ℝ → E}
    (hy : ContDiffOn ℝ 2 y I) (hbase : MapsTo y I U)
    (hphase : ∀ t ∈ I, tangentLift φ (y t, deriv y t) ∈ O)
    (hsurj : ∀ t ∈ I, Function.Surjective (fderiv ℝ φ (y t))) :
    (∀ t ∈ I,
      HasDerivAt (fun s ↦ fiberLegendre (pullbackEnergy φ L) (y s, deriv y s))
        (baseEnergyDifferential (pullbackEnergy φ L) (y t, deriv y t)) t) ↔
    (∀ t ∈ I,
      HasDerivAt (fun s ↦ fiberLegendre L ((φ ∘ y) s, deriv (φ ∘ y) s))
        (baseEnergyDifferential L ((φ ∘ y) t, deriv (φ ∘ y) t)) t) := by
  constructor
  · intro hnew t ht
    have hyD (s : ℝ) (hs : s ∈ I) :=
      (hy.contDiffAt (hI.mem_nhds hs)).differentiableAt (by norm_num)
    have hφD (s : ℝ) (hs : s ∈ I) :=
      (hφ.contDiffAt (hU.mem_nhds (hbase hs))).differentiableAt (by norm_num)
    have hlift (s : ℝ) (hs : s ∈ I) := tangentLift_curve_eq (hφD s hs) (hyD s hs)
    have hLD (s : ℝ) (hs : s ∈ I) :=
      (hL.contDiffAt (hO.mem_nhds (hphase s hs))).differentiableAt (by norm_num)
    have hphaseOld : ∀ s ∈ I, ((φ ∘ y) s, deriv (φ ∘ y) s) ∈ O := by
      intro s hs
      rw [← hlift s hs]
      exact hphase s hs
    have hP := differentiableAt_fiberLegendre_curve hO hL hI (hφ.comp hy hbase) hphaseOld ht
    have heq : (fun s ↦ fiberLegendre L (tangentLift φ (y s, deriv y s))) =ᶠ[𝓝 t]
        (fun s ↦ fiberLegendre L ((φ ∘ y) s, deriv (φ ∘ y) s)) := by
      filter_upwards [hI.mem_nhds ht] with s hs
      rw [hlift s hs]
    have hd := hasDerivAt_fiberLegendre_pullbackEnergy
      (hφ.contDiffAt (hU.mem_nhds (hbase ht))) (hyD t ht)
      (Filter.eventually_of_mem (hI.mem_nhds ht) hLD) (hP.hasDerivAt.congr_of_eventuallyEq heq)
    have hcov := hd.unique (hnew t ht)
    rw [baseEnergyDifferential_pullbackEnergy
      (hφ.contDiffAt (hU.mem_nhds (hbase ht))) (hLD t ht), hlift t ht] at hcov
    have hcomp := add_right_cancel hcov
    apply hP.hasDerivAt.congr_deriv
    apply ContinuousLinearMap.ext
    intro v
    obtain ⟨η, rfl⟩ := hsurj t ht v
    exact congrArg (fun A : E →L[ℝ] ℝ ↦ A η) hcomp
  · intro hold t ht
    exact hasDerivAt_eulerLagrange_pullback hU hO hφ hL hI hy hbase hphase ht (hold t ht)

end OTSelector.Geometry
