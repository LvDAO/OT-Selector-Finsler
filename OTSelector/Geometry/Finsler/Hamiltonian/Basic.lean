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

/-!
## Lemma skeleton

* **Conditions:** A scalar coordinate energy and an actual local inverse of its base-preserving Legendre map. Differential identities use differentiability; smoothness uses smooth L and inverse. The existence theorem derives the inverse from a positive vertical Hessian in finite dimension.
* **Objects:** H(x,p)=p(v)-L(x,v), d_xL, and X_H=(v,d_xL), where (x,v) is given by the inverse Legendre branch.
* **Proof detail:** Recover the base coordinate and momentum from the inverse identities. Differentiate H; the inverse-velocity derivative terms cancel, leaving dH(δx,δp)=δp(v)-d_xL(δx). Pairing X_H with itself gives zero energy derivative.

## Mathematical sources

* Gerald Teschl, *Ordinary Differential Equations and Dynamical Systems (AMS 2012 author preliminary version)*, Section 8.3, pp. 239–241, equations (8.39)–(8.43), (8.47), and Problem 8.9.
  https://www.mat.univie.ac.at/~gerald/ftp/book-ode/ode.pdf#page=250
* Matias Dahl, *An brief introduction to Finsler geometry (12 July 2006)*, Section 7.1, Proposition 7.10 and Example 7.11, pp. 33–34.
  https://math.aalto.fi/~fdahl/finsler/finsler.pdf#page=33

**Relationship to the sources:** This is the local open-domain Fréchet formulation of the Legendre Hamiltonian and Hamilton equations. The definitions use position before velocity; Teschl uses the opposite ordering in L. Covectors remain in the continuous dual.
-/

/-!
# Actual local Hamiltonians from coordinate energies

For the actual local Legendre inverse constructed in `ParametricLegendre`, define
`H(x,p) = p(v) - L(x,v)` with `(x,v)` given by the inverse. The inverse identities
imply preservation of the base coordinate and recovery of `d_v L = p`; differentiating
these identities makes all inverse-velocity derivative terms cancel. The proved
Fréchet differential is `dH(δx,δp) = δp(v) - d_x L(δx)`.

The resulting vector field `(v, d_x L)` is jointly smooth and satisfies the canonical
Hamiltonian differential identity. The final existence theorem constructs the inverse,
Hamiltonian and smooth field from scalar smoothness and positive actual vertical
Hessian on an arbitrary open domain. No inverse or Hamiltonian formula is a premise
of that theorem.

The coordinate base and velocity use the same real normed space, while covectors remain
in its continuous dual. No inner product is selected. These are local differential and
smoothness statements; coordinate invariance, ODE solutions and global flow are not
asserted here.
-/

open Set Filter
open scoped Topology ContDiff

namespace OTSelector.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The actual base differential of the coordinate energy, holding velocity fixed. -/
noncomputable def baseEnergyDifferential (L : E × E → ℝ) (z : E × E) : E →L[ℝ] ℝ :=
  fderiv ℝ (fun x ↦ L (x, z.2)) z.1

/-- The local Legendre transform of the actual scalar energy. -/
noncomputable def localHamiltonian (L : E × E → ℝ)
    (e : OpenPartialHomeomorph (E × E) (E × (E →L[ℝ] ℝ)))
    (p : E × (E →L[ℝ] ℝ)) : ℝ :=
  p.2 ((e.symm p).2) - L (e.symm p)

/-- The coordinate Hamiltonian vector field, with actual inverse velocity and base differential. -/
noncomputable def localHamiltonianVectorField (L : E × E → ℝ)
    (e : OpenPartialHomeomorph (E × E) (E × (E →L[ℝ] ℝ)))
    (p : E × (E →L[ℝ] ℝ)) : E × (E →L[ℝ] ℝ) :=
  ((e.symm p).2, baseEnergyDifferential L (e.symm p))

/-- Smoothness of the scalar energy implies joint smoothness of its actual base differential. -/
theorem contDiffAt_baseEnergyDifferential {L : E × E → ℝ} {z : E × E}
    (hL : ContDiffAt ℝ ∞ L z) : ContDiffAt ℝ ∞ (baseEnergyDifferential L) z := by
  have h : ContDiffAt ℝ ∞ (fun p : (E × E) × E ↦ L (p.2, p.1.2)) (z, z.1) :=
    hL.comp (z, z.1) (contDiffAt_snd.prodMk contDiffAt_fst.snd)
  exact h.fderiv contDiffAt_fst (by simp)

/-- The actual scalar energy differential splits into its base and velocity differentials. -/
theorem fderiv_energy_split {L : E × E → ℝ} {z : E × E}
    (hL : DifferentiableAt ℝ L z) (b w : E) :
    fderiv ℝ L z (b, w) = baseEnergyDifferential L z b + fiberLegendre L z w := by
  have hl := hL.hasFDerivAt.comp z.1 (hasFDerivAt_prodMk_left (𝕜 := ℝ) z.1 z.2)
  have hr := hL.hasFDerivAt.comp z.2 (hasFDerivAt_prodMk_right (𝕜 := ℝ) z.1 z.2)
  have hsplit : (b, w) = (b, 0) + (0, w) := by simp
  rw [hsplit, map_add]
  congr 1
  · exact (congrArg (fun T : E →L[ℝ] ℝ ↦ T b) hl.fderiv).symm
  · exact (congrArg (fun T : E →L[ℝ] ℝ ↦ T w) hr.fderiv).symm

/-- The constructed Legendre inverse preserves base and recovers the given covector. -/
theorem parametricLegendre_inverse_components
    {L : E × E → ℝ} {e : OpenPartialHomeomorph (E × E) (E × (E →L[ℝ] ℝ))}
    (he : (e : (E × E) → (E × (E →L[ℝ] ℝ))) = parametricLegendre L)
    {p : E × (E →L[ℝ] ℝ)} (hp : p ∈ e.target) :
    (e.symm p).1 = p.1 ∧ fiberLegendre L (e.symm p) = p.2 := by
  have h := e.right_inv hp
  rw [he] at h
  exact ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩

/-- Any derivative of the actual local Legendre inverse has identity base component. -/
theorem parametricLegendre_inverse_derivative_fst
    {L : E × E → ℝ} {e : OpenPartialHomeomorph (E × E) (E × (E →L[ℝ] ℝ))}
    (he : (e : (E × E) → (E × (E →L[ℝ] ℝ))) = parametricLegendre L)
    {p : E × (E →L[ℝ] ℝ)} (hp : p ∈ e.target)
    {G : (E × (E →L[ℝ] ℝ)) →L[ℝ] (E × E)} (hG : HasFDerivAt e.symm G p) :
    (ContinuousLinearMap.fst ℝ E E).comp G = ContinuousLinearMap.fst ℝ E (E →L[ℝ] ℝ) := by
  apply hG.fst.unique
  apply hasFDerivAt_fst.congr_of_eventuallyEq
  filter_upwards [e.open_target.mem_nhds hp] with q hq
  exact (parametricLegendre_inverse_components he hq).1

/-- Differentiating the actual Legendre energy cancels every inverse-velocity derivative
term, leaving `δp(v) - D_x L(δx)`. -/
theorem hasFDerivAt_localHamiltonian
    {L : E × E → ℝ} {e : OpenPartialHomeomorph (E × E) (E × (E →L[ℝ] ℝ))}
    (he : (e : (E × E) → (E × (E →L[ℝ] ℝ))) = parametricLegendre L)
    {p : E × (E →L[ℝ] ℝ)} (hp : p ∈ e.target)
    (hL : DifferentiableAt ℝ L (e.symm p))
    {G : (E × (E →L[ℝ] ℝ)) →L[ℝ] (E × E)} (hG : HasFDerivAt e.symm G p) :
    HasFDerivAt (localHamiltonian L e)
      ((ContinuousLinearMap.snd ℝ E (E →L[ℝ] ℝ)).flip (e.symm p).2 -
        (baseEnergyDifferential L (e.symm p)).comp
          (ContinuousLinearMap.fst ℝ E (E →L[ℝ] ℝ))) p := by
  have heval := (hasFDerivAt_snd (𝕜 := ℝ) (p := p)).clm_apply hG.snd
  have hraw := heval.sub (hL.hasFDerivAt.comp p hG)
  apply hraw.congr_fderiv
  apply ContinuousLinearMap.ext
  intro dq
  change p.2 (G dq).2 + dq.2 (e.symm p).2 - fderiv ℝ L (e.symm p) (G dq) =
    dq.2 (e.symm p).2 - baseEnergyDifferential L (e.symm p) dq.1
  have hfst : (G dq).1 = dq.1 :=
    congrArg (fun T : (E × (E →L[ℝ] ℝ)) →L[ℝ] E ↦ T dq)
      (parametricLegendre_inverse_derivative_fst he hp hG)
  have hs := fderiv_energy_split hL (G dq).1 (G dq).2
  change fderiv ℝ L (e.symm p) (G dq) = _ at hs
  rw [hs, (parametricLegendre_inverse_components he hp).2, hfst]
  ring

/-- Pointwise actual differential formula for the local Hamiltonian. -/
theorem localHamiltonian_fderiv_apply
    {L : E × E → ℝ} {e : OpenPartialHomeomorph (E × E) (E × (E →L[ℝ] ℝ))}
    (he : (e : (E × E) → (E × (E →L[ℝ] ℝ))) = parametricLegendre L)
    {p : E × (E →L[ℝ] ℝ)} (hp : p ∈ e.target)
    (hL : DifferentiableAt ℝ L (e.symm p))
    (hG : DifferentiableAt ℝ e.symm p) (dq : E × (E →L[ℝ] ℝ)) :
    fderiv ℝ (localHamiltonian L e) p dq =
      dq.2 (e.symm p).2 - baseEnergyDifferential L (e.symm p) dq.1 := by
  rw [(hasFDerivAt_localHamiltonian he hp hL hG.hasFDerivAt).fderiv]
  rfl

/-- The actual local Hamiltonian is jointly smooth throughout the inverse chart target. -/
theorem contDiffOn_localHamiltonian
    {L : E × E → ℝ} {e : OpenPartialHomeomorph (E × E) (E × (E →L[ℝ] ℝ))}
    (hL : ContDiffOn ℝ ∞ L e.source) (hG : ContDiffOn ℝ ∞ e.symm e.target) :
    ContDiffOn ℝ ∞ (localHamiltonian L e) e.target := by
  exact (contDiffOn_snd.clm_apply hG.snd).sub (hL.comp hG (fun _ hp ↦ e.map_target hp))

/-- The actual Hamiltonian vector field is jointly smooth on the inverse chart target. -/
theorem contDiffOn_localHamiltonianVectorField
    {L : E × E → ℝ} {e : OpenPartialHomeomorph (E × E) (E × (E →L[ℝ] ℝ))}
    (hL : ContDiffOn ℝ ∞ L e.source) (hG : ContDiffOn ℝ ∞ e.symm e.target) :
    ContDiffOn ℝ ∞ (localHamiltonianVectorField L e) e.target := by
  apply e.open_target.contDiffOn_iff.mpr
  intro p hp
  have hGp := hG.contDiffAt (e.open_target.mem_nhds hp)
  have hLp := hL.contDiffAt (e.open_source.mem_nhds (e.map_target hp))
  exact hGp.snd.prodMk ((contDiffAt_baseEnergyDifferential hLp).comp p hGp)

/-- The actual vector field satisfies the canonical Hamiltonian differential identity. -/
theorem localHamiltonianVectorField_identity
    {L : E × E → ℝ} {e : OpenPartialHomeomorph (E × E) (E × (E →L[ℝ] ℝ))}
    (he : (e : (E × E) → (E × (E →L[ℝ] ℝ))) = parametricLegendre L)
    {p : E × (E →L[ℝ] ℝ)} (hp : p ∈ e.target)
    (hL : DifferentiableAt ℝ L (e.symm p))
    (hG : DifferentiableAt ℝ e.symm p) (dq : E × (E →L[ℝ] ℝ)) :
    fderiv ℝ (localHamiltonian L e) p dq =
      dq.2 (localHamiltonianVectorField L e p).1 -
        (localHamiltonianVectorField L e p).2 dq.1 :=
  localHamiltonian_fderiv_apply he hp hL hG dq

/-- The Hamiltonian differential annihilates its actual Hamiltonian vector field. -/
theorem localHamiltonianVectorField_energy_identity
    {L : E × E → ℝ} {e : OpenPartialHomeomorph (E × E) (E × (E →L[ℝ] ℝ))}
    (he : (e : (E × E) → (E × (E →L[ℝ] ℝ))) = parametricLegendre L)
    {p : E × (E →L[ℝ] ℝ)} (hp : p ∈ e.target)
    (hL : DifferentiableAt ℝ L (e.symm p))
    (hG : DifferentiableAt ℝ e.symm p) :
    fderiv ℝ (localHamiltonian L e) p (localHamiltonianVectorField L e p) = 0 := by
  rw [localHamiltonianVectorField_identity he hp hL hG, sub_self]

/-- Standard local smoothness and positive actual vertical Hessian construct an actual
jointly smooth local Hamiltonian chart and its Hamiltonian vector field. No inverse or
Hamiltonian differential formula is assumed. -/
theorem exists_smooth_localHamiltonian [FiniteDimensional ℝ E]
    {L : E × E → ℝ} {U : Set (E × E)} (hU : IsOpen U)
    (hL : ContDiffOn ℝ ∞ L U)
    (hpos : ∀ z ∈ U, ∀ w : E, w ≠ 0 →
      0 < fderiv ℝ (fderiv ℝ (fun u ↦ L (z.1, u))) z.2 w w)
    {z : E × E} (hz : z ∈ U) :
    ∃ e : OpenPartialHomeomorph (E × E) (E × (E →L[ℝ] ℝ)),
      (e : (E × E) → (E × (E →L[ℝ] ℝ))) = parametricLegendre L ∧
      z ∈ e.source ∧ parametricLegendre L z ∈ e.target ∧ e.source ⊆ U ∧
      ContDiffOn ℝ ∞ e.symm e.target ∧
      ContDiffOn ℝ ∞ (localHamiltonian L e) e.target ∧
      ContDiffOn ℝ ∞ (localHamiltonianVectorField L e) e.target ∧
      ∀ p ∈ e.target, ∀ dq : E × (E →L[ℝ] ℝ),
        fderiv ℝ (localHamiltonian L e) p dq =
          dq.2 (localHamiltonianVectorField L e p).1 -
            (localHamiltonianVectorField L e p).2 dq.1 := by
  obtain ⟨e, he, hzsource, htarget, hsource, _, hinverse, _, _⟩ :=
    exists_smooth_parametricLegendre_local_inverse hU hL hpos hz
  have hLs := hL.mono hsource
  refine ⟨e, he, hzsource, htarget, hsource, hinverse,
    contDiffOn_localHamiltonian hLs hinverse,
    contDiffOn_localHamiltonianVectorField hLs hinverse, ?_⟩
  intro p hp dq
  have hLp := (hLs.contDiffAt (e.open_source.mem_nhds (e.map_target hp))).differentiableAt
    (by simp)
  have hGp := (hinverse.contDiffAt (e.open_target.mem_nhds hp)).differentiableAt (by simp)
  exact localHamiltonianVectorField_identity he hp hLp hGp dq

end OTSelector.Geometry
