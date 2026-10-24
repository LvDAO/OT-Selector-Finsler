import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
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
import OTSelector.Analysis.Convex.HomogeneousEnergy
import OTSelector.Analysis.Convex.Legendre.Parametric
import OTSelector.Geometry.Finsler.Basic
import OTSelector.Geometry.Finsler.Energy.Basic
import OTSelector.Geometry.Finsler.Energy.Chart
import OTSelector.Geometry.Finsler.Hamiltonian.Basic

/-!
## Lemma skeleton

* **Conditions:** A smooth energy, an actual smooth local Legendre inverse and a point of its open target. Positive vertical Hessian supplies positivity; finite dimension is used for inverse-Hessian identifications and existence conclusions.
* **Objects:** The actual vertical energy Hessian; derivative of inverse velocity in momentum; actual Hamiltonian second derivative and canonical blocks A,B,C of DX_H.
* **Proof detail:** Differentiate the inverse Legendre identity to identify H_pp with the inverse vertical Hessian. Differentiate dH=omega(X_H,·); symmetry of the actual scalar Hessian gives symmetric A,C and DX_H(b,q)=(Bb+Cq,-Ab-q∘B).

## Mathematical sources

* Matias Dahl, *An brief introduction to Finsler geometry (12 July 2006)*, Section 1.2, Definition 1.8, Propositions 1.9–1.10, pp. 6–8; equations (3)–(8).
  https://math.aalto.fi/~fdahl/finsler/finsler.pdf#page=6
* Gerald Teschl, *Ordinary Differential Equations and Dynamical Systems (AMS 2012 author preliminary version)*, Section 8.3, pp. 239–241, equations (8.39)–(8.43), (8.47), and Problem 8.9.
  https://www.mat.univie.ac.at/~gerald/ftp/book-ode/ode.pdf#page=250
* Jiří Lebl, *Basic Analysis II: Introduction to Real Analysis, Volume II (version 6.3, 15 May 2026)*, Section 8.3, Theorem 8.3.7, p. 38; Exercise 8.3.7, p. 45 (differentiate the inverse identity).
  https://www.jirka.org/ra/realanal2.pdf#page=38
* Jiří Lebl, *Basic Analysis II: Introduction to Real Analysis, Volume II (version 6.3, 15 May 2026)*, Section 8.6, Proposition 8.6.2, pp. 60–61 (equality of mixed second partial derivatives).
  https://www.jirka.org/ra/realanal2.pdf#page=60

**Relationship to the sources:** The inverse-Hessian relation is the local differential form of Legendre duality. Canonical blocks, mixed dual transpose and their positivity are derived here by chain rule and Hessian symmetry; no auxiliary Euclidean gradient is introduced.
-/

/-!
# Actual Hamiltonian Hessians and canonical linearization

For the genuine local Legendre inverse of a smooth coordinate energy, differentiation of
its inverse identity identifies the momentum derivative of inverse velocity with the inverse
actual vertical energy Hessian. Differentiating the proved canonical differential identity
then gives the momentum-momentum Hessian of the actual Hamiltonian under the canonical
vector-covector pairing. Strong convexity implies strict positivity of this block.

All three blocks `A`, `B`, and `C` are extracted from the actual derivative of the canonical
field. Symmetry of the actual scalar Hessian proves that `A` and `C` are symmetric and gives
`DX(b,q) = (B b + C q, -A b - q ∘ B)`. The covector precomposition is the dual transpose;
no inner product identification of vectors and covectors is introduced.

The existence results construct the Legendre chart from smoothness and strong convexity,
and the final theorem specializes them to the actual energy of a smooth strongly convex
Finsler structure in tangent coordinates. The module proves local differential identities;
it does not construct geodesic variations, a global flow, or its Jacobi fields.
-/

open Set Filter Manifold
open scoped Topology ContDiff

namespace OTSelector.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The actual vertical Hessian of a coordinate Lagrangian. -/
noncomputable def verticalEnergyHessian (L : E × E → ℝ) (z : E × E) :
    E →L[ℝ] (E →L[ℝ] ℝ) :=
  fderiv ℝ (fderiv ℝ (fun v ↦ L (z.1, v))) z.2

/-- Momentum derivative of the actual inverse Legendre velocity, without identifying the dual. -/
noncomputable def inverseLegendreMomentumDerivative
    (e : OpenPartialHomeomorph (E × E) (E × (E →L[ℝ] ℝ)))
    (p : E × (E →L[ℝ] ℝ)) : (E →L[ℝ] ℝ) →L[ℝ] E :=
  ((ContinuousLinearMap.snd ℝ E E).comp (fderiv ℝ e.symm p)).comp
    (ContinuousLinearMap.inr ℝ E (E →L[ℝ] ℝ))

/-- Differentiating the genuine inverse identity recovers every momentum variation. -/
theorem verticalEnergyHessian_inverseLegendreMomentumDerivative
    {L : E × E → ℝ} {e : OpenPartialHomeomorph (E × E) (E × (E →L[ℝ] ℝ))}
    (he : (e : (E × E) → (E × (E →L[ℝ] ℝ))) = parametricLegendre L)
    {p : E × (E →L[ℝ] ℝ)} (hp : p ∈ e.target)
    (hL : ContDiffAt ℝ ∞ L (e.symm p)) (hG : DifferentiableAt ℝ e.symm p)
    (q : E →L[ℝ] ℝ) :
    verticalEnergyHessian L (e.symm p) (inverseLegendreMomentumDerivative e p q) = q := by
  have hcomp := (hasFDerivAt_parametricLegendre hL).comp p hG.hasFDerivAt
  have hid : HasFDerivAt (fun y ↦ parametricLegendre L (e.symm y))
      (ContinuousLinearMap.id ℝ (E × (E →L[ℝ] ℝ))) p := by
    apply (hasFDerivAt_id p).congr_of_eventuallyEq
    filter_upwards [e.open_target.mem_nhds hp] with y hy
    exact (congrFun he (e.symm y)).symm.trans (e.right_inv hy)
  have hId := congrArg (fun T : (E × (E →L[ℝ] ℝ)) →L[ℝ]
      (E × (E →L[ℝ] ℝ)) ↦ T (0, q)) (hcomp.unique hid)
  have hfst : (fderiv ℝ e.symm p (0, q)).1 = 0 :=
    congrArg (fun T : (E × (E →L[ℝ] ℝ)) →L[ℝ] E ↦ T (0, q))
      (parametricLegendre_inverse_derivative_fst he hp hG.hasFDerivAt)
  have hpair : fderiv ℝ e.symm p (0, q) =
      (0, inverseLegendreMomentumDerivative e p q) := Prod.ext hfst rfl
  have hId' : fderiv ℝ (parametricLegendre L) (e.symm p)
      (fderiv ℝ e.symm p (0, q)) = (0, q) := by
    rw [parametricLegendre_fderiv_eq hL]
    exact hId
  rw [hpair, parametricLegendre_fderiv_apply hL] at hId'
  simpa only [Prod.mk_zero_zero, map_zero, zero_add, verticalEnergyHessian] using
    congrArg Prod.snd hId'

/-- Positive actual vertical energy Hessians make inverse-velocity momentum derivatives positive. -/
theorem inverseLegendreMomentumDerivative_pos
    {L : E × E → ℝ} {e : OpenPartialHomeomorph (E × E) (E × (E →L[ℝ] ℝ))}
    (he : (e : (E × E) → (E × (E →L[ℝ] ℝ))) = parametricLegendre L)
    {p : E × (E →L[ℝ] ℝ)} (hp : p ∈ e.target)
    (hL : ContDiffAt ℝ ∞ L (e.symm p)) (hG : DifferentiableAt ℝ e.symm p)
    (hpos : ∀ w : E, w ≠ 0 → 0 < verticalEnergyHessian L (e.symm p) w w)
    {q : E →L[ℝ] ℝ} (hq : q ≠ 0) :
    0 < q (inverseLegendreMomentumDerivative e p q) := by
  have hinv := verticalEnergyHessian_inverseLegendreMomentumDerivative he hp hL hG q
  have hw : inverseLegendreMomentumDerivative e p q ≠ 0 := by
    intro hzero
    apply hq
    rw [← hinv, hzero, map_zero]
  calc
    0 < verticalEnergyHessian L (e.symm p)
        (inverseLegendreMomentumDerivative e p q)
        (inverseLegendreMomentumDerivative e p q) := hpos _ hw
    _ = q (inverseLegendreMomentumDerivative e p q) :=
      congrArg (fun r : E →L[ℝ] ℝ ↦ r (inverseLegendreMomentumDerivative e p q)) hinv

/-- In finite dimension the actual inverse-velocity derivative is the inverse true energy
Hessian. -/
theorem inverseLegendreMomentumDerivative_eq_inverse [FiniteDimensional ℝ E]
    {L : E × E → ℝ} {e : OpenPartialHomeomorph (E × E) (E × (E →L[ℝ] ℝ))}
    (he : (e : (E × E) → (E × (E →L[ℝ] ℝ))) = parametricLegendre L)
    {p : E × (E →L[ℝ] ℝ)} (hp : p ∈ e.target)
    (hL : ContDiffAt ℝ ∞ L (e.symm p)) (hG : DifferentiableAt ℝ e.symm p)
    (hpos : ∀ w : E, w ≠ 0 → 0 < verticalEnergyHessian L (e.symm p) w w) :
    inverseLegendreMomentumDerivative e p =
      ContinuousLinearMap.inverse (verticalEnergyHessian L (e.symm p)) := by
  let d := positive_dualMap_equiv (verticalEnergyHessian L (e.symm p)) hpos
  have hd : ContinuousLinearMap.inverse (verticalEnergyHessian L (e.symm p)) =
      d.symm.toContinuousLinearMap := ContinuousLinearMap.inverse_equiv d
  rw [hd]
  apply ContinuousLinearMap.ext
  intro q
  apply d.injective
  change d (inverseLegendreMomentumDerivative e p q) = d (d.symm q)
  rw [d.apply_symm_apply]
  exact verticalEnergyHessian_inverseLegendreMomentumDerivative he hp hL hG q

/-- Differentiating the canonical identity identifies the actual Hessian with the
actual linearized Hamiltonian field through the canonical dual pairing. -/
theorem localHamiltonian_hessian_field_identity
    {L : E × E → ℝ} {e : OpenPartialHomeomorph (E × E) (E × (E →L[ℝ] ℝ))}
    (he : (e : (E × E) → (E × (E →L[ℝ] ℝ))) = parametricLegendre L)
    (hL : ContDiffOn ℝ ∞ L e.source) (hG : ContDiffOn ℝ ∞ e.symm e.target)
    {p : E × (E →L[ℝ] ℝ)} (hp : p ∈ e.target)
    (u v : E × (E →L[ℝ] ℝ)) :
    fderiv ℝ (fderiv ℝ (localHamiltonian L e)) p u v =
      v.2 (fderiv ℝ (localHamiltonianVectorField L e) p u).1 -
        (fderiv ℝ (localHamiltonianVectorField L e) p u).2 v.1 := by
  have hH := (contDiffOn_localHamiltonian hL hG).contDiffAt
    (e.open_target.mem_nhds hp)
  have hDH : DifferentiableAt ℝ (fderiv ℝ (localHamiltonian L e)) p :=
    (hH.fderiv_right (m := ∞) (by simp)).differentiableAt (by simp)
  have hX := ((contDiffOn_localHamiltonianVectorField hL hG).contDiffAt
    (e.open_target.mem_nhds hp)).differentiableAt (by simp)
  have hleft := hDH.hasFDerivAt.clm_apply (hasFDerivAt_const v p)
  have hright := (v.2.hasFDerivAt.comp p hX.hasFDerivAt.fst).sub
    (hX.hasFDerivAt.snd.clm_apply (hasFDerivAt_const v.1 p))
  have heq : (fun z ↦ fderiv ℝ (localHamiltonian L e) z v) =ᶠ[𝓝 p]
      (fun z ↦ v.2 (localHamiltonianVectorField L e z).1 -
        (localHamiltonianVectorField L e z).2 v.1) := by
    filter_upwards [e.open_target.mem_nhds hp] with z hz
    exact localHamiltonianVectorField_identity he hz
      ((hL.contDiffAt (e.open_source.mem_nhds (e.map_target hz))).differentiableAt
        (by simp))
      ((hG.contDiffAt (e.open_target.mem_nhds hz)).differentiableAt (by simp)) v
  have hd := hleft.unique (hright.congr_of_eventuallyEq heq)
  have h := congrArg (fun T : (E × (E →L[ℝ] ℝ)) →L[ℝ] ℝ ↦ T u) hd
  simpa only [add_apply, ContinuousLinearMap.comp_apply,
    zero_apply, ContinuousLinearMap.map_zero, zero_add,
    ContinuousLinearMap.flip_apply, sub_apply,
    ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd'] using h

/-- The first row of the actual canonical linearization is the derivative of inverse velocity. -/
theorem localHamiltonianVectorField_fderiv_fst
    {L : E × E → ℝ} {e : OpenPartialHomeomorph (E × E) (E × (E →L[ℝ] ℝ))}
    (hL : ContDiffOn ℝ ∞ L e.source) (hG : ContDiffOn ℝ ∞ e.symm e.target)
    {p : E × (E →L[ℝ] ℝ)} (hp : p ∈ e.target) (u : E × (E →L[ℝ] ℝ)) :
    (fderiv ℝ (localHamiltonianVectorField L e) p u).1 =
      (fderiv ℝ e.symm p u).2 := by
  have hX := ((contDiffOn_localHamiltonianVectorField hL hG).contDiffAt
    (e.open_target.mem_nhds hp)).differentiableAt (by simp)
  have hGi := (hG.contDiffAt (e.open_target.mem_nhds hp)).differentiableAt (by simp)
  exact congrArg (fun T : (E × (E →L[ℝ] ℝ)) →L[ℝ] E ↦ T u)
    (hX.hasFDerivAt.fst.unique hGi.hasFDerivAt.snd)

/-- The true momentum-momentum Hamiltonian Hessian is evaluated by the actual inverse velocity. -/
theorem localHamiltonian_momentum_hessian_apply
    {L : E × E → ℝ} {e : OpenPartialHomeomorph (E × E) (E × (E →L[ℝ] ℝ))}
    (he : (e : (E × E) → (E × (E →L[ℝ] ℝ))) = parametricLegendre L)
    (hL : ContDiffOn ℝ ∞ L e.source) (hG : ContDiffOn ℝ ∞ e.symm e.target)
    {p : E × (E →L[ℝ] ℝ)} (hp : p ∈ e.target) (q r : E →L[ℝ] ℝ) :
    fderiv ℝ (fderiv ℝ (localHamiltonian L e)) p (0, q) (0, r) =
      r (inverseLegendreMomentumDerivative e p q) := by
  rw [localHamiltonian_hessian_field_identity he hL hG hp,
    localHamiltonianVectorField_fderiv_fst hL hG hp]
  simp only [map_zero, sub_zero]
  rfl

/-- The actual momentum Hessian equals the inverse actual vertical energy Hessian under
canonical double-dual evaluation, with no chosen inner product. -/
theorem localHamiltonian_momentum_hessian_eq_inverse [FiniteDimensional ℝ E]
    {L : E × E → ℝ} {e : OpenPartialHomeomorph (E × E) (E × (E →L[ℝ] ℝ))}
    (he : (e : (E × E) → (E × (E →L[ℝ] ℝ))) = parametricLegendre L)
    (hL : ContDiffOn ℝ ∞ L e.source) (hG : ContDiffOn ℝ ∞ e.symm e.target)
    {p : E × (E →L[ℝ] ℝ)} (hp : p ∈ e.target)
    (hpos : ∀ w : E, w ≠ 0 → 0 < verticalEnergyHessian L (e.symm p) w w)
    (q r : E →L[ℝ] ℝ) :
    fderiv ℝ (fderiv ℝ (localHamiltonian L e)) p (0, q) (0, r) =
      r (ContinuousLinearMap.inverse (verticalEnergyHessian L (e.symm p)) q) := by
  rw [localHamiltonian_momentum_hessian_apply he hL hG hp,
    inverseLegendreMomentumDerivative_eq_inverse he hp
      (hL.contDiffAt (e.open_source.mem_nhds (e.map_target hp)))
      ((hG.contDiffAt (e.open_target.mem_nhds hp)).differentiableAt (by simp)) hpos]

/-- Strong convexity of the actual energy implies strict positivity of the actual momentum
Hessian. -/
theorem localHamiltonian_momentum_hessian_pos
    {L : E × E → ℝ} {e : OpenPartialHomeomorph (E × E) (E × (E →L[ℝ] ℝ))}
    (he : (e : (E × E) → (E × (E →L[ℝ] ℝ))) = parametricLegendre L)
    (hL : ContDiffOn ℝ ∞ L e.source) (hG : ContDiffOn ℝ ∞ e.symm e.target)
    {p : E × (E →L[ℝ] ℝ)} (hp : p ∈ e.target)
    (hpos : ∀ w : E, w ≠ 0 → 0 < verticalEnergyHessian L (e.symm p) w w)
    {q : E →L[ℝ] ℝ} (hq : q ≠ 0) :
    0 < fderiv ℝ (fderiv ℝ (localHamiltonian L e)) p (0, q) (0, q) := by
  rw [localHamiltonian_momentum_hessian_apply he hL hG hp]
  exact inverseLegendreMomentumDerivative_pos he hp
    (hL.contDiffAt (e.open_source.mem_nhds (e.map_target hp)))
    ((hG.contDiffAt (e.open_target.mem_nhds hp)).differentiableAt (by simp)) hpos hq

/-- The base-base block extracted from the actual canonical field linearization. -/
noncomputable def localHamiltonianBlockA (L : E × E → ℝ)
    (e : OpenPartialHomeomorph (E × E) (E × (E →L[ℝ] ℝ)))
    (p : E × (E →L[ℝ] ℝ)) : E →L[ℝ] (E →L[ℝ] ℝ) :=
  -(((ContinuousLinearMap.snd ℝ E (E →L[ℝ] ℝ)).comp
    (fderiv ℝ (localHamiltonianVectorField L e) p)).comp (ContinuousLinearMap.inl ℝ E _))

/-- The base-to-velocity block extracted from the actual canonical field linearization. -/
noncomputable def localHamiltonianBlockB (L : E × E → ℝ)
    (e : OpenPartialHomeomorph (E × E) (E × (E →L[ℝ] ℝ)))
    (p : E × (E →L[ℝ] ℝ)) : E →L[ℝ] E :=
  ((ContinuousLinearMap.fst ℝ E (E →L[ℝ] ℝ)).comp
    (fderiv ℝ (localHamiltonianVectorField L e) p)).comp (ContinuousLinearMap.inl ℝ E _)

/-- The momentum-to-velocity block extracted from the actual canonical field linearization. -/
noncomputable def localHamiltonianBlockC (L : E × E → ℝ)
    (e : OpenPartialHomeomorph (E × E) (E × (E →L[ℝ] ℝ)))
    (p : E × (E →L[ℝ] ℝ)) : (E →L[ℝ] ℝ) →L[ℝ] E :=
  ((ContinuousLinearMap.fst ℝ E (E →L[ℝ] ℝ)).comp
    (fderiv ℝ (localHamiltonianVectorField L e) p)).comp (ContinuousLinearMap.inr ℝ E _)

/-- The true scalar Hamiltonian Hessian is symmetric. -/
theorem localHamiltonian_hessian_symm
    {L : E × E → ℝ} {e : OpenPartialHomeomorph (E × E) (E × (E →L[ℝ] ℝ))}
    (hL : ContDiffOn ℝ ∞ L e.source) (hG : ContDiffOn ℝ ∞ e.symm e.target)
    {p : E × (E →L[ℝ] ℝ)} (hp : p ∈ e.target) (u v : E × (E →L[ℝ] ℝ)) :
    fderiv ℝ (fderiv ℝ (localHamiltonian L e)) p u v =
      fderiv ℝ (fderiv ℝ (localHamiltonian L e)) p v u :=
  (((contDiffOn_localHamiltonian hL hG).contDiffAt
    (e.open_target.mem_nhds hp)).isSymmSndFDerivAt (by simp)).eq u v

/-- The actual base block is the base-base scalar Hamiltonian Hessian. -/
theorem localHamiltonianBlockA_eq_hessian
    {L : E × E → ℝ} {e : OpenPartialHomeomorph (E × E) (E × (E →L[ℝ] ℝ))}
    (he : (e : (E × E) → (E × (E →L[ℝ] ℝ))) = parametricLegendre L)
    (hL : ContDiffOn ℝ ∞ L e.source) (hG : ContDiffOn ℝ ∞ e.symm e.target)
    {p : E × (E →L[ℝ] ℝ)} (hp : p ∈ e.target) (b w : E) :
    localHamiltonianBlockA L e p b w =
      fderiv ℝ (fderiv ℝ (localHamiltonian L e)) p (b, 0) (w, 0) := by
  rw [localHamiltonian_hessian_field_identity he hL hG hp]
  simp only [zero_apply, zero_sub]
  rfl

/-- The actual base block is symmetric under the canonical vector-covector pairing. -/
theorem localHamiltonianBlockA_symm
    {L : E × E → ℝ} {e : OpenPartialHomeomorph (E × E) (E × (E →L[ℝ] ℝ))}
    (he : (e : (E × E) → (E × (E →L[ℝ] ℝ))) = parametricLegendre L)
    (hL : ContDiffOn ℝ ∞ L e.source) (hG : ContDiffOn ℝ ∞ e.symm e.target)
    {p : E × (E →L[ℝ] ℝ)} (hp : p ∈ e.target) (b w : E) :
    localHamiltonianBlockA L e p b w = localHamiltonianBlockA L e p w b := by
  rw [localHamiltonianBlockA_eq_hessian he hL hG hp,
    localHamiltonianBlockA_eq_hessian he hL hG hp]
  exact localHamiltonian_hessian_symm hL hG hp (b, 0) (w, 0)

/-- The actual momentum-to-velocity block is the derivative of the actual inverse velocity. -/
theorem localHamiltonianBlockC_eq_inverseLegendreMomentumDerivative
    {L : E × E → ℝ} {e : OpenPartialHomeomorph (E × E) (E × (E →L[ℝ] ℝ))}
    (hL : ContDiffOn ℝ ∞ L e.source) (hG : ContDiffOn ℝ ∞ e.symm e.target)
    {p : E × (E →L[ℝ] ℝ)} (hp : p ∈ e.target) :
    localHamiltonianBlockC L e p = inverseLegendreMomentumDerivative e p := by
  ext q
  exact localHamiltonianVectorField_fderiv_fst hL hG hp (0, q)

/-- The actual momentum block is symmetric on the dual space. -/
theorem localHamiltonianBlockC_symm
    {L : E × E → ℝ} {e : OpenPartialHomeomorph (E × E) (E × (E →L[ℝ] ℝ))}
    (he : (e : (E × E) → (E × (E →L[ℝ] ℝ))) = parametricLegendre L)
    (hL : ContDiffOn ℝ ∞ L e.source) (hG : ContDiffOn ℝ ∞ e.symm e.target)
    {p : E × (E →L[ℝ] ℝ)} (hp : p ∈ e.target) (q r : E →L[ℝ] ℝ) :
    r (localHamiltonianBlockC L e p q) = q (localHamiltonianBlockC L e p r) := by
  rw [localHamiltonianBlockC_eq_inverseLegendreMomentumDerivative hL hG hp]
  rw [← localHamiltonian_momentum_hessian_apply he hL hG hp,
    ← localHamiltonian_momentum_hessian_apply he hL hG hp]
  exact localHamiltonian_hessian_symm hL hG hp (0, q) (0, r)

/-- The actual momentum block equals the inverse energy Hessian, rather than a supplied block. -/
theorem localHamiltonianBlockC_eq_inverse [FiniteDimensional ℝ E]
    {L : E × E → ℝ} {e : OpenPartialHomeomorph (E × E) (E × (E →L[ℝ] ℝ))}
    (he : (e : (E × E) → (E × (E →L[ℝ] ℝ))) = parametricLegendre L)
    (hL : ContDiffOn ℝ ∞ L e.source) (hG : ContDiffOn ℝ ∞ e.symm e.target)
    {p : E × (E →L[ℝ] ℝ)} (hp : p ∈ e.target)
    (hpos : ∀ w : E, w ≠ 0 → 0 < verticalEnergyHessian L (e.symm p) w w) :
    localHamiltonianBlockC L e p =
      ContinuousLinearMap.inverse (verticalEnergyHessian L (e.symm p)) := by
  rw [localHamiltonianBlockC_eq_inverseLegendreMomentumDerivative hL hG hp]
  exact inverseLegendreMomentumDerivative_eq_inverse he hp
    (hL.contDiffAt (e.open_source.mem_nhds (e.map_target hp)))
    ((hG.contDiffAt (e.open_target.mem_nhds hp)).differentiableAt (by simp)) hpos

/-- Strong convexity forces strict positivity of the actual momentum-to-velocity block. -/
theorem localHamiltonianBlockC_pos
    {L : E × E → ℝ} {e : OpenPartialHomeomorph (E × E) (E × (E →L[ℝ] ℝ))}
    (he : (e : (E × E) → (E × (E →L[ℝ] ℝ))) = parametricLegendre L)
    (hL : ContDiffOn ℝ ∞ L e.source) (hG : ContDiffOn ℝ ∞ e.symm e.target)
    {p : E × (E →L[ℝ] ℝ)} (hp : p ∈ e.target)
    (hpos : ∀ w : E, w ≠ 0 → 0 < verticalEnergyHessian L (e.symm p) w w)
    {q : E →L[ℝ] ℝ} (hq : q ≠ 0) : 0 < q (localHamiltonianBlockC L e p q) := by
  rw [localHamiltonianBlockC_eq_inverseLegendreMomentumDerivative hL hG hp]
  exact inverseLegendreMomentumDerivative_pos he hp
    (hL.contDiffAt (e.open_source.mem_nhds (e.map_target hp)))
    ((hG.contDiffAt (e.open_target.mem_nhds hp)).differentiableAt (by simp)) hpos hq

/-- Hessian symmetry makes the momentum-to-force block the negative dual of the
base-to-velocity block. -/
theorem localHamiltonianVectorField_mixed_block
    {L : E × E → ℝ} {e : OpenPartialHomeomorph (E × E) (E × (E →L[ℝ] ℝ))}
    (he : (e : (E × E) → (E × (E →L[ℝ] ℝ))) = parametricLegendre L)
    (hL : ContDiffOn ℝ ∞ L e.source) (hG : ContDiffOn ℝ ∞ e.symm e.target)
    {p : E × (E →L[ℝ] ℝ)} (hp : p ∈ e.target) (b : E) (q : E →L[ℝ] ℝ) :
    (fderiv ℝ (localHamiltonianVectorField L e) p (0, q)).2 b =
      -q (localHamiltonianBlockB L e p b) := by
  have h := localHamiltonian_hessian_symm hL hG hp (b, 0) (0, q)
  rw [localHamiltonian_hessian_field_identity he hL hG hp,
    localHamiltonian_hessian_field_identity he hL hG hp] at h
  simp only [map_zero, sub_zero, zero_apply, zero_sub] at h
  change _ = -q ((fderiv ℝ (localHamiltonianVectorField L e) p (b, 0)).1)
  linarith

/-- The actual derivative of the canonical field has Hamiltonian block form. The dual
transpose is covector precomposition with `B`, so no inner product identification is used. -/
theorem localHamiltonianVectorField_linearized_blocks
    {L : E × E → ℝ} {e : OpenPartialHomeomorph (E × E) (E × (E →L[ℝ] ℝ))}
    (he : (e : (E × E) → (E × (E →L[ℝ] ℝ))) = parametricLegendre L)
    (hL : ContDiffOn ℝ ∞ L e.source) (hG : ContDiffOn ℝ ∞ e.symm e.target)
    {p : E × (E →L[ℝ] ℝ)} (hp : p ∈ e.target) (b : E) (q : E →L[ℝ] ℝ) :
    fderiv ℝ (localHamiltonianVectorField L e) p (b, q) =
      (localHamiltonianBlockB L e p b + localHamiltonianBlockC L e p q,
        -localHamiltonianBlockA L e p b - q.comp (localHamiltonianBlockB L e p)) := by
  have hsplit : (b, q) = (b, 0) + (0, q) := by simp
  rw [hsplit, map_add]
  apply Prod.ext
  · rfl
  · apply ContinuousLinearMap.ext
    intro w
    change (fderiv ℝ (localHamiltonianVectorField L e) p (b, 0)).2 w +
        (fderiv ℝ (localHamiltonianVectorField L e) p (0, q)).2 w =
      -(-(fderiv ℝ (localHamiltonianVectorField L e) p (b, 0)).2 w) -
        q (localHamiltonianBlockB L e p w)
    rw [localHamiltonianVectorField_mixed_block he hL hG hp]
    ring

/-- Smooth strong convexity constructs a local Hamiltonian whose actual linearization has
positive momentum block equal to the inverse actual vertical Lagrangian Hessian. -/
theorem exists_smooth_localHamiltonian_positive_blocks [FiniteDimensional ℝ E]
    {L : E × E → ℝ} {U : Set (E × E)} (hU : IsOpen U)
    (hL : ContDiffOn ℝ ∞ L U)
    (hpos : ∀ z ∈ U, ∀ w : E, w ≠ 0 → 0 < verticalEnergyHessian L z w w)
    {z : E × E} (hz : z ∈ U) :
    ∃ e : OpenPartialHomeomorph (E × E) (E × (E →L[ℝ] ℝ)),
      (e : (E × E) → (E × (E →L[ℝ] ℝ))) = parametricLegendre L ∧
      z ∈ e.source ∧ parametricLegendre L z ∈ e.target ∧ e.source ⊆ U ∧
      ContDiffOn ℝ ∞ e.symm e.target ∧
      ContDiffOn ℝ ∞ (localHamiltonian L e) e.target ∧
      ContDiffOn ℝ ∞ (localHamiltonianVectorField L e) e.target ∧
      ∀ p ∈ e.target,
        localHamiltonianBlockC L e p =
          ContinuousLinearMap.inverse (verticalEnergyHessian L (e.symm p)) ∧
        (∀ q : E →L[ℝ] ℝ, q ≠ 0 → 0 < q (localHamiltonianBlockC L e p q)) ∧
        (∀ q r : E →L[ℝ] ℝ,
          fderiv ℝ (fderiv ℝ (localHamiltonian L e)) p (0, q) (0, r) =
            r (ContinuousLinearMap.inverse (verticalEnergyHessian L (e.symm p)) q)) := by
  obtain ⟨e, he, hzs, hzt, hsource, hG, hH, hX, _⟩ :=
    exists_smooth_localHamiltonian hU hL hpos hz
  refine ⟨e, he, hzs, hzt, hsource, hG, hH, hX, ?_⟩
  intro p hp
  have hposp := hpos (e.symm p) (hsource (e.map_target hp))
  exact ⟨localHamiltonianBlockC_eq_inverse he (hL.mono hsource) hG hp hposp,
    fun _ hq ↦ localHamiltonianBlockC_pos he (hL.mono hsource) hG hp hposp hq,
    localHamiltonian_momentum_hessian_eq_inverse he (hL.mono hsource) hG hp hposp⟩

namespace ContinuousFinslerNorm.IsSmoothStronglyConvex

variable {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [FiniteDimensional ℝ E]
  {F : ContinuousFinslerNorm E M}

/-- The genuine smooth strongly convex Finsler chart energy supplies these inverse-Hessian
and positivity conclusions for its actual locally constructed Hamiltonian. -/
theorem exists_chartHamiltonian_positive_blocks (hF : F.IsSmoothStronglyConvex)
    (x₀ : M) {z : E × E} (hz : z ∈ chartEnergyDomain x₀) :
    ∃ e : OpenPartialHomeomorph (E × E) (E × (E →L[ℝ] ℝ)),
      (e : (E × E) → (E × (E →L[ℝ] ℝ))) = parametricLegendre (F.chartEnergy x₀) ∧
      z ∈ e.source ∧ parametricLegendre (F.chartEnergy x₀) z ∈ e.target ∧
      e.source ⊆ chartEnergyDomain x₀ ∧ ContDiffOn ℝ ∞ e.symm e.target ∧
      ContDiffOn ℝ ∞ (localHamiltonian (F.chartEnergy x₀) e) e.target ∧
      ContDiffOn ℝ ∞ (localHamiltonianVectorField (F.chartEnergy x₀) e) e.target ∧
      ∀ p ∈ e.target,
        localHamiltonianBlockC (F.chartEnergy x₀) e p =
          ContinuousLinearMap.inverse (verticalEnergyHessian (F.chartEnergy x₀) (e.symm p)) ∧
        (∀ q : E →L[ℝ] ℝ, q ≠ 0 → 0 < q (localHamiltonianBlockC (F.chartEnergy x₀) e p q)) ∧
        (∀ q r : E →L[ℝ] ℝ,
          fderiv ℝ (fderiv ℝ (localHamiltonian (F.chartEnergy x₀) e)) p (0, q) (0, r) =
            r (ContinuousLinearMap.inverse
              (verticalEnergyHessian (F.chartEnergy x₀) (e.symm p)) q)) := by
  exact exists_smooth_localHamiltonian_positive_blocks (isOpen_chartEnergyDomain x₀)
    (hF.contDiffOn_chartEnergy x₀)
    (fun _ hz _ hw ↦ hF.chartEnergy_hessian_pos x₀ hz hw) hz

end ContinuousFinslerNorm.IsSmoothStronglyConvex

end OTSelector.Geometry
