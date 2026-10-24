import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
## Lemma skeleton

* **Conditions:** A real normed fiber and positive degree-two homogeneity; actual first/second Fréchet differentiability at nonzero velocities. Positive diagonal Hessian pairing is assumed only for invertibility; surjectivity uses finite dimension.
* **Objects:** DL(v), its scaling law, the radial identity D²L(v)(v,·)=DL(v), and a continuous linear equivalence E ≃ E* induced by a positive Hessian.
* **Proof detail:** Differentiate the positive scalar ray at r=1, differentiate the scaling identity in velocity, and apply Euler to the degree-one derivative map. A positive map has trivial kernel; equal finite dimensions give surjectivity.

## Mathematical sources

* Matias Dahl, *An brief introduction to Finsler geometry (12 July 2006)*, Section 1, Proposition 1.1, p. 3; Section 1.1, Definition 1.2 and Remarks 1.3(4), pp. 4–5.
  https://math.aalto.fi/~fdahl/finsler/finsler.pdf#page=3
* Matias Dahl, *An brief introduction to Finsler geometry (12 July 2006)*, Section 1.2, Definition 1.8, Propositions 1.9–1.10, pp. 6–8; equations (3)–(8).
  https://math.aalto.fi/~fdahl/finsler/finsler.pdf#page=6

**Relationship to the sources:** Euler and radial identities generalize the homogeneous-function calculations in Dahl. The continuous-dual packaging and finite-dimensional positive-map equivalence are local linear-algebra consequences, with no inner-product identification.
-/

/-!
# Fiber differentials of positively homogeneous energies

For a real fiber energy `L`, positive homogeneity of degree two and an actual Fréchet
derivative imply Euler's identity. Differentiating the scaling identity shows that the
actual map `v ↦ fderiv ℝ L v` is positively homogeneous of degree one away from zero.
Its actual derivative therefore satisfies `D²L(v)(v,w) = DL(v)(w)` for every `w`.
No Euler or Hessian identity is included among the hypotheses.

These differential identities do not require a finite-dimensional or inner-product
space. In finite dimensions, positive diagonal pairing makes the Hessian a continuous
linear equivalence from the fiber to its continuous dual. The final theorem identifies
that equivalence with the actual derivative of the Legendre map.

Only positive scaling is used; no reversibility or symmetry under `v ↦ -v` is required.
The energy need not be differentiable at zero. This module proves fiberwise differential
identities and invertibility of a differential, not a nonlinear Legendre inverse or
geodesic existence. Identifying `L` with a manifold Finsler energy belongs to its adapter.
-/

open Set Filter
open scoped Topology

namespace OTSelector.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Euler's identity for a positively homogeneous degree-two scalar energy. -/
theorem twoHomogeneous_euler
    {L : E → ℝ} {v : E} {D : E →L[ℝ] ℝ}
    (hhom : ∀ r : ℝ, 0 < r → L (r • v) = r ^ 2 * L v)
    (hd : HasFDerivAt L D v) : D v = 2 * L v := by
  have hline : HasDerivAt (fun r : ℝ ↦ r • v) v 1 := by
    simpa using (hasDerivAt_id (1 : ℝ)).smul_const v
  have hleft : HasDerivAt (fun r : ℝ ↦ L (r • v)) (D v) 1 := by
    simpa using! hd.comp_hasDerivAt_of_eq (1 : ℝ) hline (one_smul ℝ v).symm
  have hright : HasDerivAt (fun r : ℝ ↦ r ^ 2 * L v) (2 * L v) 1 := by
    simpa using ((hasDerivAt_id (1 : ℝ)).pow 2).mul_const (L v)
  apply hleft.unique
  apply hright.congr_of_eventuallyEq
  filter_upwards [eventually_gt_nhds (show (0 : ℝ) < 1 by norm_num)] with r hr
  exact hhom r hr

/-- Euler's identity stated using the actual Fréchet derivative. -/
theorem twoHomogeneous_fderiv_euler
    {L : E → ℝ} {v : E}
    (hhom : ∀ r : ℝ, 0 < r → L (r • v) = r ^ 2 * L v)
    (hd : DifferentiableAt ℝ L v) : fderiv ℝ L v v = 2 * L v :=
  twoHomogeneous_euler hhom hd.hasFDerivAt

/-- The actual Fréchet derivative of a degree-two energy scales with degree one. -/
theorem twoHomogeneous_fderiv_pos_smul
    {L : E → ℝ}
    (hhom : ∀ r : ℝ, 0 < r → ∀ x : E, L (r • x) = r ^ 2 * L x)
    (hd : ∀ x : E, x ≠ 0 → DifferentiableAt ℝ L x)
    {v : E} (hv : v ≠ 0) {r : ℝ} (hr : 0 < r) :
    fderiv ℝ L (r • v) = r • fderiv ℝ L v := by
  have hrv : r • v ≠ 0 := smul_ne_zero hr.ne' hv
  have hl := (hd (r • v) hrv).hasFDerivAt.comp v
    ((hasFDerivAt_id v).const_smul r)
  have heq : (fun x : E ↦ L (r • x)) = (fun x : E ↦ r ^ 2 * L x) :=
    funext (hhom r hr)
  have hh := (hd v hv).hasFDerivAt.const_mul (r ^ 2)
  have hD := hl.unique (by simpa only [Function.comp_def, heq] using hh)
  ext w
  have hw := congrArg (fun T : E →L[ℝ] ℝ ↦ T w) hD
  simp only [ContinuousLinearMap.comp_apply, smul_apply,
    ContinuousLinearMap.id_apply, map_smul, smul_eq_mul] at hw ⊢
  nlinarith [hr]

/-- The true derivative of the Legendre map sends the radial vector to the differential
of the energy: `D²L(v)(v,w) = DL(v)(w)` for every `w`. -/
theorem twoHomogeneous_hessian_radial
    {L : E → ℝ}
    (hhom : ∀ r : ℝ, 0 < r → ∀ x : E, L (r • x) = r ^ 2 * L x)
    (hd : ∀ x : E, x ≠ 0 → DifferentiableAt ℝ L x)
    {v : E} (hv : v ≠ 0) {H : E →L[ℝ] (E →L[ℝ] ℝ)}
    (hH : HasFDerivAt (fderiv ℝ L) H v) : H v = fderiv ℝ L v := by
  have hline : HasDerivAt (fun r : ℝ ↦ r • v) v 1 := by
    simpa using (hasDerivAt_id (1 : ℝ)).smul_const v
  have hleft : HasDerivAt (fun r : ℝ ↦ fderiv ℝ L (r • v)) (H v) 1 := by
    simpa using! hH.comp_hasDerivAt_of_eq (1 : ℝ) hline (one_smul ℝ v).symm
  have hright : HasDerivAt (fun r : ℝ ↦ r • fderiv ℝ L v) (fderiv ℝ L v) 1 := by
    simpa using (hasDerivAt_id (1 : ℝ)).smul_const (fderiv ℝ L v)
  apply hleft.unique
  apply hright.congr_of_eventuallyEq
  filter_upwards [eventually_gt_nhds (show (0 : ℝ) < 1 by norm_num)] with r hr
  exact twoHomogeneous_fderiv_pos_smul hhom hd hv hr

/-- The radial Hessian identity expressed entirely with actual Fréchet derivatives. -/
theorem twoHomogeneous_fderiv2_radial
    {L : E → ℝ}
    (hhom : ∀ r : ℝ, 0 < r → ∀ x : E, L (r • x) = r ^ 2 * L x)
    (hd : ∀ x : E, x ≠ 0 → DifferentiableAt ℝ L x)
    {v : E} (hv : v ≠ 0) (h2 : DifferentiableAt ℝ (fderiv ℝ L) v) :
    fderiv ℝ (fderiv ℝ L) v v = fderiv ℝ L v :=
  twoHomogeneous_hessian_radial hhom hd hv h2.hasFDerivAt

/-- Positive diagonal pairing forces a linear map into the continuous dual to be injective. -/
theorem positive_dualMap_injective
    {H : E →L[ℝ] (E →L[ℝ] ℝ)}
    (hpos : ∀ w : E, w ≠ 0 → 0 < H w w) : Function.Injective H := by
  apply (LinearMap.ker_eq_bot).mp
  apply LinearMap.ker_eq_bot'.mpr
  intro w hw
  by_contra hne
  have hp := hpos w hne
  change H w = 0 at hw
  rw [hw] at hp
  simp at hp

variable [FiniteDimensional ℝ E]

/-- In finite dimensions a positive map to the continuous dual is bijective. -/
theorem positive_dualMap_bijective
    {H : E →L[ℝ] (E →L[ℝ] ℝ)}
    (hpos : ∀ w : E, w ≠ 0 → 0 < H w w) : Function.Bijective H := by
  have hi := positive_dualMap_injective hpos
  have hdim : Module.finrank ℝ E = Module.finrank ℝ (E →L[ℝ] ℝ) := by
    rw [← (LinearMap.toContinuousLinearMap :
      (E →ₗ[ℝ] ℝ) ≃ₗ[ℝ] (E →L[ℝ] ℝ)).finrank_eq]
    exact (Subspace.dual_finrank_eq (K := ℝ) (V := E)).symm
  exact ⟨hi, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp hi⟩

/-- Strong positivity turns the actual Legendre differential into a continuous linear
equivalence between the fiber and its continuous dual. -/
noncomputable def positive_dualMap_equiv
    (H : E →L[ℝ] (E →L[ℝ] ℝ))
    (hpos : ∀ w : E, w ≠ 0 → 0 < H w w) : E ≃L[ℝ] (E →L[ℝ] ℝ) :=
  (LinearEquiv.ofBijective H.toLinearMap (positive_dualMap_bijective hpos)).toContinuousLinearEquiv

@[simp]
theorem positive_dualMap_equiv_toContinuousLinearMap
    (H : E →L[ℝ] (E →L[ℝ] ℝ))
    (hpos : ∀ w : E, w ≠ 0 → 0 < H w w) :
    (positive_dualMap_equiv H hpos).toContinuousLinearMap = H := rfl

/-- At a point with positive actual Hessian, the Legendre map has a continuous linear
equivalence as its derivative. This asserts no global or local nonlinear inverse theorem. -/
theorem exists_legendreDifferential_equiv
    {L : E → ℝ} {v : E} (h2 : DifferentiableAt ℝ (fderiv ℝ L) v)
    (hpos : ∀ w : E, w ≠ 0 → 0 < fderiv ℝ (fderiv ℝ L) v w w) :
    ∃ e : E ≃L[ℝ] (E →L[ℝ] ℝ),
      HasFDerivAt (fderiv ℝ L) e.toContinuousLinearMap v := by
  exact ⟨positive_dualMap_equiv _ hpos, h2.hasFDerivAt⟩

end OTSelector.Geometry
