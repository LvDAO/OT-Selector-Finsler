import OTSelector.Analysis.Convex.HomogeneousEnergy
import OTSelector.Analysis.Convex.Legendre.Parametric
import OTSelector.Geometry.Finsler.Hamiltonian.Basic
import OTSelector.Geometry.Finsler.Hamiltonian.Hessian
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Geometry.HamiltonianFlatBase.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Geometry.HamiltonianFlatBase`; the selected original proof blocks follow. -/
section

/-!
Conditions: Actual second derivatives and inverse vertical Hessians exist, and the base Hessian blocks vanish as explicitly stated.

Objects: Flat-base Hamiltonian derivative blocks and positivity of the inverse vertical block.

Proof detail: Differentiate the Legendre inverse identity, insert the zero mixed/base blocks, and transport positivity through the inverse.

Sources: Gerald Teschl, Section 8.3, pp. 239–241, equations (8.39)–(8.43), (8.47), and Problem 8.9 (https://www.mat.univie.ac.at/~gerald/ftp/book-ode/ode.pdf#page=250); Jiří Lebl, Section 8.3, Theorem 8.3.7, p. 38; Exercise 8.3.7, p. 45 (differentiate the inverse identity) (https://www.jirka.org/ra/realanal2.pdf#page=38); Stephen Boyd, Section 2.2.5, p. 34; Section 2.4.1, Example 2.15, p. 43; Appendix A.5.2, pp. 646–647 (https://web.stanford.edu/~boyd/cvxbook/bv_cvxbook.pdf#page=48).
Relation: Derived block specialization of the Legendre–Hamiltonian differential; no nonzero block is discarded without its hypothesis.
-/

/-!
# Actual Hamiltonian linearization when the energy has zero base Hessian blocks

The scalar energy Hessian, its genuine Legendre inverse, and positive vertical Hessian
identify the true linearized field with inverse vertical Hessian in the momentum column.
No replacement quadratic energy or prescribed Jacobi system is used.
-/

open Set Filter
open scoped Topology ContDiff

noncomputable section
namespace OTSelector.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

private theorem partial_fderiv_apply
    {L : E × E → ℝ} {D : (E × E) → E →L[ℝ] ℝ} {z : E × E}
    (hL : ContDiffAt ℝ ∞ L z) (hD : DifferentiableAt ℝ D z)
    (a : E × E) (w : E)
    (heq : (fun q ↦ D q w) =ᶠ[𝓝 z] (fun q ↦ fderiv ℝ L q a)) (u : E × E) :
    fderiv ℝ D z u w = fderiv ℝ (fderiv ℝ L) z u a := by
  have hdL := (hL.fderiv_right (m := ∞) (by simp)).differentiableAt (by simp)
  have hleft := hD.hasFDerivAt.clm_apply (hasFDerivAt_const w z)
  have hright := hdL.hasFDerivAt.clm_apply (hasFDerivAt_const a z)
  have hd := hleft.unique (hright.congr_of_eventuallyEq heq)
  have h := congrArg (fun T : (E × E) →L[ℝ] ℝ ↦ T u) hd
  simpa only [add_apply, ContinuousLinearMap.comp_apply, zero_apply,
    ContinuousLinearMap.map_zero, zero_add, ContinuousLinearMap.flip_apply] using h

/-- Zero base columns of the original scalar Hessian eliminate the actual base
force derivative and the base derivative of the actual momentum. -/
theorem energy_partials_zero_of_hessian_base_zero
    {L : E × E → ℝ} {U : Set (E × E)} (hU : IsOpen U)
    (hL : ContDiffOn ℝ ∞ L U) {z : E × E} (hz : z ∈ U)
    (hzero : ∀ b : E, fderiv ℝ (fderiv ℝ L) z (b, 0) = 0) :
    fderiv ℝ (baseEnergyDifferential L) z = 0 ∧
      ∀ b : E, fderiv ℝ (fiberLegendre L) z (b, 0) = 0 := by
  have hLa := hL.contDiffAt (hU.mem_nhds hz)
  have hb (w : E) : (fun q ↦ baseEnergyDifferential L q w) =ᶠ[𝓝 z]
      (fun q ↦ fderiv ℝ L q (w, 0)) := by
    filter_upwards [hU.mem_nhds hz] with q hq
    rw [fderiv_energy_split ((hL.contDiffAt (hU.mem_nhds hq)).differentiableAt
      (by simp))]
    simp
  have hv (w : E) : (fun q ↦ fiberLegendre L q w) =ᶠ[𝓝 z]
      (fun q ↦ fderiv ℝ L q (0, w)) := by
    filter_upwards [hU.mem_nhds hz] with q hq
    rw [fderiv_energy_split ((hL.contDiffAt (hU.mem_nhds hq)).differentiableAt
      (by simp))]
    simp
  constructor
  · apply ContinuousLinearMap.ext
    intro u
    apply ContinuousLinearMap.ext
    intro w
    rw [partial_fderiv_apply hLa
      ((contDiffAt_baseEnergyDifferential hLa).differentiableAt (by simp)) _ _ (hb w),
      (hLa.isSymmSndFDerivAt (by simp)).eq u (w, 0), hzero]
    rfl
  · intro b
    ext w
    rw [partial_fderiv_apply hLa
      ((contDiffAt_fiberLegendre hLa).differentiableAt (by simp)) _ _ (hv w), hzero]
    rfl

/-- The derivative of the genuine Hamiltonian field has only its actual positive
inverse-vertical-Hessian block when the original scalar Hessian has zero base columns. -/
theorem localHamiltonianVectorField_fderiv_of_hessian_base_zero
    [FiniteDimensional ℝ E]
    {L : E × E → ℝ} {e : OpenPartialHomeomorph (E × E) (E × (E →L[ℝ] ℝ))}
    (he : (e : (E × E) → (E × (E →L[ℝ] ℝ))) = parametricLegendre L)
    (hL : ContDiffOn ℝ ∞ L e.source) (hG : ContDiffOn ℝ ∞ e.symm e.target)
    {p : E × (E →L[ℝ] ℝ)} (hp : p ∈ e.target)
    (hzero : ∀ b : E, fderiv ℝ (fderiv ℝ L) (e.symm p) (b, 0) = 0)
    (hpos : ∀ w : E, w ≠ 0 → 0 < verticalEnergyHessian L (e.symm p) w w)
    (u : E × (E →L[ℝ] ℝ)) :
    fderiv ℝ (localHamiltonianVectorField L e) p u =
      (ContinuousLinearMap.inverse (verticalEnergyHessian L (e.symm p)) u.2, 0) := by
  have hLa := hL.contDiffAt (e.open_source.mem_nhds (e.map_target hp))
  have hGa := (hG.contDiffAt (e.open_target.mem_nhds hp)).differentiableAt (by simp)
  obtain ⟨hb, hv⟩ := energy_partials_zero_of_hessian_base_zero e.open_source hL
    (e.map_target hp) hzero
  have hcomp := (hasFDerivAt_parametricLegendre hLa).comp p hGa.hasFDerivAt
  have hid : HasFDerivAt (fun y ↦ parametricLegendre L (e.symm y))
      (ContinuousLinearMap.id ℝ (E × (E →L[ℝ] ℝ))) p := by
    apply (hasFDerivAt_id p).congr_of_eventuallyEq
    filter_upwards [e.open_target.mem_nhds hp] with y hy
    exact (congrFun he (e.symm y)).symm.trans (e.right_inv hy)
  have hId := congrArg (fun T : (E × (E →L[ℝ] ℝ)) →L[ℝ]
      (E × (E →L[ℝ] ℝ)) ↦ T u) (hcomp.unique hid)
  have hId' : fderiv ℝ (parametricLegendre L) (e.symm p)
      (fderiv ℝ e.symm p u) = u := by
    rw [parametricLegendre_fderiv_eq hLa]
    exact hId
  change fderiv ℝ (parametricLegendre L) (e.symm p)
    ((fderiv ℝ e.symm p u).1, (fderiv ℝ e.symm p u).2) = u at hId'
  rw [parametricLegendre_fderiv_apply hLa, hv, zero_add] at hId'
  have hvel : (fderiv ℝ e.symm p u).2 =
      ContinuousLinearMap.inverse (verticalEnergyHessian L (e.symm p)) u.2 := by
    let d := positive_dualMap_equiv (verticalEnergyHessian L (e.symm p)) hpos
    rw [show ContinuousLinearMap.inverse (verticalEnergyHessian L (e.symm p)) =
      d.symm.toContinuousLinearMap from ContinuousLinearMap.inverse_equiv d]
    apply d.injective
    exact (congrArg Prod.snd hId').trans (d.apply_symm_apply u.2).symm
  have hforce := ((contDiffAt_baseEnergyDifferential hLa).differentiableAt
    (by simp)).hasFDerivAt.comp p hGa.hasFDerivAt
  have hfield := hGa.hasFDerivAt.snd.prodMk hforce
  have heq := congrArg (fun T : (E × (E →L[ℝ] ℝ)) →L[ℝ]
      (E × (E →L[ℝ] ℝ)) ↦ T u) hfield.fderiv
  change fderiv ℝ (localHamiltonianVectorField L e) p u = _ at heq
  simpa only [ContinuousLinearMap.prod_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.coe_snd', hb, zero_apply, hvel] using heq

/-- Positivity of the true vertical Hessian gives positivity of its actual inverse. -/
theorem inverse_verticalEnergyHessian_pos [FiniteDimensional ℝ E]
    {L : E × E → ℝ} {z : E × E}
    (hpos : ∀ w : E, w ≠ 0 → 0 < verticalEnergyHessian L z w w)
    {p : E →L[ℝ] ℝ} (hp : p ≠ 0) :
    0 < p (ContinuousLinearMap.inverse (verticalEnergyHessian L z) p) := by
  let d := positive_dualMap_equiv (verticalEnergyHessian L z) hpos
  rw [show ContinuousLinearMap.inverse (verticalEnergyHessian L z) =
    d.symm.toContinuousLinearMap from ContinuousLinearMap.inverse_equiv d]
  have hw : d.symm p ≠ 0 := d.symm.map_eq_zero_iff.not.mpr hp
  have h := hpos (d.symm p) hw
  change 0 < d (d.symm p) (d.symm p) at h
  simpa using h

end OTSelector.Geometry

end
end
