import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import OTSelector.Analysis.Convex.HomogeneousEnergy
import OTSelector.Analysis.Convex.Legendre.Parametric
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Geometry.GraphLegendre.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Geometry.GraphLegendre`; the selected original proof blocks follow. -/
section

/-!
Conditions: Arbitrary base and fiber spaces, a true partial Legendre inverse and the actual vertical Hessian identities and positivity.

Objects: Inverse vertical Hessian and the differential of the partial Hamiltonian with unequal base/fiber dimensions.

Proof detail: Differentiate both actual inverse identities and H=p(v)−L; the velocity variation cancels, leaving δp(v)−Dbase L.

Sources: Gerald Teschl, Section 8.3, pp. 239–241, equations (8.39)–(8.43), (8.47), and Problem 8.9 (https://www.mat.univie.ac.at/~gerald/ftp/book-ode/ode.pdf#page=250); Jiří Lebl, Section 8.3, Theorem 8.3.7, p. 38; Exercise 8.3.7, p. 45 (differentiate the inverse identity) (https://www.jirka.org/ra/realanal2.pdf#page=38); Jiří Lebl, Section 8.6, Proposition 8.6.2, pp. 60–61 (equality of mixed second partial derivatives) (https://www.jirka.org/ra/realanal2.pdf#page=60).
Relation: General partial-Legendre calculus; the book’s standard equal-dimensional finite-dimensional formulation is supporting mathematics, not the identical statement.
-/

/-!
# Partial Legendre calculus with different base and fiber dimensions

For a genuine scalar Lagrangian on `B × E`, the base coordinate is retained while only
velocity is Legendre transformed. The actual local inverse determines the inverse velocity
and its momentum derivative. Differentiating the inverse identity proves that this block is
the inverse actual vertical Hessian, with positivity and symmetry under their proved scalar
counterparts. The actual partial Hamiltonian has differential `δp(v) - D_base L(δbase)`.

The inverse itself is constructed by `exists_smooth_parametricLegendre_local_inverse`;
consumer lemmas here keep that exact inverse identity. No inner product, separate Hessian,
nonlinear inverse oracle, or equality of base and fiber dimensions is required.
-/

open Set Filter
open scoped Topology ContDiff

namespace OTSelector.Geometry.GraphLegendre

variable {B E : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The true vertical Hessian of the original scalar Lagrangian. -/
noncomputable def verticalHessian (L : B × E → ℝ) (z : B × E) :
    E →L[ℝ] (E →L[ℝ] ℝ) :=
  fderiv ℝ (fderiv ℝ (fun v ↦ L (z.1, v))) z.2

/-- The momentum derivative of the actual inverse velocity. -/
noncomputable def inverseMomentumDerivative
    (e : OpenPartialHomeomorph (B × E) (B × (E →L[ℝ] ℝ)))
    (p : B × (E →L[ℝ] ℝ)) : (E →L[ℝ] ℝ) →L[ℝ] E :=
  ((ContinuousLinearMap.snd ℝ B E).comp (fderiv ℝ e.symm p)).comp
    (ContinuousLinearMap.inr ℝ B (E →L[ℝ] ℝ))

omit [NormedSpace ℝ B] in
/-- The actual inverse preserves base coordinates and recovers the prescribed momentum. -/
theorem inverse_components
    {L : B × E → ℝ} {e : OpenPartialHomeomorph (B × E) (B × (E →L[ℝ] ℝ))}
    (he : (e : (B × E) → (B × (E →L[ℝ] ℝ))) = parametricLegendre L)
    {p : B × (E →L[ℝ] ℝ)} (hp : p ∈ e.target) :
    (e.symm p).1 = p.1 ∧ fiberLegendre L (e.symm p) = p.2 := by
  have h := e.right_inv hp
  rw [he] at h
  exact ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩

/-- The actual inverse derivative has identity base row. -/
theorem inverse_derivative_fst
    {L : B × E → ℝ} {e : OpenPartialHomeomorph (B × E) (B × (E →L[ℝ] ℝ))}
    (he : (e : (B × E) → (B × (E →L[ℝ] ℝ))) = parametricLegendre L)
    {p : B × (E →L[ℝ] ℝ)} (hp : p ∈ e.target)
    {G : (B × (E →L[ℝ] ℝ)) →L[ℝ] (B × E)} (hG : HasFDerivAt e.symm G p) :
    (ContinuousLinearMap.fst ℝ B E).comp G = ContinuousLinearMap.fst ℝ B (E →L[ℝ] ℝ) := by
  apply hG.fst.unique
  apply hasFDerivAt_fst.congr_of_eventuallyEq
  filter_upwards [e.open_target.mem_nhds hp] with q hq
  exact (inverse_components he hq).1

/-- Differentiating the inverse identity recovers every vertical momentum variation. -/
theorem verticalHessian_inverseMomentumDerivative
    {L : B × E → ℝ} {e : OpenPartialHomeomorph (B × E) (B × (E →L[ℝ] ℝ))}
    (he : (e : (B × E) → (B × (E →L[ℝ] ℝ))) = parametricLegendre L)
    {p : B × (E →L[ℝ] ℝ)} (hp : p ∈ e.target)
    (hL : ContDiffAt ℝ ∞ L (e.symm p)) (hG : DifferentiableAt ℝ e.symm p)
    (q : E →L[ℝ] ℝ) :
    verticalHessian L (e.symm p) (inverseMomentumDerivative e p q) = q := by
  have hcomp := (hasFDerivAt_parametricLegendre hL).comp p hG.hasFDerivAt
  have hid : HasFDerivAt (fun y ↦ parametricLegendre L (e.symm y))
      (ContinuousLinearMap.id ℝ (B × (E →L[ℝ] ℝ))) p := by
    apply (hasFDerivAt_id p).congr_of_eventuallyEq
    filter_upwards [e.open_target.mem_nhds hp] with y hy
    exact (congrFun he (e.symm y)).symm.trans (e.right_inv hy)
  have hId := congrArg (fun T : (B × (E →L[ℝ] ℝ)) →L[ℝ]
      (B × (E →L[ℝ] ℝ)) ↦ T (0, q)) (hcomp.unique hid)
  have hfst : (fderiv ℝ e.symm p (0, q)).1 = 0 :=
    congrArg (fun T : (B × (E →L[ℝ] ℝ)) →L[ℝ] B ↦ T (0, q))
      (inverse_derivative_fst he hp hG.hasFDerivAt)
  have hpair : fderiv ℝ e.symm p (0, q) =
      (0, inverseMomentumDerivative e p q) := Prod.ext hfst rfl
  have hId' : fderiv ℝ (parametricLegendre L) (e.symm p)
      (fderiv ℝ e.symm p (0, q)) = (0, q) := by
    rw [parametricLegendre_fderiv_eq hL]
    exact hId
  rw [hpair, parametricLegendre_fderiv_apply hL] at hId'
  simpa only [Prod.mk_zero_zero, map_zero, zero_add, verticalHessian] using
    congrArg Prod.snd hId'

/-- Positivity of the actual vertical Hessian implies positivity of the inverse block. -/
theorem inverseMomentumDerivative_pos
    {L : B × E → ℝ} {e : OpenPartialHomeomorph (B × E) (B × (E →L[ℝ] ℝ))}
    (he : (e : (B × E) → (B × (E →L[ℝ] ℝ))) = parametricLegendre L)
    {p : B × (E →L[ℝ] ℝ)} (hp : p ∈ e.target)
    (hL : ContDiffAt ℝ ∞ L (e.symm p)) (hG : DifferentiableAt ℝ e.symm p)
    (hpos : ∀ w : E, w ≠ 0 → 0 < verticalHessian L (e.symm p) w w)
    {q : E →L[ℝ] ℝ} (hq : q ≠ 0) :
    0 < q (inverseMomentumDerivative e p q) := by
  have hinv := verticalHessian_inverseMomentumDerivative he hp hL hG q
  have hw : inverseMomentumDerivative e p q ≠ 0 := by
    intro hzero
    apply hq
    rw [← hinv, hzero, map_zero]
  calc
    0 < verticalHessian L (e.symm p)
        (inverseMomentumDerivative e p q) (inverseMomentumDerivative e p q) := hpos _ hw
    _ = q (inverseMomentumDerivative e p q) :=
      congrArg (fun r : E →L[ℝ] ℝ ↦ r (inverseMomentumDerivative e p q)) hinv

/-- The momentum derivative of the inverse equals the inverse actual fiber Hessian. -/
theorem inverseMomentumDerivative_eq_inverse [FiniteDimensional ℝ E]
    {L : B × E → ℝ} {e : OpenPartialHomeomorph (B × E) (B × (E →L[ℝ] ℝ))}
    (he : (e : (B × E) → (B × (E →L[ℝ] ℝ))) = parametricLegendre L)
    {p : B × (E →L[ℝ] ℝ)} (hp : p ∈ e.target)
    (hL : ContDiffAt ℝ ∞ L (e.symm p)) (hG : DifferentiableAt ℝ e.symm p)
    (hpos : ∀ w : E, w ≠ 0 → 0 < verticalHessian L (e.symm p) w w) :
    inverseMomentumDerivative e p = ContinuousLinearMap.inverse (verticalHessian L (e.symm p)) := by
  let d := positive_dualMap_equiv (verticalHessian L (e.symm p)) hpos
  have hd : ContinuousLinearMap.inverse (verticalHessian L (e.symm p)) =
      d.symm.toContinuousLinearMap := ContinuousLinearMap.inverse_equiv d
  rw [hd]
  apply ContinuousLinearMap.ext
  intro q
  apply d.injective
  change d (inverseMomentumDerivative e p q) = d (d.symm q)
  rw [d.apply_symm_apply]
  exact verticalHessian_inverseMomentumDerivative he hp hL hG q

/-- Symmetry is inherited from the actual scalar vertical Hessian. -/
theorem inverseMomentumDerivative_symm
    {L : B × E → ℝ} {e : OpenPartialHomeomorph (B × E) (B × (E →L[ℝ] ℝ))}
    (he : (e : (B × E) → (B × (E →L[ℝ] ℝ))) = parametricLegendre L)
    {p : B × (E →L[ℝ] ℝ)} (hp : p ∈ e.target)
    (hL : ContDiffAt ℝ ∞ L (e.symm p)) (hG : DifferentiableAt ℝ e.symm p)
    (q r : E →L[ℝ] ℝ) :
    r (inverseMomentumDerivative e p q) = q (inverseMomentumDerivative e p r) := by
  have hfiber : ContDiffAt ℝ ∞ (fun v ↦ L ((e.symm p).1, v)) (e.symm p).2 := by
    simpa only [Function.comp_def] using!
      hL.comp (e.symm p).2 (contDiffAt_const.prodMk
        (contDiffAt_id (x := (e.symm p).2)))
  have hs := hfiber.isSymmSndFDerivAt (by simp)
    (inverseMomentumDerivative e p r) (inverseMomentumDerivative e p q)
  change verticalHessian L (e.symm p) _ _ = verticalHessian L (e.symm p) _ _ at hs
  rwa [verticalHessian_inverseMomentumDerivative he hp hL hG,
    verticalHessian_inverseMomentumDerivative he hp hL hG] at hs

/-- The base differential of the original scalar Lagrangian. -/
noncomputable def baseDifferential (L : B × E → ℝ) (z : B × E) : B →L[ℝ] ℝ :=
  fderiv ℝ (fun x ↦ L (x, z.2)) z.1

/-- The actual partial Legendre transform, retaining every base parameter. -/
noncomputable def hamiltonian (L : B × E → ℝ)
    (e : OpenPartialHomeomorph (B × E) (B × (E →L[ℝ] ℝ)))
    (p : B × (E →L[ℝ] ℝ)) : ℝ :=
  p.2 ((e.symm p).2) - L (e.symm p)

/-- Joint smoothness of the actual base differential. -/
theorem contDiffAt_baseDifferential {L : B × E → ℝ} {z : B × E}
    (hL : ContDiffAt ℝ ∞ L z) : ContDiffAt ℝ ∞ (baseDifferential L) z := by
  have h : ContDiffAt ℝ ∞ (fun p : (B × E) × B ↦ L (p.2, p.1.2)) (z, z.1) :=
    hL.comp (z, z.1) (contDiffAt_snd.prodMk contDiffAt_fst.snd)
  exact h.fderiv contDiffAt_fst (by simp)

/-- The original scalar differential splits into base and velocity components. -/
theorem fderiv_split {L : B × E → ℝ} {z : B × E}
    (hL : DifferentiableAt ℝ L z) (b : B) (w : E) :
    fderiv ℝ L z (b, w) = baseDifferential L z b + fiberLegendre L z w := by
  have hl := hL.hasFDerivAt.comp z.1 (hasFDerivAt_prodMk_left (𝕜 := ℝ) z.1 z.2)
  have hr := hL.hasFDerivAt.comp z.2 (hasFDerivAt_prodMk_right (𝕜 := ℝ) z.1 z.2)
  have hsplit : (b, w) = (b, 0) + (0, w) := by simp
  rw [hsplit, map_add]
  congr 1
  · exact (congrArg (fun T : B →L[ℝ] ℝ ↦ T b) hl.fderiv).symm
  · exact (congrArg (fun T : E →L[ℝ] ℝ ↦ T w) hr.fderiv).symm

/-- All inverse-velocity derivative terms cancel in the actual partial Hamiltonian. -/
theorem hasFDerivAt_hamiltonian
    {L : B × E → ℝ} {e : OpenPartialHomeomorph (B × E) (B × (E →L[ℝ] ℝ))}
    (he : (e : (B × E) → (B × (E →L[ℝ] ℝ))) = parametricLegendre L)
    {p : B × (E →L[ℝ] ℝ)} (hp : p ∈ e.target)
    (hL : DifferentiableAt ℝ L (e.symm p))
    {G : (B × (E →L[ℝ] ℝ)) →L[ℝ] (B × E)} (hG : HasFDerivAt e.symm G p) :
    HasFDerivAt (hamiltonian L e)
      ((ContinuousLinearMap.snd ℝ B (E →L[ℝ] ℝ)).flip (e.symm p).2 -
        (baseDifferential L (e.symm p)).comp
          (ContinuousLinearMap.fst ℝ B (E →L[ℝ] ℝ))) p := by
  have heval := (hasFDerivAt_snd (𝕜 := ℝ) (p := p)).clm_apply hG.snd
  have hraw := heval.sub (hL.hasFDerivAt.comp p hG)
  apply hraw.congr_fderiv
  apply ContinuousLinearMap.ext
  intro dq
  change p.2 (G dq).2 + dq.2 (e.symm p).2 - fderiv ℝ L (e.symm p) (G dq) =
    dq.2 (e.symm p).2 - baseDifferential L (e.symm p) dq.1
  have hfst : (G dq).1 = dq.1 :=
    congrArg (fun T : (B × (E →L[ℝ] ℝ)) →L[ℝ] B ↦ T dq)
      (inverse_derivative_fst he hp hG)
  have hs := fderiv_split hL (G dq).1 (G dq).2
  change fderiv ℝ L (e.symm p) (G dq) = _ at hs
  rw [hs, (inverse_components he hp).2, hfst]
  ring

/-- Pointwise Fréchet differential of the actual partial Hamiltonian. -/
theorem hamiltonian_fderiv_apply
    {L : B × E → ℝ} {e : OpenPartialHomeomorph (B × E) (B × (E →L[ℝ] ℝ))}
    (he : (e : (B × E) → (B × (E →L[ℝ] ℝ))) = parametricLegendre L)
    {p : B × (E →L[ℝ] ℝ)} (hp : p ∈ e.target)
    (hL : DifferentiableAt ℝ L (e.symm p)) (hG : DifferentiableAt ℝ e.symm p)
    (dq : B × (E →L[ℝ] ℝ)) :
    fderiv ℝ (hamiltonian L e) p dq =
      dq.2 (e.symm p).2 - baseDifferential L (e.symm p) dq.1 := by
  rw [(hasFDerivAt_hamiltonian he hp hL hG.hasFDerivAt).fderiv]
  rfl

/-- The actual partial Hamiltonian is jointly smooth on the inverse target. -/
theorem contDiffOn_hamiltonian
    {L : B × E → ℝ} {e : OpenPartialHomeomorph (B × E) (B × (E →L[ℝ] ℝ))}
    (hL : ContDiffOn ℝ ∞ L e.source) (hG : ContDiffOn ℝ ∞ e.symm e.target) :
    ContDiffOn ℝ ∞ (hamiltonian L e) e.target := by
  exact (contDiffOn_snd.clm_apply hG.snd).sub (hL.comp hG (fun _ hp ↦ e.map_target hp))

/-- The actual momentum Hessian is the canonical pairing with inverse-velocity derivative. -/
theorem hamiltonian_momentum_hessian_apply
    {L : B × E → ℝ} {e : OpenPartialHomeomorph (B × E) (B × (E →L[ℝ] ℝ))}
    (he : (e : (B × E) → (B × (E →L[ℝ] ℝ))) = parametricLegendre L)
    (hL : ContDiffOn ℝ ∞ L e.source) (hG : ContDiffOn ℝ ∞ e.symm e.target)
    {p : B × (E →L[ℝ] ℝ)} (hp : p ∈ e.target) (q r : E →L[ℝ] ℝ) :
    fderiv ℝ (fderiv ℝ (hamiltonian L e)) p (0, q) (0, r) =
      r (inverseMomentumDerivative e p q) := by
  have hH := (contDiffOn_hamiltonian hL hG).contDiffAt (e.open_target.mem_nhds hp)
  have hDH := (hH.fderiv_right (m := ∞) (by simp)).differentiableAt (by simp)
  have hGi := (hG.contDiffAt (e.open_target.mem_nhds hp)).differentiableAt (by simp)
  have hleft := hDH.hasFDerivAt.clm_apply (hasFDerivAt_const (0, r) p)
  have hright := r.hasFDerivAt.comp p hGi.hasFDerivAt.snd
  have heq : (fun z ↦ fderiv ℝ (hamiltonian L e) z (0, r)) =ᶠ[𝓝 p]
      (fun z ↦ r (e.symm z).2) := by
    filter_upwards [e.open_target.mem_nhds hp] with z hz
    rw [hamiltonian_fderiv_apply he hz
      ((hL.contDiffAt (e.open_source.mem_nhds (e.map_target hz))).differentiableAt
        (by simp))
      ((hG.contDiffAt (e.open_target.mem_nhds hz)).differentiableAt (by simp))]
    simp
  have hd := hleft.unique (hright.congr_of_eventuallyEq heq)
  have h := congrArg (fun T : (B × (E →L[ℝ] ℝ)) →L[ℝ] ℝ ↦ T (0, q)) hd
  simpa [inverseMomentumDerivative] using h

end OTSelector.Geometry.GraphLegendre

end
