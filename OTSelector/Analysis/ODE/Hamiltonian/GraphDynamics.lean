import Mathlib.Analysis.Calculus.Deriv.Prod
import OTSelector.Analysis.Convex.HomogeneousEnergy
import OTSelector.Analysis.Convex.Legendre.Graph
import OTSelector.Analysis.Convex.Legendre.Parametric
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Geometry.GraphHamiltonianDynamics.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Geometry.GraphHamiltonianDynamics`; the selected original proof blocks follow. -/
section

/-!
Conditions: An actual graph Lagrangian L((t,x),v), a genuine partial Legendre inverse and actual second derivatives with positive vertical Hessian.

Objects: Actual partial Hamiltonian derivative/Hessian blocks and the nonautonomous Euler–Lagrange phase equation.

Proof detail: Differentiate the partial inverse identity, calculate H=p(v)−L, derive the Schur blocks and insert the true Euler–Lagrange equation.

Sources: Gerald Teschl, Section 8.3, pp. 239–241, equations (8.39)–(8.43), (8.47), and Problem 8.9 (https://www.mat.univie.ac.at/~gerald/ftp/book-ode/ode.pdf#page=250); Jiří Lebl, Section 8.3, Theorem 8.3.7, p. 38; Exercise 8.3.7, p. 45 (differentiate the inverse identity) (https://www.jirka.org/ra/realanal2.pdf#page=38); Jiří Lebl, Section 8.6, Proposition 8.6.2, pp. 60–61 (equality of mixed second partial derivatives) (https://www.jirka.org/ra/realanal2.pdf#page=60); Stephen Boyd, Section 2.2.5, p. 34; Section 2.4.1, Example 2.15, p. 43; Appendix A.5.2, pp. 646–647 (https://web.stanford.edu/~boyd/cvxbook/bv_cvxbook.pdf#page=48).
Relation: Local graph/nonautonomous partial-Legendre generalization; every block is calculated from actual derivatives.
-/

/-!
# Actual nonautonomous graph Hamiltonian fields

Time is retained as a base parameter of the partial Legendre transform. The field on
position and momentum is the actual inverse velocity paired with the original position
partial of the Lagrangian. Its fixed-time derivative has canonical Hamiltonian blocks,
extracted from that derivative, with symmetric A/C and C equal to the inverse actual
vertical Hessian. No ambient row deletion or independent coefficient choice is involved.
-/

open Set Filter
open scoped Topology ContDiff

namespace OTSelector.Geometry.GraphHamiltonian

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The actual position partial, with the time coordinate held fixed. -/
noncomputable def positionDifferential (L : (ℝ × E) × E → ℝ) (z : (ℝ × E) × E) :
    E →L[ℝ] ℝ :=
  (GraphLegendre.baseDifferential L z).comp (ContinuousLinearMap.inr ℝ ℝ E)

/-- The actual nonautonomous field in position-momentum variables. -/
noncomputable def field (L : (ℝ × E) × E → ℝ)
    (e : OpenPartialHomeomorph ((ℝ × E) × E) ((ℝ × E) × (E →L[ℝ] ℝ)))
    (t : ℝ) (p : E × (E →L[ℝ] ℝ)) : E × (E →L[ℝ] ℝ) :=
  ((e.symm ((t, p.1), p.2)).2, positionDifferential L (e.symm ((t, p.1), p.2)))

/-- The actual scalar partial Hamiltonian at a fixed time. -/
noncomputable def hamiltonian (L : (ℝ × E) × E → ℝ)
    (e : OpenPartialHomeomorph ((ℝ × E) × E) ((ℝ × E) × (E →L[ℝ] ℝ)))
    (t : ℝ) (p : E × (E →L[ℝ] ℝ)) : ℝ :=
  GraphLegendre.hamiltonian L e ((t, p.1), p.2)

/-- Joint smoothness of the genuine position differential. -/
theorem contDiffAt_positionDifferential {L : (ℝ × E) × E → ℝ} {z : (ℝ × E) × E}
    (hL : ContDiffAt ℝ ∞ L z) : ContDiffAt ℝ ∞ (positionDifferential L) z :=
  (GraphLegendre.contDiffAt_baseDifferential hL).clm_comp contDiffAt_const

/-- The actual field is jointly smooth in time, position and momentum on the same target. -/
theorem contDiffOn_field
    {L : (ℝ × E) × E → ℝ}
    {e : OpenPartialHomeomorph ((ℝ × E) × E) ((ℝ × E) × (E →L[ℝ] ℝ))}
    (hL : ContDiffOn ℝ ∞ L e.source) (hG : ContDiffOn ℝ ∞ e.symm e.target) :
    ContDiffOn ℝ ∞ (fun p : (ℝ × E) × (E →L[ℝ] ℝ) ↦ field L e p.1.1 (p.1.2, p.2))
      e.target := by
  intro p hp
  have hGa := hG.contDiffAt (e.open_target.mem_nhds hp)
  have hLa := hL.contDiffAt (e.open_source.mem_nhds (e.map_target hp))
  exact (hGa.snd.prodMk ((contDiffAt_positionDifferential hLa).comp p hGa)).contDiffWithinAt

private theorem contDiffAt_field
    {L : (ℝ × E) × E → ℝ}
    {e : OpenPartialHomeomorph ((ℝ × E) × E) ((ℝ × E) × (E →L[ℝ] ℝ))}
    (hL : ContDiffOn ℝ ∞ L e.source) (hG : ContDiffOn ℝ ∞ e.symm e.target)
    {t : ℝ} {p : E × (E →L[ℝ] ℝ)} (hp : ((t, p.1), p.2) ∈ e.target) :
    ContDiffAt ℝ ∞ (field L e t) p := by
  have h := (contDiffOn_field hL hG).contDiffAt (e.open_target.mem_nhds hp)
  exact h.comp p ((contDiffAt_const.prodMk contDiffAt_fst).prodMk contDiffAt_snd)

private theorem contDiffAt_hamiltonian
    {L : (ℝ × E) × E → ℝ}
    {e : OpenPartialHomeomorph ((ℝ × E) × E) ((ℝ × E) × (E →L[ℝ] ℝ))}
    (hL : ContDiffOn ℝ ∞ L e.source) (hG : ContDiffOn ℝ ∞ e.symm e.target)
    {t : ℝ} {p : E × (E →L[ℝ] ℝ)} (hp : ((t, p.1), p.2) ∈ e.target) :
    ContDiffAt ℝ ∞ (hamiltonian L e t) p := by
  have h := (GraphLegendre.contDiffOn_hamiltonian hL hG).contDiffAt
    (e.open_target.mem_nhds hp)
  exact h.comp p ((contDiffAt_const.prodMk contDiffAt_fst).prodMk contDiffAt_snd)

/-- The true fixed-time scalar differential is canonical evaluation against the field. -/
theorem hamiltonian_fderiv_apply
    {L : (ℝ × E) × E → ℝ}
    {e : OpenPartialHomeomorph ((ℝ × E) × E) ((ℝ × E) × (E →L[ℝ] ℝ))}
    (he : (e : ((ℝ × E) × E) → ((ℝ × E) × (E →L[ℝ] ℝ))) = parametricLegendre L)
    (hL : ContDiffOn ℝ ∞ L e.source) (hG : ContDiffOn ℝ ∞ e.symm e.target)
    {t : ℝ} {p : E × (E →L[ℝ] ℝ)} (hp : ((t, p.1), p.2) ∈ e.target)
    (u : E × (E →L[ℝ] ℝ)) :
    fderiv ℝ (hamiltonian L e t) p u =
      u.2 (field L e t p).1 - (field L e t p).2 u.1 := by
  have hd := GraphLegendre.hasFDerivAt_hamiltonian he hp
    ((hL.contDiffAt (e.open_source.mem_nhds (e.map_target hp))).differentiableAt (by simp))
    ((hG.contDiffAt (e.open_target.mem_nhds hp)).differentiableAt (by simp)).hasFDerivAt
  have hi := ((hasFDerivAt_const (𝕜 := ℝ) t p).prodMk hasFDerivAt_fst).prodMk
    hasFDerivAt_snd
  have h := (hd.comp p hi).fderiv
  exact congrArg (fun D : (E × (E →L[ℝ] ℝ)) →L[ℝ] ℝ ↦ D u) h

/-- Differentiating the actual canonical identity identifies the true scalar Hessian. -/
theorem hessian_field_identity
    {L : (ℝ × E) × E → ℝ}
    {e : OpenPartialHomeomorph ((ℝ × E) × E) ((ℝ × E) × (E →L[ℝ] ℝ))}
    (he : (e : ((ℝ × E) × E) → ((ℝ × E) × (E →L[ℝ] ℝ))) = parametricLegendre L)
    (hL : ContDiffOn ℝ ∞ L e.source) (hG : ContDiffOn ℝ ∞ e.symm e.target)
    {t : ℝ} {p : E × (E →L[ℝ] ℝ)} (hp : ((t, p.1), p.2) ∈ e.target)
    (u v : E × (E →L[ℝ] ℝ)) :
    fderiv ℝ (fderiv ℝ (hamiltonian L e t)) p u v =
      v.2 (fderiv ℝ (field L e t) p u).1 -
        (fderiv ℝ (field L e t) p u).2 v.1 := by
  have hDH := ((contDiffAt_hamiltonian hL hG hp).fderiv_right
    (m := ∞) (by simp)).differentiableAt (by simp)
  have hX := (contDiffAt_field hL hG hp).differentiableAt (by simp)
  have hleft := hDH.hasFDerivAt.clm_apply (hasFDerivAt_const v p)
  have hright := (v.2.hasFDerivAt.comp p hX.hasFDerivAt.fst).sub
    (hX.hasFDerivAt.snd.clm_apply (hasFDerivAt_const v.1 p))
  have hn : ∀ᶠ q : E × (E →L[ℝ] ℝ) in 𝓝 p, ((t, q.1), q.2) ∈ e.target :=
    ((continuous_const.prodMk continuous_fst).prodMk continuous_snd).continuousAt
      (e.open_target.mem_nhds hp)
  have heq : (fun q ↦ fderiv ℝ (hamiltonian L e t) q v) =ᶠ[𝓝 p]
      (fun q ↦ v.2 (field L e t q).1 - (field L e t q).2 v.1) := by
    filter_upwards [hn] with q hq
    exact hamiltonian_fderiv_apply he hL hG hq v
  have hd := hleft.unique (hright.congr_of_eventuallyEq heq)
  have h := congrArg (fun D : (E × (E →L[ℝ] ℝ)) →L[ℝ] ℝ ↦ D u) hd
  simpa only [add_apply, ContinuousLinearMap.comp_apply, zero_apply,
    ContinuousLinearMap.map_zero, zero_add, ContinuousLinearMap.flip_apply, sub_apply,
    ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd'] using h

/-- The true fixed-time scalar Hessian is symmetric. -/
theorem hessian_symm
    {L : (ℝ × E) × E → ℝ}
    {e : OpenPartialHomeomorph ((ℝ × E) × E) ((ℝ × E) × (E →L[ℝ] ℝ))}
    (hL : ContDiffOn ℝ ∞ L e.source) (hG : ContDiffOn ℝ ∞ e.symm e.target)
    {t : ℝ} {p : E × (E →L[ℝ] ℝ)} (hp : ((t, p.1), p.2) ∈ e.target)
    (u v : E × (E →L[ℝ] ℝ)) :
    fderiv ℝ (fderiv ℝ (hamiltonian L e t)) p u v =
      fderiv ℝ (fderiv ℝ (hamiltonian L e t)) p v u :=
  ((contDiffAt_hamiltonian hL hG hp).isSymmSndFDerivAt (by simp)).eq u v

/-- The actual negative position-to-force derivative. -/
noncomputable def blockA (L : (ℝ × E) × E → ℝ)
    (e : OpenPartialHomeomorph ((ℝ × E) × E) ((ℝ × E) × (E →L[ℝ] ℝ)))
    (t : ℝ) (p : E × (E →L[ℝ] ℝ)) : E →L[ℝ] (E →L[ℝ] ℝ) :=
  -(((ContinuousLinearMap.snd ℝ E (E →L[ℝ] ℝ)).comp
    (fderiv ℝ (field L e t) p)).comp (ContinuousLinearMap.inl ℝ E _))

/-- The actual position-to-velocity derivative. -/
noncomputable def blockB (L : (ℝ × E) × E → ℝ)
    (e : OpenPartialHomeomorph ((ℝ × E) × E) ((ℝ × E) × (E →L[ℝ] ℝ)))
    (t : ℝ) (p : E × (E →L[ℝ] ℝ)) : E →L[ℝ] E :=
  ((ContinuousLinearMap.fst ℝ E (E →L[ℝ] ℝ)).comp
    (fderiv ℝ (field L e t) p)).comp (ContinuousLinearMap.inl ℝ E _)

/-- The actual momentum-to-velocity derivative. -/
noncomputable def blockC (L : (ℝ × E) × E → ℝ)
    (e : OpenPartialHomeomorph ((ℝ × E) × E) ((ℝ × E) × (E →L[ℝ] ℝ)))
    (t : ℝ) (p : E × (E →L[ℝ] ℝ)) : (E →L[ℝ] ℝ) →L[ℝ] E :=
  ((ContinuousLinearMap.fst ℝ E (E →L[ℝ] ℝ)).comp
    (fderiv ℝ (field L e t) p)).comp (ContinuousLinearMap.inr ℝ E _)

/-- The true first derivative row is the derivative of the same inverse velocity. -/
theorem field_fderiv_fst
    {L : (ℝ × E) × E → ℝ}
    {e : OpenPartialHomeomorph ((ℝ × E) × E) ((ℝ × E) × (E →L[ℝ] ℝ))}
    (hL : ContDiffOn ℝ ∞ L e.source) (hG : ContDiffOn ℝ ∞ e.symm e.target)
    {t : ℝ} {p : E × (E →L[ℝ] ℝ)} (hp : ((t, p.1), p.2) ∈ e.target)
    (u : E × (E →L[ℝ] ℝ)) :
    (fderiv ℝ (field L e t) p u).1 =
      (fderiv ℝ e.symm ((t, p.1), p.2) ((0, u.1), u.2)).2 := by
  have hX := (contDiffAt_field hL hG hp).differentiableAt (by simp)
  have hGi := (hG.contDiffAt (e.open_target.mem_nhds hp)).differentiableAt (by simp)
  have hi := ((hasFDerivAt_const (𝕜 := ℝ) t p).prodMk hasFDerivAt_fst).prodMk
    hasFDerivAt_snd
  have hh := hGi.hasFDerivAt.snd.comp p hi
  have hx : HasFDerivAt (fun q ↦ (e.symm ((t, q.1), q.2)).2)
      ((ContinuousLinearMap.fst ℝ E (E →L[ℝ] ℝ)).comp
        (fderiv ℝ (field L e t) p)) p := hX.hasFDerivAt.fst
  exact congrArg (fun D : (E × (E →L[ℝ] ℝ)) →L[ℝ] E ↦ D u) (hx.unique hh)

/-- The A block is the actual fixed-time position Hessian of the scalar Hamiltonian. -/
theorem blockA_eq_hessian
    {L : (ℝ × E) × E → ℝ}
    {e : OpenPartialHomeomorph ((ℝ × E) × E) ((ℝ × E) × (E →L[ℝ] ℝ))}
    (he : (e : ((ℝ × E) × E) → ((ℝ × E) × (E →L[ℝ] ℝ))) = parametricLegendre L)
    (hL : ContDiffOn ℝ ∞ L e.source) (hG : ContDiffOn ℝ ∞ e.symm e.target)
    {t : ℝ} {p : E × (E →L[ℝ] ℝ)} (hp : ((t, p.1), p.2) ∈ e.target)
    (b w : E) :
    blockA L e t p b w =
      fderiv ℝ (fderiv ℝ (hamiltonian L e t)) p (b, 0) (w, 0) := by
  rw [hessian_field_identity he hL hG hp]
  simp only [zero_apply, zero_sub]
  rfl

/-- The actual position block is symmetric under canonical covector evaluation. -/
theorem blockA_symm
    {L : (ℝ × E) × E → ℝ}
    {e : OpenPartialHomeomorph ((ℝ × E) × E) ((ℝ × E) × (E →L[ℝ] ℝ))}
    (he : (e : ((ℝ × E) × E) → ((ℝ × E) × (E →L[ℝ] ℝ))) = parametricLegendre L)
    (hL : ContDiffOn ℝ ∞ L e.source) (hG : ContDiffOn ℝ ∞ e.symm e.target)
    {t : ℝ} {p : E × (E →L[ℝ] ℝ)} (hp : ((t, p.1), p.2) ∈ e.target)
    (b w : E) : blockA L e t p b w = blockA L e t p w b := by
  rw [blockA_eq_hessian he hL hG hp, blockA_eq_hessian he hL hG hp]
  exact hessian_symm hL hG hp (b, 0) (w, 0)

/-- The actual C block is the previously identified inverse-Legendre momentum derivative. -/
theorem blockC_eq_inverseMomentumDerivative
    {L : (ℝ × E) × E → ℝ}
    {e : OpenPartialHomeomorph ((ℝ × E) × E) ((ℝ × E) × (E →L[ℝ] ℝ))}
    (hL : ContDiffOn ℝ ∞ L e.source) (hG : ContDiffOn ℝ ∞ e.symm e.target)
    {t : ℝ} {p : E × (E →L[ℝ] ℝ)} (hp : ((t, p.1), p.2) ∈ e.target) :
    blockC L e t p = GraphLegendre.inverseMomentumDerivative e ((t, p.1), p.2) := by
  ext q
  exact field_fderiv_fst hL hG hp (0, q)

/-- The actual C block is symmetric on the dual space. -/
theorem blockC_symm
    {L : (ℝ × E) × E → ℝ}
    {e : OpenPartialHomeomorph ((ℝ × E) × E) ((ℝ × E) × (E →L[ℝ] ℝ))}
    (he : (e : ((ℝ × E) × E) → ((ℝ × E) × (E →L[ℝ] ℝ))) = parametricLegendre L)
    (hL : ContDiffOn ℝ ∞ L e.source) (hG : ContDiffOn ℝ ∞ e.symm e.target)
    {t : ℝ} {p : E × (E →L[ℝ] ℝ)} (hp : ((t, p.1), p.2) ∈ e.target)
    (q r : E →L[ℝ] ℝ) : r (blockC L e t p q) = q (blockC L e t p r) := by
  rw [blockC_eq_inverseMomentumDerivative hL hG hp]
  exact GraphLegendre.inverseMomentumDerivative_symm he hp
    (hL.contDiffAt (e.open_source.mem_nhds (e.map_target hp)))
    ((hG.contDiffAt (e.open_target.mem_nhds hp)).differentiableAt (by simp)) q r

/-- The actual C block is the inverse actual vertical Lagrangian Hessian. -/
theorem blockC_eq_inverse [FiniteDimensional ℝ E]
    {L : (ℝ × E) × E → ℝ}
    {e : OpenPartialHomeomorph ((ℝ × E) × E) ((ℝ × E) × (E →L[ℝ] ℝ))}
    (he : (e : ((ℝ × E) × E) → ((ℝ × E) × (E →L[ℝ] ℝ))) = parametricLegendre L)
    (hL : ContDiffOn ℝ ∞ L e.source) (hG : ContDiffOn ℝ ∞ e.symm e.target)
    {t : ℝ} {p : E × (E →L[ℝ] ℝ)} (hp : ((t, p.1), p.2) ∈ e.target)
    (hpos : ∀ w : E, w ≠ 0 →
      0 < GraphLegendre.verticalHessian L (e.symm ((t, p.1), p.2)) w w) :
    blockC L e t p =
      ContinuousLinearMap.inverse (GraphLegendre.verticalHessian L (e.symm ((t, p.1), p.2))) := by
  rw [blockC_eq_inverseMomentumDerivative hL hG hp]
  exact GraphLegendre.inverseMomentumDerivative_eq_inverse he hp
    (hL.contDiffAt (e.open_source.mem_nhds (e.map_target hp)))
    ((hG.contDiffAt (e.open_target.mem_nhds hp)).differentiableAt (by simp)) hpos

/-- Positive actual vertical Hessians give strict positivity of the actual C block. -/
theorem blockC_pos
    {L : (ℝ × E) × E → ℝ}
    {e : OpenPartialHomeomorph ((ℝ × E) × E) ((ℝ × E) × (E →L[ℝ] ℝ))}
    (he : (e : ((ℝ × E) × E) → ((ℝ × E) × (E →L[ℝ] ℝ))) = parametricLegendre L)
    (hL : ContDiffOn ℝ ∞ L e.source) (hG : ContDiffOn ℝ ∞ e.symm e.target)
    {t : ℝ} {p : E × (E →L[ℝ] ℝ)} (hp : ((t, p.1), p.2) ∈ e.target)
    (hpos : ∀ w : E, w ≠ 0 →
      0 < GraphLegendre.verticalHessian L (e.symm ((t, p.1), p.2)) w w)
    {q : E →L[ℝ] ℝ} (hq : q ≠ 0) : 0 < q (blockC L e t p q) := by
  rw [blockC_eq_inverseMomentumDerivative hL hG hp]
  exact GraphLegendre.inverseMomentumDerivative_pos he hp
    (hL.contDiffAt (e.open_source.mem_nhds (e.map_target hp)))
    ((hG.contDiffAt (e.open_target.mem_nhds hp)).differentiableAt (by simp)) hpos hq

/-- Scalar Hessian symmetry gives the canonical negative dual mixed block. -/
theorem field_mixed_block
    {L : (ℝ × E) × E → ℝ}
    {e : OpenPartialHomeomorph ((ℝ × E) × E) ((ℝ × E) × (E →L[ℝ] ℝ))}
    (he : (e : ((ℝ × E) × E) → ((ℝ × E) × (E →L[ℝ] ℝ))) = parametricLegendre L)
    (hL : ContDiffOn ℝ ∞ L e.source) (hG : ContDiffOn ℝ ∞ e.symm e.target)
    {t : ℝ} {p : E × (E →L[ℝ] ℝ)} (hp : ((t, p.1), p.2) ∈ e.target)
    (b : E) (q : E →L[ℝ] ℝ) :
    (fderiv ℝ (field L e t) p (0, q)).2 b = -q (blockB L e t p b) := by
  have h := hessian_symm hL hG hp (b, 0) (0, q)
  rw [hessian_field_identity he hL hG hp, hessian_field_identity he hL hG hp] at h
  simp only [map_zero, sub_zero, zero_apply, zero_sub] at h
  change _ = -q ((fderiv ℝ (field L e t) p (b, 0)).1)
  linarith

/-- The derivative with respect to true graph position and momentum has Hamiltonian blocks. -/
theorem field_linearized_blocks
    {L : (ℝ × E) × E → ℝ}
    {e : OpenPartialHomeomorph ((ℝ × E) × E) ((ℝ × E) × (E →L[ℝ] ℝ))}
    (he : (e : ((ℝ × E) × E) → ((ℝ × E) × (E →L[ℝ] ℝ))) = parametricLegendre L)
    (hL : ContDiffOn ℝ ∞ L e.source) (hG : ContDiffOn ℝ ∞ e.symm e.target)
    {t : ℝ} {p : E × (E →L[ℝ] ℝ)} (hp : ((t, p.1), p.2) ∈ e.target)
    (b : E) (q : E →L[ℝ] ℝ) :
    fderiv ℝ (field L e t) p (b, q) =
      (blockB L e t p b + blockC L e t p q,
        -blockA L e t p b - q.comp (blockB L e t p)) := by
  have hsplit : (b, q) = (b, 0) + (0, q) := by simp
  rw [hsplit, map_add]
  apply Prod.ext
  · rfl
  · apply ContinuousLinearMap.ext
    intro w
    change (fderiv ℝ (field L e t) p (b, 0)).2 w +
        (fderiv ℝ (field L e t) p (0, q)).2 w =
      -(-(fderiv ℝ (field L e t) p (b, 0)).2 w) - q (blockB L e t p w)
    rw [field_mixed_block he hL hG hp]
    ring

/-- A genuine graph Euler–Lagrange curve has its actual momentum lift tangent to the
same inverse branch's nonautonomous Hamiltonian field. -/
theorem hasDerivAt_phase_of_graphEulerLagrange
    {L : (ℝ × E) × E → ℝ}
    {e : OpenPartialHomeomorph ((ℝ × E) × E) ((ℝ × E) × (E →L[ℝ] ℝ))}
    (he : (e : ((ℝ × E) × E) → ((ℝ × E) × (E →L[ℝ] ℝ))) = parametricLegendre L)
    {y : ℝ → E} {t : ℝ} (hy : DifferentiableAt ℝ y t)
    (hel : HasDerivAt (fun s ↦ fiberLegendre L ((s, y s), deriv y s))
      (positionDifferential L ((t, y t), deriv y t)) t)
    (hz : ((t, y t), deriv y t) ∈ e.source) :
    let p := fun s ↦ (y s, fiberLegendre L ((s, y s), deriv y s))
    HasDerivAt p (field L e t (p t)) t := by
  dsimp only
  have hinv : e.symm ((t, y t), fiberLegendre L ((t, y t), deriv y t)) =
      ((t, y t), deriv y t) := by
    change e.symm (parametricLegendre L ((t, y t), deriv y t)) = _
    rw [← he, e.left_inv hz]
  simpa only [field, hinv] using hy.hasDerivAt.prodMk hel

/-- The actual position derivative of the vertical momentum, with time fixed. -/
noncomputable def lagrangianMixed (L : (ℝ × E) × E → ℝ) (z : (ℝ × E) × E) :
    E →L[ℝ] (E →L[ℝ] ℝ) :=
  (fderiv ℝ (fiberLegendre L) z).comp
    ((ContinuousLinearMap.inl ℝ (ℝ × E) E).comp (ContinuousLinearMap.inr ℝ ℝ E))

/-- The actual second position partial, holding time and velocity fixed. -/
noncomputable def lagrangianPositionHessian (L : (ℝ × E) × E → ℝ)
    (z : (ℝ × E) × E) : E →L[ℝ] (E →L[ℝ] ℝ) :=
  (fderiv ℝ (positionDifferential L) z).comp
    ((ContinuousLinearMap.inl ℝ (ℝ × E) E).comp (ContinuousLinearMap.inr ℝ ℝ E))

private theorem partial_fderiv_apply
    {L : (ℝ × E) × E → ℝ} {D : ((ℝ × E) × E) → E →L[ℝ] ℝ}
    {z : (ℝ × E) × E} (hL : ContDiffAt ℝ ∞ L z) (hD : DifferentiableAt ℝ D z)
    (a : (ℝ × E) × E) (w : E)
    (heq : (fun q ↦ D q w) =ᶠ[𝓝 z] (fun q ↦ fderiv ℝ L q a))
    (u : (ℝ × E) × E) :
    fderiv ℝ D z u w = fderiv ℝ (fderiv ℝ L) z u a := by
  have hdL := (hL.fderiv_right (m := ∞) (by simp)).differentiableAt (by simp)
  have hleft := hD.hasFDerivAt.clm_apply (hasFDerivAt_const w z)
  have hright := hdL.hasFDerivAt.clm_apply (hasFDerivAt_const a z)
  have hd := hleft.unique (hright.congr_of_eventuallyEq heq)
  have h := congrArg (fun T : ((ℝ × E) × E) →L[ℝ] ℝ ↦ T u) hd
  simpa only [add_apply, ContinuousLinearMap.comp_apply, zero_apply,
    ContinuousLinearMap.map_zero, zero_add, ContinuousLinearMap.flip_apply] using h

/-- The mixed position/velocity partials coincide by the true scalar Hessian symmetry. -/
theorem positionDifferential_fderiv_vertical
    {L : (ℝ × E) × E → ℝ} {U : Set ((ℝ × E) × E)} (hU : IsOpen U)
    (hL : ContDiffOn ℝ ∞ L U) {z : (ℝ × E) × E} (hz : z ∈ U) (v w : E) :
    fderiv ℝ (positionDifferential L) z (0, v) w = lagrangianMixed L z w v := by
  have hLa := hL.contDiffAt (hU.mem_nhds hz)
  have hpos : (fun q ↦ positionDifferential L q w) =ᶠ[𝓝 z]
      (fun q ↦ fderiv ℝ L q ((0, w), 0)) := by
    filter_upwards [hU.mem_nhds hz] with q hq
    rw [GraphLegendre.fderiv_split
      ((hL.contDiffAt (hU.mem_nhds hq)).differentiableAt (by simp))]
    simp [positionDifferential]
  have hfib : (fun q ↦ fiberLegendre L q v) =ᶠ[𝓝 z]
      (fun q ↦ fderiv ℝ L q (0, v)) := by
    filter_upwards [hU.mem_nhds hz] with q hq
    rw [GraphLegendre.fderiv_split
      ((hL.contDiffAt (hU.mem_nhds hq)).differentiableAt (by simp))]
    simp
  rw [partial_fderiv_apply hLa
    ((contDiffAt_positionDifferential hLa).differentiableAt (by simp)) _ _ hpos]
  change _ = fderiv ℝ (fiberLegendre L) z ((0, w), 0) v
  rw [partial_fderiv_apply hLa
    ((contDiffAt_fiberLegendre hLa).differentiableAt (by simp)) _ _ hfib]
  exact (hLa.isSymmSndFDerivAt (by simp)).eq _ _

/-- Differentiating the true inverse equation gives G B + E = 0. -/
theorem verticalHessian_blockB
    {L : (ℝ × E) × E → ℝ}
    {e : OpenPartialHomeomorph ((ℝ × E) × E) ((ℝ × E) × (E →L[ℝ] ℝ))}
    (he : (e : ((ℝ × E) × E) → ((ℝ × E) × (E →L[ℝ] ℝ))) = parametricLegendre L)
    (hL : ContDiffOn ℝ ∞ L e.source) (hG : ContDiffOn ℝ ∞ e.symm e.target)
    {t : ℝ} {p : E × (E →L[ℝ] ℝ)} (hp : ((t, p.1), p.2) ∈ e.target) (b : E) :
    GraphLegendre.verticalHessian L (e.symm ((t, p.1), p.2)) (blockB L e t p b) =
      -lagrangianMixed L (e.symm ((t, p.1), p.2)) b := by
  let q := ((t, p.1), p.2)
  have hLa := hL.contDiffAt (e.open_source.mem_nhds (e.map_target hp))
  have hGi := (hG.contDiffAt (e.open_target.mem_nhds hp)).differentiableAt (by simp)
  have hc := (hasFDerivAt_parametricLegendre hLa).comp q hGi.hasFDerivAt
  have hid : HasFDerivAt (fun r ↦ parametricLegendre L (e.symm r))
      (ContinuousLinearMap.id ℝ ((ℝ × E) × (E →L[ℝ] ℝ))) q := by
    apply (hasFDerivAt_id q).congr_of_eventuallyEq
    filter_upwards [e.open_target.mem_nhds hp] with r hr
    exact (congrFun he (e.symm r)).symm.trans (e.right_inv hr)
  have hfst : (fderiv ℝ e.symm q ((0, b), 0)).1 = (0, b) :=
    congrArg (fun D : ((ℝ × E) × (E →L[ℝ] ℝ)) →L[ℝ] (ℝ × E) ↦ D ((0, b), 0))
      (GraphLegendre.inverse_derivative_fst he hp hGi.hasFDerivAt)
  have hsnd : (fderiv ℝ e.symm q ((0, b), 0)).2 = blockB L e t p b :=
    (field_fderiv_fst hL hG hp (b, 0)).symm
  have hpair : fderiv ℝ e.symm q ((0, b), 0) = ((0, b), blockB L e t p b) :=
    Prod.ext hfst hsnd
  have hId := congrArg (fun D : ((ℝ × E) × (E →L[ℝ] ℝ)) →L[ℝ]
      ((ℝ × E) × (E →L[ℝ] ℝ)) ↦ D ((0, b), 0)) (hc.unique hid)
  have hId' : fderiv ℝ (parametricLegendre L) (e.symm q)
      (fderiv ℝ e.symm q ((0, b), 0)) = ((0, b), 0) := by
    rw [parametricLegendre_fderiv_eq hLa]
    exact hId
  rw [hpair, parametricLegendre_fderiv_apply hLa] at hId'
  have hm := congrArg Prod.snd hId'
  change lagrangianMixed L (e.symm q) b +
    GraphLegendre.verticalHessian L (e.symm q) (blockB L e t p b) = 0 at hm
  exact eq_neg_of_add_eq_zero_right hm

/-- The actual B block equals minus inverse vertical Hessian times the actual mixed partial. -/
theorem blockB_eq_neg_inverse_mixed [FiniteDimensional ℝ E]
    {L : (ℝ × E) × E → ℝ}
    {e : OpenPartialHomeomorph ((ℝ × E) × E) ((ℝ × E) × (E →L[ℝ] ℝ))}
    (he : (e : ((ℝ × E) × E) → ((ℝ × E) × (E →L[ℝ] ℝ))) = parametricLegendre L)
    (hL : ContDiffOn ℝ ∞ L e.source) (hG : ContDiffOn ℝ ∞ e.symm e.target)
    {t : ℝ} {p : E × (E →L[ℝ] ℝ)} (hp : ((t, p.1), p.2) ∈ e.target)
    (hpos : ∀ w : E, w ≠ 0 →
      0 < GraphLegendre.verticalHessian L (e.symm ((t, p.1), p.2)) w w) (b : E) :
    blockB L e t p b = -blockC L e t p (lagrangianMixed L (e.symm ((t, p.1), p.2)) b) := by
  apply (positive_dualMap_equiv _ hpos).injective
  change GraphLegendre.verticalHessian L (e.symm ((t, p.1), p.2)) (blockB L e t p b) =
    GraphLegendre.verticalHessian L (e.symm ((t, p.1), p.2))
      (-blockC L e t p (lagrangianMixed L (e.symm ((t, p.1), p.2)) b))
  rw [verticalHessian_blockB he hL hG hp, map_neg,
    blockC_eq_inverseMomentumDerivative hL hG hp]
  rw [GraphLegendre.verticalHessian_inverseMomentumDerivative he hp
    (hL.contDiffAt (e.open_source.mem_nhds (e.map_target hp)))
    ((hG.contDiffAt (e.open_target.mem_nhds hp)).differentiableAt (by simp))]

/-- The actual A block has the Lagrangian Schur-complement expression E* C E - D. -/
theorem blockA_eq_lagrangian_schur [FiniteDimensional ℝ E]
    {L : (ℝ × E) × E → ℝ}
    {e : OpenPartialHomeomorph ((ℝ × E) × E) ((ℝ × E) × (E →L[ℝ] ℝ))}
    (he : (e : ((ℝ × E) × E) → ((ℝ × E) × (E →L[ℝ] ℝ))) = parametricLegendre L)
    (hL : ContDiffOn ℝ ∞ L e.source) (hG : ContDiffOn ℝ ∞ e.symm e.target)
    {t : ℝ} {p : E × (E →L[ℝ] ℝ)} (hp : ((t, p.1), p.2) ∈ e.target)
    (hpos : ∀ w : E, w ≠ 0 →
      0 < GraphLegendre.verticalHessian L (e.symm ((t, p.1), p.2)) w w) (b w : E) :
    blockA L e t p b w =
      lagrangianMixed L (e.symm ((t, p.1), p.2)) w
        (blockC L e t p (lagrangianMixed L (e.symm ((t, p.1), p.2)) b)) -
      lagrangianPositionHessian L (e.symm ((t, p.1), p.2)) b w := by
  let q := ((t, p.1), p.2)
  have hLa := hL.contDiffAt (e.open_source.mem_nhds (e.map_target hp))
  have hGi := (hG.contDiffAt (e.open_target.mem_nhds hp)).differentiableAt (by simp)
  have hi := ((hasFDerivAt_const (𝕜 := ℝ) t p).prodMk hasFDerivAt_fst).prodMk
    hasFDerivAt_snd
  have hposD := (contDiffAt_positionDifferential hLa).differentiableAt (by simp)
  have hchain := (hposD.hasFDerivAt.comp p (hGi.hasFDerivAt.comp p hi))
  have hX := (contDiffAt_field hL hG hp).differentiableAt (by simp)
  have hD : (ContinuousLinearMap.snd ℝ E (E →L[ℝ] ℝ)).comp
      (fderiv ℝ (field L e t) p) =
      (fderiv ℝ (positionDifferential L) (e.symm q)).comp
        ((fderiv ℝ e.symm q).comp
          ((ContinuousLinearMap.prod 0 (ContinuousLinearMap.fst ℝ E (E →L[ℝ] ℝ))).prod
            (ContinuousLinearMap.snd ℝ E (E →L[ℝ] ℝ)))) :=
    hX.hasFDerivAt.snd.unique hchain
  have hfst : (fderiv ℝ e.symm q ((0, b), 0)).1 = (0, b) :=
    congrArg (fun D : ((ℝ × E) × (E →L[ℝ] ℝ)) →L[ℝ] (ℝ × E) ↦ D ((0, b), 0))
      (GraphLegendre.inverse_derivative_fst he hp hGi.hasFDerivAt)
  have hsnd : (fderiv ℝ e.symm q ((0, b), 0)).2 = blockB L e t p b :=
    (field_fderiv_fst hL hG hp (b, 0)).symm
  have hpair : fderiv ℝ e.symm q ((0, b), 0) = ((0, b), blockB L e t p b) :=
    Prod.ext hfst hsnd
  have hh := congrArg (fun D : (E × (E →L[ℝ] ℝ)) →L[ℝ] (E →L[ℝ] ℝ) ↦ D (b, 0) w) hD
  change (fderiv ℝ (field L e t) p (b, 0)).2 w =
    fderiv ℝ (positionDifferential L) (e.symm q)
      (fderiv ℝ e.symm q ((0, b), 0)) w at hh
  rw [hpair] at hh
  have hsplit : (((0 : ℝ), b), blockB L e t p b) =
      ((0, b), 0) + (0, blockB L e t p b) := by
    simp
  rw [hsplit, map_add, add_apply,
    positionDifferential_fderiv_vertical e.open_source hL (e.map_target hp),
    blockB_eq_neg_inverse_mixed he hL hG hp hpos, map_neg] at hh
  change _ = lagrangianPositionHessian L (e.symm q) b w -
    lagrangianMixed L (e.symm q) w (blockC L e t p (lagrangianMixed L (e.symm q) b)) at hh
  change -(fderiv ℝ (field L e t) p (b, 0)).2 w = _
  rw [hh]
  ring

end OTSelector.Geometry.GraphHamiltonian

end
