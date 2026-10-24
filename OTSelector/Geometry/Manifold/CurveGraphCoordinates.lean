import OTSelector.Analysis.Convex.Legendre.Parametric
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Geometry.CurveGraphCoordinates.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Geometry.CurveGraphCoordinates`; the selected original proof blocks follow. -/
section

/-!
Conditions: An actual C2 position family with nonzero longitudinal velocity and the stated inverse graph coordinates.

Objects: Graph coordinate maps, inverse differentials, time correction and invariance of radial-zero bilinear expressions.

Proof detail: Differentiate (w,t)↦(w,γ₁), solve the block inverse identity and substitute its longitudinal correction in the bilinear expressions.

Sources: Jiří Lebl, Section 8.5.1, Proposition 8.5.5 and the following block-operator argument, p. 55 (https://www.jirka.org/ra/realanal2.pdf#page=55); Jiří Lebl, Section 8.3, Theorem 8.3.7, p. 38; Exercise 8.3.7, p. 45 (differentiate the inverse identity) (https://www.jirka.org/ra/realanal2.pdf#page=38); Jiří Lebl, Section 8.6, Proposition 8.6.2, pp. 60–61 (equality of mixed second partial derivatives) (https://www.jirka.org/ra/realanal2.pdf#page=60).
Relation: Explicit graph-coordinate calculus, including the actual correction terms.
-/

/-!
# Actual local graph coordinates for a family of regular curves

The change `(w,t) ↦ (w, (γ(w,t)).1)` retains the family parameter and uses the
first position coordinate as the new time. A nonzero longitudinal velocity makes
its actual derivative invertible. The local inverse gives a jointly C2 reparameterized
family, equal to the original curves at the recovered old times. Differentiating
this same inverse computes the removed tangential variation and the new velocity.
These are local coordinates for an arbitrary finite-dimensional curve family;
no global tubular chart or Euler--Lagrange reparameterization is asserted.
-/

open Set Filter
open scoped Topology ContDiff

noncomputable section
namespace OTSelector.Geometry

variable {W V : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- Retain the family parameter and replace time by the first position coordinate. -/
def curveGraphCoordinateMap (γ : W × ℝ → ℝ × V) (z : W × ℝ) : W × ℝ :=
  (z.1, (γ z).1)

/-- The original position evaluated at the actual recovered old time. -/
def curveGraphPosition (γ : W × ℝ → ℝ × V)
    (e : OpenPartialHomeomorph (W × ℝ) (W × ℝ)) (q : W × ℝ) : ℝ × V :=
  γ (e.symm q)

omit [NormedSpace ℝ W] [NormedAddCommGroup V] [NormedSpace ℝ V] in
/-- The inverse retains the family label and the reparameterized first position is new time. -/
theorem curveGraph_inverse_components {γ : W × ℝ → ℝ × V}
    {e : OpenPartialHomeomorph (W × ℝ) (W × ℝ)}
    (he : (e : W × ℝ → W × ℝ) = curveGraphCoordinateMap γ)
    {q : W × ℝ} (hq : q ∈ e.target) :
    (e.symm q).1 = q.1 ∧ (γ (e.symm q)).1 = q.2 := by
  have h := e.right_inv hq
  rw [he] at h
  change ((e.symm q).1, (γ (e.symm q)).1) = q at h
  constructor
  · have hf := congrArg (fun p : W × ℝ ↦ p.1) h
    exact hf
  · have hs := congrArg (fun p : W × ℝ ↦ p.2) h
    exact hs

omit [NormedSpace ℝ W] [NormedAddCommGroup V] [NormedSpace ℝ V] in
/-- The same recovered parameter gives the original curve, now exactly in graph form. -/
theorem curveGraphPosition_eq {γ : W × ℝ → ℝ × V}
    {e : OpenPartialHomeomorph (W × ℝ) (W × ℝ)}
    (he : (e : W × ℝ → W × ℝ) = curveGraphCoordinateMap γ)
    {q : W × ℝ} (hq : q ∈ e.target) :
    curveGraphPosition γ e q = (q.2, (γ (q.1, (e.symm q).2)).2) := by
  have h := curveGraph_inverse_components he hq
  apply Prod.ext
  · exact h.2
  · change (γ (e.symm q)).2 = _
    have heq : e.symm q = (q.1, (e.symm q).2) := Prod.ext h.1 rfl
    rw [heq]

/-- The actual derivative of the inverse gives the precise old-time correction. -/
theorem curveGraph_inverse_fderiv_apply {γ : W × ℝ → ℝ × V}
    {e : OpenPartialHomeomorph (W × ℝ) (W × ℝ)}
    (he : (e : W × ℝ → W × ℝ) = curveGraphCoordinateMap γ)
    {q : W × ℝ} (hq : q ∈ e.target)
    (hγ : DifferentiableAt ℝ γ (e.symm q)) (hi : DifferentiableAt ℝ e.symm q)
    (hv : (fderiv ℝ γ (e.symm q) (0, 1)).1 ≠ 0) (w : W) (s : ℝ) :
    fderiv ℝ e.symm q (w, s) =
      (w, (s - (fderiv ℝ γ (e.symm q) (w, 0)).1) /
        (fderiv ℝ γ (e.symm q) (0, 1)).1) := by
  have hfst : (ContinuousLinearMap.fst ℝ W ℝ).comp (fderiv ℝ e.symm q) =
      ContinuousLinearMap.fst ℝ W ℝ := by
    apply hi.hasFDerivAt.fst.unique
    apply hasFDerivAt_fst.congr_of_eventuallyEq
    filter_upwards [e.open_target.mem_nhds hq] with p hp
    exact (curveGraph_inverse_components he hp).1
  have hfirst : (fderiv ℝ e.symm q (w, s)).1 = w :=
    congrArg (fun T : (W × ℝ) →L[ℝ] W ↦ T (w, s)) hfst
  have hsnd : ((ContinuousLinearMap.fst ℝ ℝ V).comp
      (fderiv ℝ γ (e.symm q))).comp (fderiv ℝ e.symm q) =
      ContinuousLinearMap.snd ℝ W ℝ := by
    apply (hγ.hasFDerivAt.fst.comp q hi.hasFDerivAt).unique
    apply hasFDerivAt_snd.congr_of_eventuallyEq
    filter_upwards [e.open_target.mem_nhds hq] with p hp
    exact (curveGraph_inverse_components he hp).2
  have hlast := congrArg (fun T : (W × ℝ) →L[ℝ] ℝ ↦ T (w, s)) hsnd
  change (fderiv ℝ γ (e.symm q) (fderiv ℝ e.symm q (w, s))).1 = s at hlast
  have hsplit : fderiv ℝ e.symm q (w, s) =
      (w, 0) + (fderiv ℝ e.symm q (w, s)).2 • (0, 1) := by
    apply Prod.ext <;> simp [hfirst]
  rw [hsplit, map_add, map_smul] at hlast
  apply Prod.ext hfirst
  apply (eq_div_iff hv).2
  change (fderiv ℝ γ (e.symm q) (w, 0)).1 +
    (fderiv ℝ e.symm q (w, s)).2 * (fderiv ℝ γ (e.symm q) (0, 1)).1 = s at hlast
  linarith

/-- Differentiating the reparameterized original positions retains the full tangent correction. -/
theorem curveGraphPosition_fderiv_apply {γ : W × ℝ → ℝ × V}
    {e : OpenPartialHomeomorph (W × ℝ) (W × ℝ)}
    (he : (e : W × ℝ → W × ℝ) = curveGraphCoordinateMap γ)
    {q : W × ℝ} (hq : q ∈ e.target)
    (hγ : DifferentiableAt ℝ γ (e.symm q)) (hi : DifferentiableAt ℝ e.symm q)
    (hv : (fderiv ℝ γ (e.symm q) (0, 1)).1 ≠ 0) (w : W) (s : ℝ) :
    fderiv ℝ (curveGraphPosition γ e) q (w, s) =
      fderiv ℝ γ (e.symm q) (w, 0) +
        ((s - (fderiv ℝ γ (e.symm q) (w, 0)).1) /
          (fderiv ℝ γ (e.symm q) (0, 1)).1) •
          fderiv ℝ γ (e.symm q) (0, 1) := by
  rw [show curveGraphPosition γ e = γ ∘ e.symm from rfl, fderiv_comp q hγ hi]
  change fderiv ℝ γ (e.symm q) (fderiv ℝ e.symm q (w, s)) = _
  rw [curveGraph_inverse_fderiv_apply he hq hγ hi hv]
  have hsplit (r : ℝ) : (w, r) = (w, 0) + r • (0, 1) := by ext <;> simp
  rw [hsplit, map_add, map_smul]

/-- At fixed graph time, regraphing subtracts precisely a radial multiple of old velocity. -/
theorem curveGraphPosition_parameter_fderiv {γ : W × ℝ → ℝ × V}
    {e : OpenPartialHomeomorph (W × ℝ) (W × ℝ)}
    (he : (e : W × ℝ → W × ℝ) = curveGraphCoordinateMap γ)
    {q : W × ℝ} (hq : q ∈ e.target)
    (hγ : DifferentiableAt ℝ γ (e.symm q)) (hi : DifferentiableAt ℝ e.symm q)
    (hv : (fderiv ℝ γ (e.symm q) (0, 1)).1 ≠ 0) (w : W) :
    fderiv ℝ (curveGraphPosition γ e) q (w, 0) =
      fderiv ℝ γ (e.symm q) (w, 0) -
        ((fderiv ℝ γ (e.symm q) (w, 0)).1 /
          (fderiv ℝ γ (e.symm q) (0, 1)).1) •
          fderiv ℝ γ (e.symm q) (0, 1) := by
  have h := curveGraphPosition_fderiv_apply he hq hγ hi hv w 0
  rw [zero_sub, neg_div, neg_smul, ← sub_eq_add_neg] at h
  exact h

/-- The new actual velocity is old velocity divided by its longitudinal component. -/
theorem curveGraphPosition_time_fderiv {γ : W × ℝ → ℝ × V}
    {e : OpenPartialHomeomorph (W × ℝ) (W × ℝ)}
    (he : (e : W × ℝ → W × ℝ) = curveGraphCoordinateMap γ)
    {q : W × ℝ} (hq : q ∈ e.target)
    (hγ : DifferentiableAt ℝ γ (e.symm q)) (hi : DifferentiableAt ℝ e.symm q)
    (hv : (fderiv ℝ γ (e.symm q) (0, 1)).1 ≠ 0) :
    fderiv ℝ (curveGraphPosition γ e) q (0, 1) =
      (fderiv ℝ γ (e.symm q) (0, 1)).1⁻¹ • fderiv ℝ γ (e.symm q) (0, 1) := by
  have h := curveGraphPosition_fderiv_apply he hq hγ hi hv (0 : W) 1
  have hzero : fderiv ℝ γ (e.symm q) ((0 : W), (0 : ℝ)) = 0 := map_zero _
  rw [hzero] at h
  simpa using h

/-- A symmetric bilinear form killing old velocity is unchanged by actual regraphing. -/
theorem curveGraphPosition_bilinear_invariant {γ : W × ℝ → ℝ × V}
    {e : OpenPartialHomeomorph (W × ℝ) (W × ℝ)}
    (he : (e : W × ℝ → W × ℝ) = curveGraphCoordinateMap γ)
    {q : W × ℝ} (hq : q ∈ e.target)
    (hγ : DifferentiableAt ℝ γ (e.symm q)) (hi : DifferentiableAt ℝ e.symm q)
    (hv : (fderiv ℝ γ (e.symm q) (0, 1)).1 ≠ 0)
    (H : (ℝ × V) →L[ℝ] (ℝ × V) →L[ℝ] ℝ)
    (hsym : ∀ u v, H u v = H v u)
    (hrad : H (fderiv ℝ γ (e.symm q) (0, 1)) = 0) (u w : W) :
    H (fderiv ℝ (curveGraphPosition γ e) q (u, 0))
      (fderiv ℝ (curveGraphPosition γ e) q (w, 0)) =
      H (fderiv ℝ γ (e.symm q) (u, 0)) (fderiv ℝ γ (e.symm q) (w, 0)) := by
  have hr (x) : H x (fderiv ℝ γ (e.symm q) (0, 1)) = 0 := by
    rw [hsym, hrad, zero_apply]
  rw [curveGraphPosition_parameter_fderiv he hq hγ hi hv,
    curveGraphPosition_parameter_fderiv he hq hγ hi hv]
  simp only [map_sub, map_smul, sub_apply, smul_apply, smul_eq_mul,
    hrad, zero_apply, hr, mul_zero, sub_zero]

/-- A regular longitudinal coordinate constructs an actual local C2 graph inverse
inside any prescribed open parameter neighborhood. -/
theorem exists_curveGraphCoordinates [FiniteDimensional ℝ W]
    {γ : W × ℝ → ℝ × V} {z : W × ℝ} {U : Set (W × ℝ)}
    (hγ : ContDiffAt ℝ 2 γ z)
    (hv : (fderiv ℝ γ z (0, 1)).1 ≠ 0) (hU : IsOpen U) (hz : z ∈ U) :
    ∃ e : OpenPartialHomeomorph (W × ℝ) (W × ℝ),
      (e : W × ℝ → W × ℝ) = curveGraphCoordinateMap γ ∧
      z ∈ e.source ∧ curveGraphCoordinateMap γ z ∈ e.target ∧ e.source ⊆ U ∧
      ContDiffOn ℝ 2 γ e.source ∧ ContDiffOn ℝ 2 e e.source ∧
      ContDiffOn ℝ 2 e.symm e.target ∧
      ContDiffOn ℝ 2 (curveGraphPosition γ e) e.target ∧
      (∀ p ∈ e.source, (fderiv ℝ γ p (0, 1)).1 ≠ 0 ∧
        0 < (fderiv ℝ γ p (0, 1)).1 * (fderiv ℝ γ z (0, 1)).1) ∧
      ∀ q ∈ e.target, (e.symm q).1 = q.1 ∧ (curveGraphPosition γ e q).1 = q.2 := by
  let ψ := curveGraphCoordinateMap γ
  have hψ : ContDiffAt ℝ 2 ψ z := contDiffAt_fst.prodMk hγ.fst
  let K := (ContinuousLinearMap.fst ℝ ℝ V).comp (fderiv ℝ γ z)
  let T := (ContinuousLinearMap.fst ℝ W ℝ).prod K
  have hD : HasFDerivAt ψ T z :=
    hasFDerivAt_fst.prodMk (hγ.differentiableAt (by norm_num)).hasFDerivAt.fst
  let d := ContinuousLinearEquiv.unitsEquivAut ℝ
    (Units.mk0 (fderiv ℝ γ z (0, 1)).1 hv)
  have hK (s : ℝ) : K (0, s) = d s := by
    have hs : ((0 : W), s) = s • (0, 1) := by ext <;> simp
    dsimp [K]
    rw [hs, map_smul]
    simp [d, ContinuousLinearEquiv.unitsEquivAut_apply]
  have hbij : Function.Bijective T := base_preserving_block_bijective K d hK
  let D := (LinearEquiv.ofBijective T.toLinearMap hbij).toContinuousLinearEquiv
  have hDE : HasFDerivAt ψ D.toContinuousLinearMap z := hD
  let e₀ := hψ.toOpenPartialHomeomorph ψ hDE (by norm_num)
  have hsrc : z ∈ e₀.source := hψ.mem_toOpenPartialHomeomorph_source hDE (by norm_num)
  have hinv : ContDiffAt ℝ 2 e₀.symm (ψ z) := hψ.to_localInverse hDE (by norm_num)
  let c := fun p ↦ (fderiv ℝ γ p (0, 1)).1
  have hc : ContinuousAt c z :=
    ((hγ.continuousAt_fderiv (by norm_num)).clm_apply continuousAt_const).fst
  have hsign : ∀ᶠ p in 𝓝 z, 0 < c p * c z :=
    (hc.mul continuousAt_const) (Ioi_mem_nhds (mul_self_pos.mpr hv))
  let G := (U ∩ ({p | ContDiffAt ℝ 2 γ p} ∩
    ψ ⁻¹' {q | ContDiffAt ℝ 2 e₀.symm q})) ∩ {p | 0 < c p * c z}
  have hG : G ∈ 𝓝 z := inter_mem
    (inter_mem (hU.mem_nhds hz) (inter_mem (hγ.eventually (by norm_num))
      (hψ.continuousAt (hinv.eventually (by norm_num))))) hsign
  let e := e₀.restr G
  have hez : z ∈ e.source := ⟨hsrc, mem_interior_iff_mem_nhds.mpr hG⟩
  have hsub : e.source ⊆ G := fun _ hp ↦ interior_subset hp.2
  have he : (e : W × ℝ → W × ℝ) = curveGraphCoordinateMap γ := rfl
  have hγlocal (p) (hp : p ∈ e.source) : ContDiffAt ℝ 2 γ p := (hsub hp).1.2.1
  have hγs : ContDiffOn ℝ 2 γ e.source :=
    fun p hp ↦ (hγlocal p hp).contDiffWithinAt
  have hes : ContDiffOn ℝ 2 e e.source := by
    intro p hp
    exact (contDiffAt_fst.prodMk (hγlocal p hp).fst).contDiffWithinAt
  have hei : ContDiffOn ℝ 2 e.symm e.target := by
    intro q hq
    have h := (hsub (e.map_target hq)).1.2.2
    change ContDiffAt ℝ 2 e₀.symm (ψ (e.symm q)) at h
    have hr : ψ (e.symm q) = q := e.right_inv hq
    rw [hr] at h
    exact h.contDiffWithinAt
  refine ⟨e, he, hez, e.map_source hez, fun p hp ↦ (hsub hp).1.1,
    hγs, hes, hei, ?_, ?_, ?_⟩
  · exact hγs.comp hei (fun q hq ↦ e.map_target hq)
  · intro p hp
    have hs : 0 < c p * c z := (hsub hp).2
    refine ⟨?_, hs⟩
    intro hn
    change c p = 0 at hn
    rw [hn, zero_mul] at hs
    exact (lt_irrefl 0) hs
  · intro q hq
    exact curveGraph_inverse_components he hq

end OTSelector.Geometry

end
end
