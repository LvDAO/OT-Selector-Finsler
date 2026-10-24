import OTSelector.Analysis.ODE.Flow.NonautonomousVariation
import OTSelector.Geometry.Manifold.CurveGraphCoordinates
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Geometry.RegraphedPositionKernel.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Geometry.RegraphedPositionKernel`; the selected original proof blocks follow. -/
section

/-!
Conditions: A position variation is annihilated by the reference covector, while the longitudinal velocity has nonzero covector pairing.

Objects: Preservation of position-kernel rank under the actual graph-time correction.

Proof detail: Insert the explicit time correction, apply the covector to recover its scalar coefficient and compare the two kernels.

Sources: Jiří Lebl, Section 8.5.1, Proposition 8.5.5 and the following block-operator argument, p. 55 (https://www.jirka.org/ra/realanal2.pdf#page=55); Jiří Lebl, Section 8.1.3, Propositions 8.1.17–8.1.18, p. 15 (https://www.jirka.org/ra/realanal2.pdf#page=15).
Relation: Explicit transversality/kernel calculation; no Jacobi equation or curvature theorem is used.
-/

/-!
# The actual position kernel survives a change to graph time

A covector annihilating the original parameter position variations and nonzero on the
original velocity prevents loss of a position-kernel direction under time correction.
The same genuine graph inverse therefore preserves the kernel of the actual position
parameter derivative. No position-rank or global-clock assumption is used.
-/

open Set Filter
open scoped Topology

noncomputable section
namespace OTSelector.Geometry

variable {E V W : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]

omit [NormedAddCommGroup W] [NormedSpace ℝ W] in
/-- A normal position direction vanishes after genuine graph-time correction exactly
when the original direction vanishes. -/
theorem adapted_spatial_correction_eq_zero_iff (T : E ≃L[ℝ] (ℝ × V))
    (p : E →L[ℝ] ℝ) {J v : E} (hc : (T v).1 ≠ 0) (hpv : p v ≠ 0)
    (hnormal : p J = 0) :
    (T J - ((T J).1 / (T v).1) • T v).2 = 0 ↔ J = 0 := by
  constructor
  · intro hzero
    let a := (T J).1 / (T v).1
    have hfirst : (T J - a • T v).1 = 0 := by
      change (T J).1 - ((T J).1 / (T v).1) * (T v).1 = 0
      rw [div_mul_cancel₀ _ hc, sub_self]
    have hfull : T J - a • T v = 0 := Prod.ext hfirst hzero
    have hJ : J - a • v = 0 := T.injective (by simpa using hfull)
    have ha : a = 0 := by
      have h := congrArg p hJ
      rw [map_sub, map_smul, hnormal, map_zero] at h
      change 0 - a * p v = 0 at h
      have hm : a * p v = 0 := by linarith
      exact (mul_eq_zero.mp hm).resolve_right hpv
    simpa only [ha, zero_smul, sub_zero] using hJ
  · rintro rfl
    simp

/-- The actual graph spatial parameter derivative has the same zero directions as the
original position parameter derivative, at the very same recovered family label/time. -/
theorem curveGraphPosition_parameter_eq_zero_iff
    {γ : W × ℝ → E} (T : E ≃L[ℝ] (ℝ × V))
    {e : OpenPartialHomeomorph (W × ℝ) (W × ℝ)}
    (he : (e : W × ℝ → W × ℝ) = curveGraphCoordinateMap (fun z ↦ T (γ z)))
    {q : W × ℝ} (hq : q ∈ e.target)
    (hγ : DifferentiableAt ℝ γ (e.symm q)) (hi : DifferentiableAt ℝ e.symm q)
    (hc : (T (fderiv ℝ γ (e.symm q) (0, 1))).1 ≠ 0)
    (p : E →L[ℝ] ℝ) (hpv : p (fderiv ℝ γ (e.symm q) (0, 1)) ≠ 0)
    (hnormal : ∀ u : W, p (fderiv ℝ (fun w ↦ γ (w, (e.symm q).2)) q.1 u) = 0)
    (u : W) :
    fderiv ℝ (fun w ↦
      (curveGraphPosition (fun z ↦ T (γ z)) e (w, q.2)).2) q.1 u = 0 ↔
        fderiv ℝ (fun w ↦ γ (w, (e.symm q).2)) q.1 u = 0 := by
  let z := e.symm q
  let γT := fun z ↦ T (γ z)
  let J := fderiv ℝ (fun w ↦ γ (w, z.2)) q.1
  let v := fderiv ℝ γ z (0, 1)
  have hlabel : z.1 = q.1 := (curveGraph_inverse_components he hq).1
  have hT : DifferentiableAt ℝ γT z := T.differentiableAt.comp z hγ
  have hDT (w : W × ℝ) : fderiv ℝ γT z w = T (fderiv ℝ γ z w) := by
    exact congrArg (fun D ↦ D w) (T.hasFDerivAt.comp z hγ.hasFDerivAt).fderiv
  have hv : (fderiv ℝ γT z (0, 1)).1 ≠ 0 := by rwa [hDT]
  have hJ : fderiv ℝ γ z (u, 0) = J u := by
    change fderiv ℝ γ z (u, 0) =
      fderiv ℝ (fun w ↦ γ (w, z.2)) q.1 u
    rw [← hlabel]
    exact (parameterVariation_eq_fderiv hγ u).symm
  have hP : DifferentiableAt ℝ (curveGraphPosition γT e) q := hT.comp q hi
  have hPs : DifferentiableAt ℝ (fun w ↦ curveGraphPosition γT e (w, q.2)) q.1 :=
    (hP.hasFDerivAt.comp (g := curveGraphPosition γT e)
      (f := fun w : W ↦ (w, q.2)) q.1
      (hasFDerivAt_prodMk_left q.1 q.2)).differentiableAt
  have hR : fderiv ℝ (fun w ↦ (curveGraphPosition γT e (w, q.2)).2) q.1 u =
      (T (J u) - ((T (J u)).1 / (T v).1) • T v).2 := by
    rw [show fderiv ℝ (fun w ↦ (curveGraphPosition γT e (w, q.2)).2) q.1 u =
      (fderiv ℝ (fun w ↦ curveGraphPosition γT e (w, q.2)) q.1 u).2 from
        congrArg (fun D ↦ D u) hPs.hasFDerivAt.snd.fderiv,
      parameterVariation_eq_fderiv hP u,
      curveGraphPosition_parameter_fderiv he hq hT hi hv,
      hDT, hDT, hJ]
  rw [hR]
  exact adapted_spatial_correction_eq_zero_iff T p hc hpv (hnormal u)

/-- Changing to a genuine local graph clock preserves injectivity of the actual
position parameter derivative under the proved normality condition. -/
theorem curveGraphPosition_parameter_injective_iff
    {γ : W × ℝ → E} (T : E ≃L[ℝ] (ℝ × V))
    {e : OpenPartialHomeomorph (W × ℝ) (W × ℝ)}
    (he : (e : W × ℝ → W × ℝ) = curveGraphCoordinateMap (fun z ↦ T (γ z)))
    {q : W × ℝ} (hq : q ∈ e.target)
    (hγ : DifferentiableAt ℝ γ (e.symm q)) (hi : DifferentiableAt ℝ e.symm q)
    (hc : (T (fderiv ℝ γ (e.symm q) (0, 1))).1 ≠ 0)
    (p : E →L[ℝ] ℝ) (hpv : p (fderiv ℝ γ (e.symm q) (0, 1)) ≠ 0)
    (hnormal : ∀ u : W, p (fderiv ℝ (fun w ↦ γ (w, (e.symm q).2)) q.1 u) = 0) :
    Function.Injective (fderiv ℝ (fun w ↦
      (curveGraphPosition (fun z ↦ T (γ z)) e (w, q.2)).2) q.1) ↔
        Function.Injective (fderiv ℝ (fun w ↦ γ (w, (e.symm q).2)) q.1) := by
  let R := fderiv ℝ (fun w ↦
    (curveGraphPosition (fun z ↦ T (γ z)) e (w, q.2)).2) q.1
  let J := fderiv ℝ (fun w ↦ γ (w, (e.symm q).2)) q.1
  have hk (u : W) : R u = 0 ↔ J u = 0 :=
    curveGraphPosition_parameter_eq_zero_iff T he hq hγ hi hc p hpv hnormal u
  constructor
  · intro h u v huv
    apply h
    apply sub_eq_zero.mp
    rw [← map_sub]
    apply (hk (u - v)).2
    rw [map_sub, huv, sub_self]
  · intro h u v huv
    apply h
    apply sub_eq_zero.mp
    rw [← map_sub]
    apply (hk (u - v)).1
    rw [map_sub, huv, sub_self]

end OTSelector.Geometry

end
end
