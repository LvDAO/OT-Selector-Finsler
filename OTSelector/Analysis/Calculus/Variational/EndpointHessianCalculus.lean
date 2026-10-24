import OTSelector.Analysis.Calculus.Variational.EndpointJacobiCompliance
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Geometry.EndpointHessianCalculus.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Geometry.EndpointHessianCalculus`; the selected original proof blocks follow. -/
section

/-!
Conditions: An actual endpoint gradient has the stated boundary momentum form and the indicated radial and inverse-compliance identities hold.

Objects: Endpoint Hessian as an inverse-compliance term minus its radial rank-one correction.

Proof detail: Differentiate the true endpoint gradient, evaluate it on endpoint variations, substitute the integrated momentum relation and separate the radial component.

Sources: Gerald Teschl, Section 8.3, p. 238, equations (8.33)–(8.36); Problem 8.7, p. 241 (https://www.mat.univie.ac.at/~gerald/ftp/book-ode/ode.pdf#page=249); Jiří Lebl, Section 8.3, Theorem 8.3.7, p. 38; Exercise 8.3.7, p. 45 (differentiate the inverse identity) (https://www.jirka.org/ra/realanal2.pdf#page=38); Stephen Boyd, Section 2.2.5, p. 34; Section 2.4.1, Example 2.15, p. 43; Appendix A.5.2, pp. 646–647 (https://web.stanford.edu/~boyd/cvxbook/bv_cvxbook.pdf#page=48).
Relation: Derived second-variation algebra with explicit endpoint assumptions; the displayed rank-one coefficient is proved in this library.
-/

/-!
# Endpoint Hessians from differentiated boundary momentum

A genuine first-variation gradient can be differentiated through its endpoint covectors.
The actual integrated response retains radial pairing, which fixes the scalar correction
when energy momentum is normalized to length momentum.
-/

open Set Filter MeasureTheory
open scoped Topology

noncomputable section
namespace OTSelector.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Differentiation of a proved endpoint-gradient identity gives the actual second
differential by differentiating its two endpoint momenta. -/
theorem fderiv_fderiv_of_endpoint_gradient {d : E × E → ℝ}
    {Pa Pb : E × E → E →L[ℝ] ℝ} {q₀ : E × E}
    (ha : DifferentiableAt ℝ Pa q₀) (hb : DifferentiableAt ℝ Pb q₀)
    (hgrad : fderiv ℝ d =ᶠ[𝓝 q₀] fun q ↦
      (Pb q).comp (ContinuousLinearMap.snd ℝ E E) -
        (Pa q).comp (ContinuousLinearMap.fst ℝ E E)) (h k : E × E) :
    fderiv ℝ (fderiv ℝ d) q₀ h k =
      fderiv ℝ Pb q₀ h k.2 - fderiv ℝ Pa q₀ h k.1 := by
  rw [hgrad.fderiv_eq, fderiv_fun_sub
    (hb.clm_comp (differentiableAt_const _))
    (ha.clm_comp (differentiableAt_const _)),
    fderiv_clm_comp hb (differentiableAt_const _),
    fderiv_clm_comp ha (differentiableAt_const _)]
  simp

/-- A radial pairing identity for the actual inverse Hessians integrates to the
same identity for their true operator integral. -/
theorem endpointCompliance_radial_pairing [CompleteSpace E]
    {C : ℝ → (E →L[ℝ] ℝ) →L[ℝ] E} {a b : ℝ}
    (hab : a ≤ b) (hC : ContinuousOn C (Icc a b)) (p : E →L[ℝ] ℝ) (v : E)
    (hrad : ∀ t ∈ Icc a b, ∀ q : E →L[ℝ] ℝ, p (C t q) = q v)
    (q : E →L[ℝ] ℝ) :
    p (endpointCompliance C a b q) = (b - a) * q v := by
  rw [endpointCompliance_apply hab hC,
    ← p.intervalIntegral_comp_comm
      ((hC.clm_apply continuousOn_const).intervalIntegrable_of_Icc hab)]
  calc
    (∫ t in a..b, p (C t q)) = ∫ _ in a..b, q v := by
      apply intervalIntegral.integral_congr
      intro t ht
      exact hrad t (by simpa only [uIcc_of_le hab] using ht) q
    _ = (b - a) * q v := by simp

/-- Evaluation of the inverse integral on the actual radial velocity is determined
by the original radial covector and the time duration. -/
theorem endpointCompliance_inverse_radial_pairing [CompleteSpace E]
    {C : ℝ → (E →L[ℝ] ℝ) →L[ℝ] E} {a b : ℝ}
    (hab : a < b) (hC : ContinuousOn C (Icc a b)) (p : E →L[ℝ] ℝ) (v : E)
    (hrad : ∀ t ∈ Icc a b, ∀ q : E →L[ℝ] ℝ, p (C t q) = q v)
    (hinv : (endpointCompliance C a b).IsInvertible) (w : E) :
    (endpointCompliance C a b).inverse w v = p w / (b - a) := by
  obtain ⟨d, hd⟩ := hinv
  have h := endpointCompliance_radial_pairing hab.le hC p v hrad (d.symm w)
  rw [← hd] at h
  change p (d (d.symm w)) = (b - a) * (d.symm w) v at h
  rw [d.apply_symm_apply] at h
  rw [← hd, ContinuousLinearMap.inverse_equiv]
  exact (eq_div_iff (sub_pos.mpr hab).ne').2 (by simpa only [mul_comm] using! h.symm)

/-- Identical corrected momentum responses at the two endpoints yield the full
second differential, expressed through their displacement difference. -/
theorem endpoint_hessian_of_momentum_response {d : E × E → ℝ}
    {Pa Pb : E × E → E →L[ℝ] ℝ} {q₀ : E × E}
    (ha : DifferentiableAt ℝ Pa q₀) (hb : DifferentiableAt ℝ Pb q₀)
    (hgrad : fderiv ℝ d =ᶠ[𝓝 q₀] fun q ↦
      (Pb q).comp (ContinuousLinearMap.snd ℝ E E) -
        (Pa q).comp (ContinuousLinearMap.fst ℝ E E))
    (R : E →L[ℝ] (E →L[ℝ] ℝ)) (p : E →L[ℝ] ℝ) (T : ℝ)
    (hPa : ∀ h : E × E, fderiv ℝ Pa q₀ h =
      R (h.2 - h.1) - (p (h.2 - h.1) / T) • p)
    (hPb : ∀ h : E × E, fderiv ℝ Pb q₀ h =
      R (h.2 - h.1) - (p (h.2 - h.1) / T) • p) (h k : E × E) :
    fderiv ℝ (fderiv ℝ d) q₀ h k =
      R (h.2 - h.1) (k.2 - k.1) - p (h.2 - h.1) * p (k.2 - k.1) / T := by
  rw [fderiv_fderiv_of_endpoint_gradient ha hb hgrad h k, hPa, hPb]
  simp only [sub_apply, smul_apply, smul_eq_mul, map_sub]
  ring

end OTSelector.Geometry

end
end
