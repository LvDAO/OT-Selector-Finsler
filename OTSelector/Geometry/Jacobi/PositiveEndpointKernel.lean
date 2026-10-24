import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Geometry.Jacobi.PositiveEndpointKernel

## Lemma skeleton

* **Conditions:** A nontrivial real interval, an actual position derivative driven by a positive inverse-Hessian response, zero momentum derivative and zero position variation at both endpoints.

* **Objects:** Vanishing of the endpoint momentum variation.

* **Proof detail:** Zero derivative makes momentum constant. If it were nonzero, pairing the position variation with it would have strictly positive derivative throughout the interval, contradicting equal zero endpoint values.

## Mathematical sources

- [Jiří Lebl, Basic Analysis II: Introduction to Real Analysis, Volume II (version 6.3, 15 May 2026)](https://www.jirka.org/ra/realanal2.pdf#page=46): Section 8.4.1, Lemma 8.4.1 and Proposition 8.4.2, pp. 46–47.
- [Gerald Teschl, Ordinary Differential Equations and Dynamical Systems (AMS 2012 author preliminary version)](https://www.mat.univie.ac.at/~gerald/ftp/book-ode/ode.pdf#page=56): Section 2.4, pp. 45–47, equations (2.46)–(2.50), Theorem 2.10.

Source relation (corollary): A positive-variation uniqueness argument proved from scalar derivative monotonicity, not a general Jacobi boundary-value existence theorem.
-/

/-!
# The endpoint-fixed kernel for a positive inverse-Hessian equation

A constant momentum variation and a positive velocity response admit no nonzero
momentum when the position variation vanishes at both ends of a nontrivial interval.
This analytic lemma is consumed by the original Finsler family derivative.
-/

open Set

namespace OTSelector.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Strict positivity rules out a nonzero momentum for an endpoint-fixed variation. -/
theorem momentum_eq_zero_of_endpoint_fixed_positive_variation
    {J : ℝ → E} {P : ℝ → (E →L[ℝ] ℝ)} {C : ℝ → (E →L[ℝ] ℝ) →L[ℝ] E}
    {a b : ℝ} (hab : a < b)
    (hJ : ∀ t ∈ Icc a b, HasDerivAt J (C t (P t)) t)
    (hP : ∀ t ∈ Icc a b, HasDerivAt P 0 t)
    (hpos : ∀ t ∈ Icc a b, ∀ p : E →L[ℝ] ℝ, p ≠ 0 → 0 < p (C t p))
    (ha : J a = 0) (hb : J b = 0) : P a = 0 := by
  have hPa (t : ℝ) (ht : t ∈ Icc a b) : P t = P a := by
    apply Convex.is_const_of_fderivWithin_eq_zero (𝕜 := ℝ) (convex_Icc a b)
      (fun s hs ↦ (hP s hs).differentiableAt.differentiableWithinAt) ?_ ht
      (left_mem_Icc.mpr hab.le)
    intro s hs
    simpa using ((hP s hs).hasFDerivAt.hasFDerivWithinAt.fderivWithin
      ((uniqueDiffOn_Icc hab) s hs))
  by_contra hne
  have hd (t : ℝ) (ht : t ∈ Icc a b) :
      HasDerivAt (fun s ↦ P a (J s)) (P a (C t (P a))) t := by
    simpa only [hPa t ht] using! (P a).hasFDerivAt.comp_hasDerivAt t (hJ t ht)
  have hm : StrictMonoOn (fun t ↦ P a (J t)) (Icc a b) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc a b)
      (fun t ht ↦ (hd t ht).continuousAt.continuousWithinAt)
    intro t ht
    have ht' : t ∈ Icc a b := interior_subset ht
    rw [(hd t ht').deriv]
    exact hpos t ht' (P a) hne
  have hlt := hm (left_mem_Icc.mpr hab.le) (right_mem_Icc.mpr hab.le) hab
  simp [ha, hb] at hlt

end OTSelector.Geometry
