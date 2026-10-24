import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.TangentCone.Real
import Mathlib.Tactic.Linarith
import Mathlib.Topology.MetricSpace.Isometry
import Mathlib.Topology.MetricSpace.Lipschitz

/-!
# Topology.MetricSpace.SaturatedCalibration

## Lemma skeleton

* **Conditions:** A one-Lipschitz real potential, an isometric closed interval and endpoint saturation; the derivative conclusions additionally supply actual differentiability at the initial endpoint and a nontrivial interval.

* **Objects:** Exact affine potential along the whole interval and unit derivative at the supplied endpoint derivative.

* **Proof detail:** Use the Lipschitz inequalities from both endpoints to squeeze each interior value to the affine formula. Restrict difference quotients to the right-hand interval and use uniqueness of the supplied derivative.

## Mathematical sources

- [Anton Petrunin, Lectures on metric geometry](https://anton-petrunin.github.io/metric-geometry/tex/lectures.pdf#page=18): Lecture 1, Section L, Proposition 1.29 and its preceding compact approximate-midpoint argument, p. 18; Section I, p. 13, defines a geodesic as an isometric interval.
- [Terence Tao, Analysis I](https://github.com/teorth/analysis/blob/main/Analysis/Section_6_4.lean): Section 6.4, Corollaries 6.4.14 (squeeze test) and 6.4.17 (zero test).
- [Jiří Lebl, Basic Analysis I: Introduction to Real Analysis, Volume I (version 6.3, 15 May 2026)](https://www.jirka.org/ra/realanal.pdf#page=155): Section 4.1.1, Definition 4.1.1, p. 155; Section 3.1, limits and one-sided limits.

Source relation (corollary): Pure metric saturation and a one-sided derivative argument; no smoothness of the calibration on the rest of the curve is imposed.
-/

/-!
# Saturation of metric calibrations on actual minimizing intervals

A one-Lipschitz real function which saturates the endpoint distance of an isometric
interval increases exactly at unit rate on that whole closed interval. If the actual
scalar composition has a derivative at the initial endpoint, that derivative is one.
No differentiability of the calibration along the rest of the curve is required.
-/

open Set
open scoped Topology

namespace OTSelector.Geometry

/-- Endpoint saturation propagates to every point of the same actual isometric interval. -/
theorem eq_affine_of_lipschitz_saturated_isometry
    {X : Type*} [PseudoMetricSpace X] {u : X → ℝ} {c : ℝ → X} {a b : ℝ}
    (hu : LipschitzWith 1 u) (hiso : Isometry (fun t : Icc a b ↦ c t))
    (hsat : u (c b) - u (c a) = b - a) :
    ∀ t ∈ Icc a b, u (c t) = u (c a) + (t - a) := by
  intro t ht
  have hab : a ≤ b := ht.1.trans ht.2
  have ha : a ∈ Icc a b := left_mem_Icc.mpr hab
  have hb : b ∈ Icc a b := right_mem_Icc.mpr hab
  have hta : dist (c t) (c a) = t - a := by
    have h := hiso.dist_eq ⟨t, ht⟩ ⟨a, ha⟩
    simpa only [Subtype.dist_eq, Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr ht.1)] using h
  have hbt : dist (c b) (c t) = b - t := by
    have h := hiso.dist_eq ⟨b, hb⟩ ⟨t, ht⟩
    simpa only [Subtype.dist_eq, Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr ht.2)] using h
  have hupper := hu.le_add_mul (c t) (c a)
  have hlower := hu.le_add_mul (c b) (c t)
  simp only [NNReal.coe_one, one_mul, hta, hbt] at hupper hlower
  linarith

/-- An actual derivative at the left endpoint is determined by affine agreement on a
nondegenerate closed interval; agreement outside that interval is unnecessary. -/
theorem deriv_eq_one_of_eq_affine_on_Icc {f : ℝ → ℝ} {a b d : ℝ}
    (hab : a < b) (hf : HasDerivAt f d a)
    (heq : ∀ t ∈ Icc a b, f t = f a + (t - a)) : d = 1 := by
  have ha : a ∈ Icc a b := left_mem_Icc.mpr hab.le
  have hlin : HasDerivAt (fun t : ℝ ↦ f a + (t - a)) 1 a := by
    simpa only [Pi.add_apply, id_eq, sub_zero, zero_add] using!
      (hasDerivAt_const a (f a)).add ((hasDerivAt_id a).sub_const a)
  have hwithin : HasDerivWithinAt f 1 (Icc a b) a :=
    hlin.hasDerivWithinAt.congr_of_mem heq ha
  exact (uniqueDiffOn_Icc hab a ha).eq_deriv (Icc a b) hf.hasDerivWithinAt hwithin

/-- A saturated one-Lipschitz calibration has derivative one at the initial point of an
actual isometric interval whenever that scalar composition has an actual derivative. -/
theorem deriv_comp_eq_one_of_lipschitz_saturated_isometry
    {X : Type*} [PseudoMetricSpace X] {u : X → ℝ} {c : ℝ → X} {a b d : ℝ}
    (hu : LipschitzWith 1 u) (hab : a < b)
    (hiso : Isometry (fun t : Icc a b ↦ c t))
    (hsat : u (c b) - u (c a) = b - a) (hd : HasDerivAt (u ∘ c) d a) : d = 1 :=
  deriv_eq_one_of_eq_affine_on_Icc hab hd
    (eq_affine_of_lipschitz_saturated_isometry (u := u) (c := c) hu hiso hsat)

end OTSelector.Geometry
