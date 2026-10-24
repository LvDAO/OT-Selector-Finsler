import Mathlib.Tactic.Linarith
import Mathlib.Topology.MetricSpace.Isometry

/-!
# Transport.CalibratedFiberIsometry

## Lemma skeleton

* **Conditions:** For every ordered pair in the given set, equality of labels and ordered clock values is equivalent to calibration of the distance.

* **Objects:** An exact isometric real clock coordinate on each label fiber and its inverse values.

* **Proof detail:** Split into the two possible clock orders, use calibration in the appropriate order, and rewrite the absolute real distance. Restrict to a fiber and substitute the prescribed inverse-clock identities.

## Mathematical sources

- [Anton Petrunin, Lectures on metric geometry](https://anton-petrunin.github.io/metric-geometry/tex/lectures.pdf#page=18): Lecture 1, Section L, Proposition 1.29 and its preceding compact approximate-midpoint argument, p. 18; Section I, p. 13, defines a geodesic as an isometric interval.
- [J. C. Álvarez Paiva; A. C. Thompson, Volumes on Normed and Finsler Spaces, MSRI Publications 50 (2004)](https://library.slmath.org/books/Book50/files/02AT.pdf#page=22): Section 4.2, Definition 4.11 and Proposition 4.12, p. 22.

Source relation (corollary): Metric algebra from the supplied ordered-calibration equivalence; no differentiable Finsler structure or preselected coupling is added.
-/

/-!
# The potential is an exact distance coordinate on each calibrated label

The proved equivalence between ordered common labels and original calibration already
forces the potential coordinate to preserve every distance within each label. This does
not require a preselected coupling, an orientation of all supports or conditional densities.
-/

open Set
open scoped Topology

noncomputable section
namespace OTSelector.Reconstruction

variable {M Z : Type*} [MetricSpace M] {N : Set M} {a : M → Z} {u : M → ℝ}

/-- Ordered-label calibration makes the actual potential an isometry on each label. -/
theorem dist_eq_clock_dist_of_ordered_calibration
    (horder : ∀ x ∈ N, ∀ y ∈ N,
      (a x = a y ∧ u x ≤ u y) ↔ u y - u x = dist x y)
    {x y : M} (hx : x ∈ N) (hy : y ∈ N) (hlabel : a x = a y) :
    dist x y = dist (u x) (u y) := by
  rcases le_total (u x) (u y) with hle | hle
  · have hcal := (horder x hx y hy).mp ⟨hlabel, hle⟩
    rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hle)]
    linarith
  · have hcal := (horder y hy x hx).mp ⟨hlabel.symm, hle⟩
    rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hle)]
    simpa only [dist_comm y x] using hcal.symm

/-- Every actual label fiber embeds isometrically in the real potential coordinate. -/
theorem isometry_clock_on_label
    (horder : ∀ x ∈ N, ∀ y ∈ N,
      (a x = a y ∧ u x ≤ u y) ↔ u y - u x = dist x y) (z : Z) :
    Isometry (fun x : {x : M // x ∈ N ∧ a x = z} ↦ u x.val) := by
  apply Isometry.of_dist_eq
  intro x y
  exact (dist_eq_clock_dist_of_ordered_calibration horder x.property.1 y.property.1
    (x.property.2.trans y.property.2.symm)).symm

/-- Inverse coordinates retain the true distance whenever they lie in the actual fiber. -/
theorem dist_inverse_clock_of_ordered_calibration
    (horder : ∀ x ∈ N, ∀ y ∈ N,
      (a x = a y ∧ u x ≤ u y) ↔ u y - u x = dist x y)
    {b : Z → ℝ → M} {z : Z} {r s : ℝ}
    (hr : b z r ∈ N ∧ a (b z r) = z ∧ u (b z r) = r)
    (hs : b z s ∈ N ∧ a (b z s) = z ∧ u (b z s) = s) :
    dist (b z r) (b z s) = dist r s := by
  simpa only [hr.2.2, hs.2.2] using
    dist_eq_clock_dist_of_ordered_calibration horder hr.1 hs.1
      (hr.2.1.trans hs.2.1.symm)

end OTSelector.Reconstruction
