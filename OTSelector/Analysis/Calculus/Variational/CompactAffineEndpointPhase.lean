import Mathlib.Analysis.Normed.Module.FiniteDimension
import OTSelector.Analysis.Calculus.AffineEndpointVariation
import OTSelector.Analysis.Calculus.Variational.AffineEndpointParameter
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Geometry.CompactAffineEndpointPhase.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Geometry.CompactAffineEndpointPhase`; the selected original proof blocks follow. -/
section

/-!
Conditions: The central phase trace is compact inside the open admissible Lagrangian domain; smoothness is used for the derivative-bound consequence.

Objects: A common radius and compact phase set containing all affine endpoint perturbations, with uniform actual Hessian bounds.

Proof detail: Thicken the compact trace within the open set, bound the perturbation operator and use continuity of the actual Hessian on the compact enlargement.

Sources: Terence Tao, Sections 1.6.2 and 1.8.1, compactness by finite subcovers, pp. 78 and 101–102; Section 1.8.3, Proposition 1.8.10, pp. 107–108 (finite products) (https://terrytao.wordpress.com/wp-content/uploads/2012/12/gsm-117-tao3-epsilon1.pdf#page=110); Jiří Lebl, Section 8.4.1, Lemma 8.4.1 and Proposition 8.4.2, pp. 46–47 (https://www.jirka.org/ra/realanal2.pdf#page=46).
Relation: Compact domain-control corollary; no additional regularity of the center family is introduced.
-/

/-!
# Uniform compact neighborhoods of actual affine endpoint phases

One compact central phase set in an open domain supplies a common endpoint radius
and a compact neighborhood containing every affine endpoint perturbation. The radius
is uniform over all central paths with phase in that set. Actual smoothness of a
scalar cost then supplies a common bound on its actual Hessian in this neighborhood.
No regularity of a chosen family of central paths is required.
-/

open Set Filter Metric
open scoped Topology ContDiff NNReal

noncomputable section
namespace OTSelector.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- A compact phase set in an open domain supplies a common compact neighborhood
for all actual affine endpoint perturbations of all paths staying in that set. -/
theorem exists_compact_affineEndpointPhase_neighborhood
    {P D : Set (E × E)} (hP : IsCompact P) (hD : IsOpen D) (hPD : P ⊆ D)
    {a b : ℝ} (hab : a < b) :
    ∃ r : ℝ, 0 < r ∧ ∃ Q : Set (E × E), IsCompact Q ∧ Q ⊆ D ∧ P ⊆ Q ∧
      ∀ x : ℝ → E, (∀ t ∈ Icc a b, (x t, deriv x t) ∈ P) →
        ∀ z ∈ closedBall (x b) (2 * r), ∀ t ∈ Icc a b,
          affineEndpointPhase x a b (z, t) ∈ Q := by
  obtain ⟨η, hη, hηD⟩ := hP.exists_cthickening_subset_open hD hPD
  let A : ℝ := 1 + (b - a)⁻¹
  have hA : 0 < A := by dsimp [A]; positivity
  let r : ℝ := η / (4 * A)
  have hr : 0 < r := by dsimp [r]; positivity
  refine ⟨r, hr, cthickening η P, hP.cthickening, hηD, self_subset_cthickening P, ?_⟩
  intro x hx z hz t ht
  apply mem_cthickening_of_dist_le _ (x t, deriv x t) η P (hx t ht)
  calc
    dist (affineEndpointPhase x a b (z, t)) (x t, deriv x t) =
        ‖affineEndpointParameterMap (E := E) a b t (z - x b)‖ := by
      rw [dist_eq_norm, affineEndpointPhase_sub_center]
    _ ≤ ‖affineEndpointParameterMap (E := E) a b t‖ * ‖z - x b‖ :=
      ContinuousLinearMap.le_opNorm _ _
    _ ≤ A * ‖z - x b‖ := mul_le_mul_of_nonneg_right
      (norm_affineEndpointParameterMap_le hab ht) (norm_nonneg _)
    _ ≤ A * (2 * r) := mul_le_mul_of_nonneg_left
      (by simpa only [mem_closedBall, dist_eq_norm] using hz) hA.le
    _ = η / 2 := by dsimp [r]; field_simp [hA.ne']; ring
    _ ≤ η := half_le_self hη.le

/-- The same compact neighborhood supplies a uniform bound for the actual Hessian
of any smooth scalar cost, independent of the chosen central path. -/
theorem exists_compact_affineEndpointPhase_hessian_bound
    {P D : Set (E × E)} (hP : IsCompact P) (hD : IsOpen D) (hPD : P ⊆ D)
    {L : E × E → ℝ} (hL : ContDiffOn ℝ ∞ L D) {a b : ℝ} (hab : a < b) :
    ∃ r : ℝ, 0 < r ∧ ∃ (Q : Set (E × E)) (C : ℝ≥0),
      IsCompact Q ∧ Q ⊆ D ∧ P ⊆ Q ∧
      (∀ q ∈ Q, ‖fderiv ℝ (fderiv ℝ L) q‖ ≤ (C : ℝ)) ∧
      ∀ x : ℝ → E, (∀ t ∈ Icc a b, (x t, deriv x t) ∈ P) →
        ∀ z ∈ closedBall (x b) (2 * r), ∀ t ∈ Icc a b,
          affineEndpointPhase x a b (z, t) ∈ Q := by
  obtain ⟨r, hr, Q, hQ, hQD, hPQ, hphase⟩ :=
    exists_compact_affineEndpointPhase_neighborhood hP hD hPD hab
  let _instCompactAffineHessianNorm :
      NormedAddCommGroup ((E × E) →L[ℝ] (E × E) →L[ℝ] ℝ) :=
    ContinuousLinearMap.toNormedAddCommGroup
  let _instCompactAffineHessianSpace :
      NormedSpace ℝ ((E × E) →L[ℝ] (E × E) →L[ℝ] ℝ) :=
    ContinuousLinearMap.toNormedSpace
  have hH : ContinuousOn (fderiv ℝ (fderiv ℝ L)) D :=
    (hL.fderiv_of_isOpen hD (m := 1) (by simp)).continuousOn_fderiv_of_isOpen hD le_rfl
  obtain ⟨C, hC⟩ := hQ.exists_bound_of_continuousOn (hH.mono hQD)
  refine ⟨r, hr, Q, ⟨max C 0, le_max_right _ _⟩, hQ, hQD, hPQ, ?_, hphase⟩
  intro q hq
  exact (hC q hq).trans (le_max_left _ _)

end OTSelector.Geometry

end
end
