import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Normed.Module.FiniteDimension
import OTSelector.Analysis.Calculus.QuadraticContactJet
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Geometry.MetricPotentialContact.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Geometry.MetricPotentialContact`; the selected original proof blocks follow. -/
section

/-!
Conditions: A one-Lipschitz potential is calibrated between the stated partners and actual endpoint costs have the given quadratic Taylor bounds.

Objects: Two-sided quadratic contact, actual first differential and quantitative Lipschitz control of that jet.

Proof detail: Sandwich the potential by endpoint costs, compare their linear/quadratic expansions and use the contact inequalities at two points to bound the jet difference.

Sources: Rotem Assouline, Section 4.2, Theorem 4.11, Lemmas 4.12–4.13, equations (4.6)–(4.9) (https://arxiv.org/html/2409.08001v6#S4.SS2); Jiří Lebl, Section 4.3, Theorem 4.3.2 (Taylor), Exercise 4.3.5 and its finite-differentiability footnote (Peano remainder) (https://www.jirka.org/ra/html/sec_taylor.html); Jiří Lebl, Section 8.4.1, Lemma 8.4.1 and Proposition 8.4.2, pp. 46–47 (https://www.jirka.org/ra/realanal2.pdf#page=46).
Relation: Derived metric version of the calibrated quadratic-contact method; the explicit constants are locally proved. The cited Lagrangian theorem is used for its contact/extension method; this module proves its own stated metric hypotheses.
-/

/-!
# Original metric calibration produces quadratic contact jets

A one-Lipschitz potential is trapped between its original calibrated endpoint distance
functions. Their actual second-derivative bounds produce quadratic contacts and hence
the original potential's actual Lipschitz first jet on the contact set.
-/

open Set Filter Metric
open scoped Topology ContDiff NNReal

noncomputable section
namespace OTSelector.Geometry

set_option backward.isDefEq.respectTransparency false

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A bound on the actual Hessian on a convex set controls the first-order Taylor
remainder. Two mean-value estimates suffice, without an assumed Taylor remainder. -/
theorem norm_linear_remainder_le_of_hessian_bound {f : E → ℝ} {U : Set E}
    (hU : Convex ℝ U) (hf : ∀ z ∈ U, DifferentiableAt ℝ f z)
    (hdf : ∀ z ∈ U, DifferentiableAt ℝ (fderiv ℝ f) z)
    {C : ℝ} (hC : 0 ≤ C) (hbound : ∀ z ∈ U, ‖fderiv ℝ (fderiv ℝ f) z‖ ≤ C)
    {x y : E} (hx : x ∈ U) (hy : y ∈ U) :
    ‖f y - f x - fderiv ℝ f x (y - x)‖ ≤ C * ‖y - x‖ ^ 2 := by
  have hseg : segment ℝ x y ⊆ U := hU.segment_subset hx hy
  let r : E → ℝ := fun z ↦ f z - f x - fderiv ℝ f x (z - x)
  have hd (z : E) (hz : z ∈ segment ℝ x y) :
      HasFDerivAt r (fderiv ℝ f z - fderiv ℝ f x) z := by
    simpa only [r, ContinuousLinearMap.comp_id, Function.comp_apply, id_eq, Pi.sub_apply] using!
      ((hf z (hseg hz)).hasFDerivAt.sub_const (f x)).sub
        ((fderiv ℝ f x).hasFDerivAt.comp z ((hasFDerivAt_id z).sub_const x))
  have hb (z : E) (hz : z ∈ segment ℝ x y) :
      ‖fderiv ℝ f z - fderiv ℝ f x‖ ≤ C * ‖y - x‖ := by
    calc
      _ ≤ C * ‖z - x‖ := hU.norm_image_sub_le_of_norm_fderiv_le hdf hbound hx (hseg hz)
      _ ≤ C * ‖y - x‖ := mul_le_mul_of_nonneg_left (norm_sub_le_of_mem_segment hz) hC
  have h := (convex_segment x y).norm_image_sub_le_of_norm_hasFDerivWithin_le
    (fun z hz ↦ (hd z hz).hasFDerivWithinAt) hb (left_mem_segment ℝ x y)
      (right_mem_segment ℝ x y)
  simpa only [r, sub_self, map_zero, sub_zero, pow_two, mul_assoc] using h

variable {M : Type*} [PseudoMetricSpace M]

/-- The original one-Lipschitz potential lies between original endpoint-distance
functions. Calibration makes both bounds touch the original potential at the center. -/
theorem metric_potential_calibrated_sandwich {φ : M → ℝ} (hφ : LipschitzWith 1 φ)
    {x a b : M} (ha : φ x - φ a = dist a x) (hb : φ b - φ x = dist x b) :
    (φ b - dist x b = φ x) ∧ (φ a + dist a x = φ x) ∧
      ∀ y : M, φ b - dist y b ≤ φ y ∧ φ y ≤ φ a + dist a y := by
  refine ⟨by linarith, by linarith, ?_⟩
  intro y
  have hleft := hφ.dist_le_mul b y
  have hright := hφ.dist_le_mul y a
  simp only [Real.dist_eq, NNReal.coe_one, one_mul] at hleft hright
  rw [dist_comm b y] at hleft
  rw [dist_comm y a] at hright
  constructor
  · linarith [(le_abs_self (φ b - φ y)).trans hleft]
  · linarith [(le_abs_self (φ y - φ a)).trans hright]

/-- Taylor bounds for the two original endpoint distances give genuine quadratic
supports of the original potential; no independent support functions are supplied. -/
theorem metric_potential_quadratic_supports {φ : M → ℝ} (hφ : LipschitzWith 1 φ)
    (Y : E → M) {x : E} {a b : M} {U : Set E} {C : ℝ}
    (ha : φ (Y x) - φ a = dist a (Y x))
    (hb : φ b - φ (Y x) = dist (Y x) b)
    (hleft : ∀ y ∈ U,
      ‖dist a (Y y) - dist a (Y x) -
        fderiv ℝ (fun z ↦ dist a (Y z)) x (y - x)‖ ≤ C * ‖y - x‖ ^ 2)
    (hright : ∀ y ∈ U,
      ‖dist (Y y) b - dist (Y x) b -
        fderiv ℝ (fun z ↦ dist (Y z) b) x (y - x)‖ ≤ C * ‖y - x‖ ^ 2) :
    ∀ y ∈ U,
      φ (Y x) + (-fderiv ℝ (fun z ↦ dist (Y z) b) x) (y - x) -
          C * ‖y - x‖ ^ 2 ≤ φ (Y y) ∧
        φ (Y y) ≤ φ (Y x) + fderiv ℝ (fun z ↦ dist a (Y z)) x (y - x) +
          C * ‖y - x‖ ^ 2 := by
  intro y hy
  obtain ⟨_, _, hbound⟩ := metric_potential_calibrated_sandwich hφ ha hb
  have hl := (abs_le.mp (show |dist a (Y y) - dist a (Y x) -
    fderiv ℝ (fun z ↦ dist a (Y z)) x (y - x)| ≤ C * ‖y - x‖ ^ 2 from hleft y hy)).2
  have hr := (abs_le.mp (show |dist (Y y) b - dist (Y x) b -
    fderiv ℝ (fun z ↦ dist (Y z) b) x (y - x)| ≤ C * ‖y - x‖ ^ 2 from hright y hy)).2
  simp only [neg_apply]
  constructor <;> linarith [(hbound (Y y)).1, (hbound (Y y)).2]

/-- Actual quadratic Taylor estimates for the calibrated original distances produce
actual derivatives and Lipschitz and quadratic Whitney bounds for the original potential. -/
theorem metric_potential_contactJet_of_distance_remainders {φ : M → ℝ}
    (hφ : LipschitzWith 1 φ) (Y : E → M) {K : Set E} {c : E} {R : ℝ}
    (hR : 0 < R) (C : ℝ≥0) (hK : K ⊆ closedBall c R) (a b : E → M)
    (ha : ∀ x ∈ K, φ (Y x) - φ (a x) = dist (a x) (Y x))
    (hb : ∀ x ∈ K, φ (b x) - φ (Y x) = dist (Y x) (b x))
    (hleft : ∀ x ∈ K, ∀ y ∈ closedBall c (3 * R),
      ‖dist (a x) (Y y) - dist (a x) (Y x) -
        fderiv ℝ (fun z ↦ dist (a x) (Y z)) x (y - x)‖ ≤ (C : ℝ) * ‖y - x‖ ^ 2)
    (hright : ∀ x ∈ K, ∀ y ∈ closedBall c (3 * R),
      ‖dist (Y y) (b x) - dist (Y x) (b x) -
        fderiv ℝ (fun z ↦ dist (Y z) (b x)) x (y - x)‖ ≤ (C : ℝ) * ‖y - x‖ ^ 2) :
    (∀ x ∈ K,
      HasFDerivAt (φ ∘ Y) (fderiv ℝ (fun z ↦ dist (a x) (Y z)) x) x ∧
        fderiv ℝ (φ ∘ Y) x = -fderiv ℝ (fun z ↦ dist (Y z) (b x)) x) ∧
      LipschitzOnWith (6 * C) (fderiv ℝ (φ ∘ Y)) K ∧
      ∀ x ∈ K, ∀ y ∈ K,
        ‖φ (Y y) - φ (Y x) - fderiv ℝ (φ ∘ Y) x (y - x)‖ ≤
          (C : ℝ) * ‖y - x‖ ^ 2 := by
  obtain ⟨heq, hderiv, hlip, hrem⟩ := contactJet_of_two_sided_supports
    (u := φ ∘ Y) hR C hK
    (fun x hx ↦ metric_potential_quadratic_supports hφ Y (ha x hx) (hb x hx)
      (hleft x hx) (hright x hx))
  refine ⟨?_, hlip, hrem⟩
  intro x hx
  refine ⟨?_, (hderiv x hx).fderiv⟩
  convert hderiv x hx using 1
  exact (heq hx).symm

/-- Actual C2 endpoint distances and a common bound on their actual Hessians produce
the original calibrated potential's first jet. Quadratic support and Taylor bounds
are derived, rather than supplied, and the calibrated endpoints may vary with x. -/
theorem metric_potential_contactJet_of_distance_hessians {φ : M → ℝ}
    (hφ : LipschitzWith 1 φ) (Y : E → M) {K : Set E} {c : E} {R : ℝ}
    (hR : 0 < R) (C : ℝ≥0) (hK : K ⊆ closedBall c R) (a b : E → M)
    (ha : ∀ x ∈ K, φ (Y x) - φ (a x) = dist (a x) (Y x))
    (hb : ∀ x ∈ K, φ (b x) - φ (Y x) = dist (Y x) (b x))
    (hleft : ∀ x ∈ K, ∀ z ∈ closedBall c (3 * R),
      ContDiffAt ℝ 2 (fun y ↦ dist (a x) (Y y)) z)
    (hright : ∀ x ∈ K, ∀ z ∈ closedBall c (3 * R),
      ContDiffAt ℝ 2 (fun y ↦ dist (Y y) (b x)) z)
    (hboundLeft : ∀ x ∈ K, ∀ z ∈ closedBall c (3 * R),
      ‖fderiv ℝ (fderiv ℝ (fun y ↦ dist (a x) (Y y))) z‖ ≤ (C : ℝ))
    (hboundRight : ∀ x ∈ K, ∀ z ∈ closedBall c (3 * R),
      ‖fderiv ℝ (fderiv ℝ (fun y ↦ dist (Y y) (b x))) z‖ ≤ (C : ℝ)) :
    (∀ x ∈ K,
      HasFDerivAt (φ ∘ Y) (fderiv ℝ (fun z ↦ dist (a x) (Y z)) x) x ∧
        fderiv ℝ (φ ∘ Y) x = -fderiv ℝ (fun z ↦ dist (Y z) (b x)) x) ∧
      LipschitzOnWith (6 * C) (fderiv ℝ (φ ∘ Y)) K ∧
      ∀ x ∈ K, ∀ y ∈ K,
        ‖φ (Y y) - φ (Y x) - fderiv ℝ (φ ∘ Y) x (y - x)‖ ≤
          (C : ℝ) * ‖y - x‖ ^ 2 := by
  have hxlarge (x : E) (hx : x ∈ K) : x ∈ closedBall c (3 * R) := by
    have hh := mem_closedBall.mp (hK hx)
    rw [mem_closedBall]
    linarith
  apply metric_potential_contactJet_of_distance_remainders hφ Y hR C hK a b ha hb
  · intro x hx y hy
    exact norm_linear_remainder_le_of_hessian_bound (convex_closedBall c (3 * R))
      (fun z hz ↦ (hleft x hx z hz).differentiableAt (by norm_num))
      (fun z hz ↦ ((hleft x hx z hz).fderiv_right (m := 1)
        (by norm_num)).differentiableAt one_ne_zero)
      C.coe_nonneg (hboundLeft x hx) (hxlarge x hx) hy
  · intro x hx y hy
    exact norm_linear_remainder_le_of_hessian_bound (convex_closedBall c (3 * R))
      (fun z hz ↦ (hright x hx z hz).differentiableAt (by norm_num))
      (fun z hz ↦ ((hright x hx z hz).fderiv_right (m := 1)
        (by norm_num)).differentiableAt one_ne_zero)
      C.coe_nonneg (hboundRight x hx) (hxlarge x hx) hy

/-- Compact endpoint sets and joint continuity of the actual distance Hessians supply
one uniform constant for the original calibrated contact jet. No Hessian bound or
quadratic support function is an input to this compact consumer. -/
theorem metric_potential_contactJet_of_compact_distance_hessians
    [FiniteDimensional ℝ E] {φ : M → ℝ} (hφ : LipschitzWith 1 φ) (Y : E → M)
    {K : Set E} {c : E} {R : ℝ} (hR : 0 < R) (hK : K ⊆ closedBall c R)
    (a b : E → M) {A B : Set M} (hA : IsCompact A) (hB : IsCompact B)
    (haA : MapsTo a K A) (hbB : MapsTo b K B)
    (ha : ∀ x ∈ K, φ (Y x) - φ (a x) = dist (a x) (Y x))
    (hb : ∀ x ∈ K, φ (b x) - φ (Y x) = dist (Y x) (b x))
    (hleft : ∀ a ∈ A, ∀ z ∈ closedBall c (3 * R),
      ContDiffAt ℝ 2 (fun y ↦ dist a (Y y)) z)
    (hright : ∀ b ∈ B, ∀ z ∈ closedBall c (3 * R),
      ContDiffAt ℝ 2 (fun y ↦ dist (Y y) b) z)
    (hcontLeft : ContinuousOn
      (fun q : M × E ↦ fderiv ℝ (fderiv ℝ (fun y ↦ dist q.1 (Y y))) q.2)
      (A ×ˢ closedBall c (3 * R)))
    (hcontRight : ContinuousOn
      (fun q : M × E ↦ fderiv ℝ (fderiv ℝ (fun y ↦ dist (Y y) q.1)) q.2)
      (B ×ˢ closedBall c (3 * R))) :
    ∃ C : ℝ≥0,
      (∀ x ∈ K,
        HasFDerivAt (φ ∘ Y) (fderiv ℝ (fun z ↦ dist (a x) (Y z)) x) x ∧
          fderiv ℝ (φ ∘ Y) x = -fderiv ℝ (fun z ↦ dist (Y z) (b x)) x) ∧
        LipschitzOnWith (6 * C) (fderiv ℝ (φ ∘ Y)) K ∧
        ∀ x ∈ K, ∀ y ∈ K,
          ‖φ (Y y) - φ (Y x) - fderiv ℝ (φ ∘ Y) x (y - x)‖ ≤
            (C : ℝ) * ‖y - x‖ ^ 2 := by
  obtain ⟨CL, hCL⟩ := (hA.prod (isCompact_closedBall c (3 * R))).exists_bound_of_continuousOn
    (f := fun q : M × E ↦ fderiv ℝ (fderiv ℝ (fun y ↦ dist q.1 (Y y))) q.2)
    (by exact hcontLeft)
  obtain ⟨CR, hCR⟩ := (hB.prod (isCompact_closedBall c (3 * R))).exists_bound_of_continuousOn
    (f := fun q : M × E ↦ fderiv ℝ (fderiv ℝ (fun y ↦ dist (Y y) q.1)) q.2)
    (by exact hcontRight)
  let C : ℝ≥0 := ⟨max 0 (max CL CR), le_max_left _ _⟩
  refine ⟨C, metric_potential_contactJet_of_distance_hessians hφ Y hR C hK a b ha hb
    (fun x hx ↦ hleft (a x) (haA hx)) (fun x hx ↦ hright (b x) (hbB hx)) ?_ ?_⟩
  · intro x hx z hz
    exact (hCL (a x, z) ⟨haA hx, hz⟩).trans
      ((le_max_left CL CR).trans (le_max_right 0 (max CL CR)))
  · intro x hx z hz
    exact (hCR (b x, z) ⟨hbB hx, hz⟩).trans
      ((le_max_right CL CR).trans (le_max_right 0 (max CL CR)))

end OTSelector.Geometry

end
end
