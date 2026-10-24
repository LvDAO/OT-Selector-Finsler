import OTSelector.Analysis.Calculus.MetricPotentialContact
import OTSelector.Analysis.Calculus.QuadraticContactJet
import OTSelector.Analysis.Calculus.Whitney.C11
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Geometry.MetricPotentialUpperContact.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Geometry.MetricPotentialUpperContact`; the selected original proof blocks follow. -/
section

/-!
Conditions: Smooth upper path costs touch the actual endpoint distances and satisfy the stated Hessian bounds near the contact points.

Objects: Quadratic contact and C1,1/Whitney jet conclusions without assuming the distance itself is C2.

Proof detail: Use the touching upper costs in the calibration sandwich, obtain their Taylor bounds and apply the contact/Whitney interface.

Sources: Rotem Assouline, Section 4.2, Theorem 4.11, Lemmas 4.12–4.13, equations (4.6)–(4.9) (https://arxiv.org/html/2409.08001v6#S4.SS2); Jiří Lebl, Section 4.3, Theorem 4.3.2 (Taylor), Exercise 4.3.5 and its finite-differentiability footnote (Peano remainder) (https://www.jirka.org/ra/html/sec_taylor.html); Aris Daniilidis, Introduction, equation (1.1), pp. 1–2; Section 3, Theorem 3.1, pp. 6–7 (https://www.arisdaniilidis.at/DHLL.pdf#page=2).
Relation: Upper-contact adaptation of the standard method; distance smoothness is not added. The cited Lagrangian theorem is used for its contact/extension method; this module proves its own stated metric hypotheses.
-/

/-!
# Actual potential jets from smooth upper path-cost contacts

The original one-Lipschitz potential is bounded by calibrated endpoint distances.
Any upper path costs that touch those distances at the calibrated point give the
same two-sided contact. Bounds on their actual Hessians then supply the original
potential's actual derivative and Whitney estimates through the existing contact
jet theorem. A compact contact set admits a genuine C1,1 extension matching that
actual first jet. The original distance itself need not be twice differentiable.
-/

open Set Filter Metric
open scoped Topology ContDiff NNReal

noncomputable section
namespace OTSelector.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [PseudoMetricSpace M]

/-- Upper bounds for the original endpoint distances, touching at a calibrated point,
produce quadratic supports using their own actual Taylor remainders. -/
theorem metric_potential_quadratic_supports_of_upper_costs
    {φ : M → ℝ} (hφ : LipschitzWith 1 φ) (Y : E → M)
    {x : E} {a b : M} {U : Set E} {C : ℝ} (cA cB : E → ℝ)
    (ha : φ (Y x) - φ a = dist a (Y x))
    (hb : φ b - φ (Y x) = dist (Y x) b)
    (hdomA : ∀ y ∈ U, dist a (Y y) ≤ cA y)
    (hdomB : ∀ y ∈ U, dist (Y y) b ≤ cB y)
    (htouchA : cA x = dist a (Y x)) (htouchB : cB x = dist (Y x) b)
    (hleft : ∀ y ∈ U,
      ‖cA y - cA x - fderiv ℝ cA x (y - x)‖ ≤ C * ‖y - x‖ ^ 2)
    (hright : ∀ y ∈ U,
      ‖cB y - cB x - fderiv ℝ cB x (y - x)‖ ≤ C * ‖y - x‖ ^ 2) :
    ∀ y ∈ U,
      φ (Y x) + (-fderiv ℝ cB x) (y - x) - C * ‖y - x‖ ^ 2 ≤ φ (Y y) ∧
        φ (Y y) ≤ φ (Y x) + fderiv ℝ cA x (y - x) + C * ‖y - x‖ ^ 2 := by
  intro y hy
  obtain ⟨_, _, hbound⟩ := metric_potential_calibrated_sandwich hφ ha hb
  have hl := (abs_le.mp (show |cA y - cA x - fderiv ℝ cA x (y - x)| ≤
    C * ‖y - x‖ ^ 2 from hleft y hy)).2
  have hr := (abs_le.mp (show |cB y - cB x - fderiv ℝ cB x (y - x)| ≤
    C * ‖y - x‖ ^ 2 from hright y hy)).2
  simp only [neg_apply]
  constructor <;> linarith [(hbound (Y y)).1, (hbound (Y y)).2, hdomA y hy, hdomB y hy]

/-- Actual Taylor remainders of touching upper path costs determine the original
potential's actual derivative and its Lipschitz and quadratic Whitney bounds. -/
theorem metric_potential_contactJet_of_upper_cost_remainders
    {φ : M → ℝ} (hφ : LipschitzWith 1 φ) (Y : E → M)
    {K : Set E} {c : E} {R : ℝ} (hR : 0 < R) (C : ℝ≥0)
    (hK : K ⊆ closedBall c R) (a b : E → M) (cA cB : E → E → ℝ)
    (ha : ∀ x ∈ K, φ (Y x) - φ (a x) = dist (a x) (Y x))
    (hb : ∀ x ∈ K, φ (b x) - φ (Y x) = dist (Y x) (b x))
    (hdomA : ∀ x ∈ K, ∀ y ∈ closedBall c (3 * R), dist (a x) (Y y) ≤ cA x y)
    (hdomB : ∀ x ∈ K, ∀ y ∈ closedBall c (3 * R), dist (Y y) (b x) ≤ cB x y)
    (htouchA : ∀ x ∈ K, cA x x = dist (a x) (Y x))
    (htouchB : ∀ x ∈ K, cB x x = dist (Y x) (b x))
    (hleft : ∀ x ∈ K, ∀ y ∈ closedBall c (3 * R),
      ‖cA x y - cA x x - fderiv ℝ (cA x) x (y - x)‖ ≤ (C : ℝ) * ‖y - x‖ ^ 2)
    (hright : ∀ x ∈ K, ∀ y ∈ closedBall c (3 * R),
      ‖cB x y - cB x x - fderiv ℝ (cB x) x (y - x)‖ ≤ (C : ℝ) * ‖y - x‖ ^ 2) :
    (∀ x ∈ K, HasFDerivAt (φ ∘ Y) (fderiv ℝ (cA x) x) x ∧
      fderiv ℝ (φ ∘ Y) x = -fderiv ℝ (cB x) x) ∧
      LipschitzOnWith (6 * C) (fderiv ℝ (φ ∘ Y)) K ∧
      ∀ x ∈ K, ∀ y ∈ K,
        ‖φ (Y y) - φ (Y x) - fderiv ℝ (φ ∘ Y) x (y - x)‖ ≤
          (C : ℝ) * ‖y - x‖ ^ 2 := by
  obtain ⟨heq, hderiv, hlip, hrem⟩ := contactJet_of_two_sided_supports
    (u := φ ∘ Y) hR C hK
    (fun x hx ↦ metric_potential_quadratic_supports_of_upper_costs hφ Y
      (cA x) (cB x) (ha x hx) (hb x hx) (hdomA x hx) (hdomB x hx)
      (htouchA x hx) (htouchB x hx) (hleft x hx) (hright x hx))
  refine ⟨?_, hlip, hrem⟩
  intro x hx
  refine ⟨?_, (hderiv x hx).fderiv⟩
  convert hderiv x hx using 1
  exact (heq hx).symm

/-- Actual Hessian bounds of touching upper path costs produce the original potential
jet without assuming any smoothness of the original distance or any potential derivative. -/
theorem metric_potential_contactJet_of_upper_cost_hessians
    {φ : M → ℝ} (hφ : LipschitzWith 1 φ) (Y : E → M)
    {K : Set E} {c : E} {R : ℝ} (hR : 0 < R) (C : ℝ≥0)
    (hK : K ⊆ closedBall c R) (a b : E → M) (cA cB : E → E → ℝ)
    (ha : ∀ x ∈ K, φ (Y x) - φ (a x) = dist (a x) (Y x))
    (hb : ∀ x ∈ K, φ (b x) - φ (Y x) = dist (Y x) (b x))
    (hdomA : ∀ x ∈ K, ∀ y ∈ closedBall c (3 * R), dist (a x) (Y y) ≤ cA x y)
    (hdomB : ∀ x ∈ K, ∀ y ∈ closedBall c (3 * R), dist (Y y) (b x) ≤ cB x y)
    (htouchA : ∀ x ∈ K, cA x x = dist (a x) (Y x))
    (htouchB : ∀ x ∈ K, cB x x = dist (Y x) (b x))
    (hleft : ∀ x ∈ K, ∀ z ∈ closedBall c (3 * R), ContDiffAt ℝ 2 (cA x) z)
    (hright : ∀ x ∈ K, ∀ z ∈ closedBall c (3 * R), ContDiffAt ℝ 2 (cB x) z)
    (hboundLeft : ∀ x ∈ K, ∀ z ∈ closedBall c (3 * R),
      ‖fderiv ℝ (fderiv ℝ (cA x)) z‖ ≤ (C : ℝ))
    (hboundRight : ∀ x ∈ K, ∀ z ∈ closedBall c (3 * R),
      ‖fderiv ℝ (fderiv ℝ (cB x)) z‖ ≤ (C : ℝ)) :
    (∀ x ∈ K, HasFDerivAt (φ ∘ Y) (fderiv ℝ (cA x) x) x ∧
      fderiv ℝ (φ ∘ Y) x = -fderiv ℝ (cB x) x) ∧
      LipschitzOnWith (6 * C) (fderiv ℝ (φ ∘ Y)) K ∧
      ∀ x ∈ K, ∀ y ∈ K,
        ‖φ (Y y) - φ (Y x) - fderiv ℝ (φ ∘ Y) x (y - x)‖ ≤
          (C : ℝ) * ‖y - x‖ ^ 2 := by
  have hxlarge (x : E) (hx : x ∈ K) : x ∈ closedBall c (3 * R) := by
    have hh := mem_closedBall.mp (hK hx)
    rw [mem_closedBall]
    linarith
  apply metric_potential_contactJet_of_upper_cost_remainders hφ Y hR C hK a b cA cB
    ha hb hdomA hdomB htouchA htouchB
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

/-- Touching smooth upper path costs on a compact calibrated contact set construct a
compactly supported C1,1 extension matching both the original potential and its actual
first derivative. The two independently supplied cost derivatives agree as a conclusion. -/
theorem exists_metric_potential_C11_of_upper_cost_hessians
    [FiniteDimensional ℝ E] {φ : M → ℝ} (hφ : LipschitzWith 1 φ) (Y : E → M)
    {K : Set E} (hK : IsCompact K) {c : E} {R : ℝ} (hR : 0 < R)
    (C : ℝ≥0) (hKball : K ⊆ closedBall c R) (a b : E → M) (cA cB : E → E → ℝ)
    (ha : ∀ x ∈ K, φ (Y x) - φ (a x) = dist (a x) (Y x))
    (hb : ∀ x ∈ K, φ (b x) - φ (Y x) = dist (Y x) (b x))
    (hdomA : ∀ x ∈ K, ∀ y ∈ closedBall c (3 * R), dist (a x) (Y y) ≤ cA x y)
    (hdomB : ∀ x ∈ K, ∀ y ∈ closedBall c (3 * R), dist (Y y) (b x) ≤ cB x y)
    (htouchA : ∀ x ∈ K, cA x x = dist (a x) (Y x))
    (htouchB : ∀ x ∈ K, cB x x = dist (Y x) (b x))
    (hleft : ∀ x ∈ K, ∀ z ∈ closedBall c (3 * R), ContDiffAt ℝ 2 (cA x) z)
    (hright : ∀ x ∈ K, ∀ z ∈ closedBall c (3 * R), ContDiffAt ℝ 2 (cB x) z)
    (hboundLeft : ∀ x ∈ K, ∀ z ∈ closedBall c (3 * R),
      ‖fderiv ℝ (fderiv ℝ (cA x)) z‖ ≤ (C : ℝ))
    (hboundRight : ∀ x ∈ K, ∀ z ∈ closedBall c (3 * R),
      ‖fderiv ℝ (fderiv ℝ (cB x)) z‖ ≤ (C : ℝ)) :
    ∃ (G : E → ℝ) (L : ℝ≥0), ContDiff ℝ 1 G ∧ HasCompactSupport G ∧
      ContDiffOn ℝ ∞ G Kᶜ ∧ LipschitzWith L (fderiv ℝ G) ∧ EqOn G (φ ∘ Y) K ∧
      EqOn (fderiv ℝ G) (fderiv ℝ (φ ∘ Y)) K ∧
      ∀ x ∈ K, HasFDerivAt (φ ∘ Y) (fderiv ℝ G x) x ∧
        fderiv ℝ G x = fderiv ℝ (cA x) x ∧ fderiv ℝ G x = -fderiv ℝ (cB x) x := by
  obtain ⟨hactual, hlip, hrem⟩ := metric_potential_contactJet_of_upper_cost_hessians
    hφ Y hR C hKball a b cA cB ha hb hdomA hdomB htouchA htouchB
    hleft hright hboundLeft hboundRight
  have hC : (C : ℝ) ≤ ((6 * C : ℝ≥0) : ℝ) := by
    simp only [NNReal.coe_mul, NNReal.coe_ofNat]
    linarith [C.coe_nonneg]
  have hquad (v) (hv : v ∈ K) (w) (hw : w ∈ K) :
      ‖φ (Y v) - φ (Y w) - fderiv ℝ (φ ∘ Y) w (v - w)‖ ≤
        ((6 * C : ℝ≥0) : ℝ) * ‖v - w‖ ^ 2 :=
    (hrem w hw v hv).trans (mul_le_mul_of_nonneg_right hC (sq_nonneg _))
  obtain ⟨G, L, hG, hsupp, hOff, hLip, hval, hder⟩ :=
    exists_contDiff_one_lipschitz_fderiv_extension hK hlip hquad
  have hmatch : EqOn (fderiv ℝ G) (fderiv ℝ (φ ∘ Y)) K :=
    fun x hx ↦ (hder x hx).fderiv
  refine ⟨G, L, hG, hsupp, hOff, hLip, hval, hmatch, ?_⟩
  intro x hx
  have hp := (hmatch hx).trans (hactual x hx).1.fderiv
  exact ⟨(hactual x hx).1.congr_fderiv hp.symm, hp, (hmatch hx).trans (hactual x hx).2⟩

end OTSelector.Geometry

end
end
