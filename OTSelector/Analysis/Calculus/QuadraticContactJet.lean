import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.MetricSpace.Lipschitz

/-!
# Analysis.Calculus.QuadraticContactJet

Conditions: An actual quadratic contact bound, or two-sided quadratic supporting covectors, with the explicit radius and constant; normed source and real target.

Objects: A first derivative, uniqueness of contact covectors, and local Lipschitz control of the recovered jet.

Proof detail: Divide the quadratic remainder by the displacement for differentiability. To compare two covectors, evaluate supports at carefully chosen small probes and use linearity and norm duality.

## Mathematical sources

- [Jiří Lebl, Basic Analysis II](https://www.jirka.org/ra/realanal2.pdf#page=37): Section 8.3, Proposition 8.3.6 and Theorem 8.3.7, pp. 37–38; Section 8.6, pp. 60–61.
- [Hassler Whitney, Analytic Extensions of Differentiable Functions Defined in Closed Sets, Transactions of the AMS 36(1), 63–89 (1934)](https://www.ams.org/journals/tran/1934-036-01/S0002-9947-1934-1501735-3/S0002-9947-1934-1501735-3.pdf#page=2): Section 3, pp. 64–65, equations (3.1)–(3.2); Section 6, p. 66, equations (6.1)–(6.3).

Source relation: Locally proved normed-space contact estimates. The affine-jet remainder structure is classical; the factor-six bound and support-to-jet conversion are not claimed as Whitney’s verbatim theorem.
-/

/-!
# First jets on sets with quadratic contact bounds

A quadratic bound for the original function implies its actual derivative at a contact
point. Probing the ambient neighborhood, including points outside the contact set,
controls differences of contact derivatives. No extension or Lipschitz derivative is
assumed, and no Euclidean inner product or finite dimension is used.
-/

open Set Filter Metric
open scoped Topology NNReal

noncomputable section
namespace OTSelector.Geometry

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- A local quadratic affine error bound gives the actual prescribed derivative. -/
theorem hasFDerivAt_of_quadratic_contact {f : E → F} {p : E →L[ℝ] F} {x : E}
    {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ᶠ y in 𝓝 x, ‖f y - f x - p (y - x)‖ ≤ C * ‖y - x‖ ^ 2) :
    HasFDerivAt f p x := by
  apply HasFDerivAt.of_isLittleO
  apply Asymptotics.isLittleO_iff.mpr
  intro ε hε
  have hδ : 0 < ε / (C + 1) := div_pos hε (by positivity)
  filter_upwards [h, ball_mem_nhds x hδ] with y hy hxy
  have hd : ‖y - x‖ < ε / (C + 1) := by
    simpa only [mem_ball, dist_eq_norm] using hxy
  have hh : (C + 1) * ‖y - x‖ < ε := by
    nlinarith [(lt_div_iff₀ (by positivity : 0 < C + 1)).mp hd]
  have hc : C * ‖y - x‖ ≤ ε := by linarith [norm_nonneg (y - x)]
  exact hy.trans (by nlinarith [mul_le_mul_of_nonneg_right hc (norm_nonneg (y - x))])

/-- Lower and upper quadratic supports at the same scalar contact have the same
covector. Their equality is forced by ambient positive and negative direction tests. -/
theorem eq_contactCovectors_of_quadratic_supports {u : E → ℝ} {x : E}
    {p q : E →L[ℝ] ℝ} {R C : ℝ} (hR : 0 < R) (hC : 0 ≤ C)
    (h : ∀ z ∈ ball x R,
      u x + p (z - x) - C * ‖z - x‖ ^ 2 ≤ u z ∧
        u z ≤ u x + q (z - x) + C * ‖z - x‖ ^ 2) : p = q := by
  have hzero : HasFDerivAt (p - q) (0 : E →L[ℝ] ℝ) (0 : E) := by
    apply hasFDerivAt_of_quadratic_contact (by positivity : 0 ≤ 2 * C)
    filter_upwards [ball_mem_nhds (0 : E) hR] with v hv
    have hvR : ‖v‖ < R := by simpa only [mem_ball, dist_zero_right] using hv
    have hp := h (x + v) (by simpa only [mem_ball, dist_eq_norm, add_sub_cancel_left])
    have hm := h (x - v) (by
      rw [mem_ball, dist_eq_norm, show x - v - x = -v by abel, norm_neg]
      exact hvR)
    simp only [add_sub_cancel_left] at hp
    rw [show x - v - x = -v by abel, map_neg, map_neg, norm_neg] at hm
    simp only [map_zero, zero_apply, sub_zero, sub_apply,
      Real.norm_eq_abs, abs_le]
    constructor <;> linarith [hp.1, hp.2, hm.1, hm.2]
  exact sub_eq_zero.mp ((p - q).hasFDerivAt.unique hzero)

/-- Ambient quadratic contacts control the difference of their actual linear jets.
The probing ball is centered at the first contact and has radius their separation. -/
theorem norm_sub_contactJet_le {f : E → F} {D : E → E →L[ℝ] F}
    {x y : E} {U : Set E} {C : ℝ} (hC : 0 ≤ C)
    (hU : closedBall x ‖x - y‖ ⊆ U)
    (hx : ∀ z ∈ U, ‖f z - f x - D x (z - x)‖ ≤ C * ‖z - x‖ ^ 2)
    (hy : ∀ z ∈ U, ‖f z - f y - D y (z - y)‖ ≤ C * ‖z - y‖ ^ 2) :
    ‖D x - D y‖ ≤ 6 * C * ‖x - y‖ := by
  by_cases hxy : x = y
  · subst y
    simp
  have hr : 0 < ‖x - y‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hxy)
  apply (D x - D y).opNorm_le_bound' (by positivity)
  intro v hv
  have hvpos : 0 < ‖v‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hv)
  let t := ‖x - y‖ / ‖v‖
  have ht : 0 < t := div_pos hr hvpos
  have htv : t * ‖v‖ = ‖x - y‖ := div_mul_cancel₀ _ hv
  let z := x + t • v
  have hzx : ‖z - x‖ = ‖x - y‖ := by
    simpa only [z, add_sub_cancel_left, norm_smul_of_nonneg ht.le] using htv
  have hzU : z ∈ U := hU (by simp only [mem_closedBall, dist_eq_norm, hzx, le_refl])
  have hxU : x ∈ U := hU (mem_closedBall_self hr.le)
  have hzy : ‖z - y‖ ≤ 2 * ‖x - y‖ := by
    have hh := dist_triangle z x y
    simp only [dist_eq_norm, hzx] at hh
    linarith
  have hboundx : ‖f z - f x - D x (z - x)‖ ≤ C * ‖x - y‖ ^ 2 := by
    simpa only [hzx] using hx z hzU
  have hboundy : ‖f z - f y - D y (z - y)‖ ≤ 4 * C * ‖x - y‖ ^ 2 := by
    have hh := hy z hzU
    have hsq : ‖z - y‖ ^ 2 ≤ (2 * ‖x - y‖) ^ 2 := by nlinarith [norm_nonneg (z - y)]
    nlinarith [mul_le_mul_of_nonneg_left hsq hC]
  have hboundxy := hy x hxU
  have heq : (D x - D y) (t • v) =
      -(f z - f x - D x (z - x)) + (f z - f y - D y (z - y)) -
        (f x - f y - D y (x - y)) := by
    simp only [z, add_sub_cancel_left, sub_apply, map_sub, map_add]
    abel
  have hbound : ‖(D x - D y) (t • v)‖ ≤ 6 * C * ‖x - y‖ ^ 2 := by
    rw [heq]
    calc
      _ ≤ ‖-(f z - f x - D x (z - x)) + (f z - f y - D y (z - y))‖ +
          ‖f x - f y - D y (x - y)‖ := norm_sub_le _ _
      _ ≤ (‖f z - f x - D x (z - x)‖ + ‖f z - f y - D y (z - y)‖) +
          ‖f x - f y - D y (x - y)‖ := by
        gcongr
        simpa only [norm_neg] using norm_add_le (-(f z - f x - D x (z - x)))
          (f z - f y - D y (z - y))
      _ ≤ 6 * C * ‖x - y‖ ^ 2 := by linarith
  rw [map_smul, norm_smul_of_nonneg ht.le] at hbound
  apply le_of_mul_le_mul_left (a := t) _ ht
  calc
    _ ≤ 6 * C * ‖x - y‖ ^ 2 := hbound
    _ = t * (6 * C * ‖x - y‖ * ‖v‖) := by rw [← htv]; ring

/-- Uniform quadratic contacts on an ambient ball give the actual Lipschitz first jet
on any subset of its smaller concentric ball, even if that contact set has no interior. -/
theorem contactJet_on_closedBall {f : E → F} {D : E → E →L[ℝ] F}
    {K : Set E} {c : E} {R : ℝ} (hR : 0 < R) (C : ℝ≥0)
    (hK : K ⊆ closedBall c R)
    (hcontact : ∀ x ∈ K, ∀ z ∈ closedBall c (3 * R),
      ‖f z - f x - D x (z - x)‖ ≤ (C : ℝ) * ‖z - x‖ ^ 2) :
    (∀ x ∈ K, HasFDerivAt f (D x) x) ∧ LipschitzOnWith (6 * C) D K ∧
      LipschitzOnWith (6 * C) (fderiv ℝ f) K ∧
      ∀ x ∈ K, ∀ y ∈ K,
        ‖f y - f x - fderiv ℝ f x (y - x)‖ ≤ (C : ℝ) * ‖y - x‖ ^ 2 := by
  have hderiv (x : E) (hx : x ∈ K) : HasFDerivAt f (D x) x := by
    apply hasFDerivAt_of_quadratic_contact C.coe_nonneg
    have hxball : x ∈ ball c (3 * R) := by
      have hh := mem_closedBall.mp (hK hx)
      rw [mem_ball]
      linarith
    filter_upwards [isOpen_ball.mem_nhds hxball] with z hz
    exact hcontact x hx z (ball_subset_closedBall hz)
  have hlip : LipschitzOnWith (6 * C) D K := by
    apply lipschitzOnWith_iff_dist_le_mul.mpr
    intro x hx y hy
    have hU : closedBall x ‖x - y‖ ⊆ closedBall c (3 * R) := by
      intro z hz
      have hx' := mem_closedBall.mp (hK hx)
      have hy' := mem_closedBall.mp (hK hy)
      have hz' := mem_closedBall.mp hz
      rw [mem_closedBall]
      rw [← dist_eq_norm] at hz'
      have hxy := dist_triangle x c y
      rw [dist_comm c y] at hxy
      linarith [dist_triangle z x c]
    simpa only [dist_eq_norm, NNReal.coe_mul, NNReal.coe_ofNat] using
      norm_sub_contactJet_le C.coe_nonneg hU (hcontact x hx) (hcontact y hy)
  refine ⟨hderiv, hlip, ?_, ?_⟩
  · apply lipschitzOnWith_iff_dist_le_mul.mpr
    intro x hx y hy
    rw [(hderiv x hx).fderiv, (hderiv y hy).fderiv]
    exact lipschitzOnWith_iff_dist_le_mul.mp hlip x hx y hy
  · intro x hx y hy
    rw [(hderiv x hx).fderiv]
    apply hcontact x hx y
    have hy' := mem_closedBall.mp (hK hy)
    rw [mem_closedBall]
    linarith

/-- Genuine lower and upper quadratic supports derive a common actual derivative and
its Lipschitz and quadratic Whitney bounds on an arbitrary contact subset. The two
support covectors are initially independent; their agreement is a conclusion. -/
theorem contactJet_of_two_sided_supports {u : E → ℝ} {p q : E → E →L[ℝ] ℝ}
    {K : Set E} {c : E} {R : ℝ} (hR : 0 < R) (C : ℝ≥0)
    (hK : K ⊆ closedBall c R)
    (hcontact : ∀ x ∈ K, ∀ z ∈ closedBall c (3 * R),
      u x + p x (z - x) - (C : ℝ) * ‖z - x‖ ^ 2 ≤ u z ∧
        u z ≤ u x + q x (z - x) + (C : ℝ) * ‖z - x‖ ^ 2) :
    EqOn p q K ∧ (∀ x ∈ K, HasFDerivAt u (p x) x) ∧
      LipschitzOnWith (6 * C) (fderiv ℝ u) K ∧
      ∀ x ∈ K, ∀ y ∈ K,
        ‖u y - u x - fderiv ℝ u x (y - x)‖ ≤ (C : ℝ) * ‖y - x‖ ^ 2 := by
  have hpq : EqOn p q K := by
    intro x hx
    apply eq_contactCovectors_of_quadratic_supports hR C.coe_nonneg
    intro z hz
    apply hcontact x hx z
    have hx' := mem_closedBall.mp (hK hx)
    have hz' := mem_ball.mp hz
    rw [mem_closedBall]
    linarith [dist_triangle z x c]
  have hquad (x : E) (hx : x ∈ K) (z : E) (hz : z ∈ closedBall c (3 * R)) :
      ‖u z - u x - p x (z - x)‖ ≤ (C : ℝ) * ‖z - x‖ ^ 2 := by
    have hh := hcontact x hx z hz
    rw [← hpq hx] at hh
    rw [Real.norm_eq_abs, abs_le]
    constructor <;> linarith [hh.1, hh.2]
  obtain ⟨hderiv, _, hlip, hrem⟩ := contactJet_on_closedBall hR C hK hquad
  exact ⟨hpq, hderiv, hlip, hrem⟩

/-- Ordered lower and upper quadratic supports at the same contact imply the actual
original scalar function has the corresponding two-sided quadratic affine error. -/
theorem quadratic_contact_of_sandwich {u lower upper : E → ℝ} {x : E}
    {p : E →L[ℝ] ℝ} {C : ℝ} {U : Set E}
    (hvalue : lower x = u x ∧ upper x = u x)
    (horder : ∀ z ∈ U, lower z ≤ u z ∧ u z ≤ upper z)
    (hlower : ∀ z ∈ U, lower x + p (z - x) - C * ‖z - x‖ ^ 2 ≤ lower z)
    (hupper : ∀ z ∈ U, upper z ≤ upper x + p (z - x) + C * ‖z - x‖ ^ 2) :
    ∀ z ∈ U, ‖u z - u x - p (z - x)‖ ≤ C * ‖z - x‖ ^ 2 := by
  intro z hz
  rw [Real.norm_eq_abs, abs_le]
  have hl := hlower z hz
  have hu := hupper z hz
  rw [hvalue.1] at hl
  rw [hvalue.2] at hu
  constructor <;> linarith [(horder z hz).1, (horder z hz).2]

end OTSelector.Geometry
