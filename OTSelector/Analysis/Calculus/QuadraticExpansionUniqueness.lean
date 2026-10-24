import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Tactic.Ring

/-!
# Analysis.Calculus.QuadraticExpansionUniqueness

Conditions: An explicit quadratic error bound gives a little-o remainder, or a degree-two homogeneous difference is little-o of the squared norm.

Objects: Little-o conversion, zero of the homogeneous difference, and uniqueness of quadratic expansions.

Proof detail: Restrict to t times an arbitrary fixed vector, divide by t² and let t tend to zero; subtract two expansions for uniqueness.

## Mathematical sources

- [Jiří Lebl, Basic Analysis I](https://www.jirka.org/ra/html/sec_taylor.html): Section 4.3, Theorem 4.3.2 (Taylor), Exercise 4.3.5 and its finite-differentiability footnote (Peano remainder).

Source relation: Elementary Peano/homogeneity consequences; the local statements use exact degree-two scaling and arbitrary normed targets.
-/

/-!
# Uniqueness of a homogeneous quadratic expansion

A quadratic homogeneous function that is little-o of the squared norm vanishes.
Consequently two homogeneous quadratic approximations to the same scalar function
agree everywhere. No finite-dimensionality or regularity of the coefficients is used.
-/

open Set Filter Asymptotics Metric
open scoped Topology

namespace OTSelector.Geometry

variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]

omit [NormedSpace ℝ W] in
/-- Epsilon-radius quadratic remainder bounds give the corresponding little-o
statement at the origin, including its value at zero. -/
theorem isLittleO_norm_sq_of_remainder_bound {error : W → ℝ}
    (hbound : ∀ ε : ℝ, 0 < ε → ∃ r > 0, ∀ w : W, ‖w‖ < r →
      ‖error w‖ ≤ ε * ‖w‖ ^ 2) :
    error =o[𝓝 (0 : W)] (fun w ↦ ‖w‖ ^ 2) := by
  apply isLittleO_iff.mpr
  intro ε hε
  obtain ⟨r, hr, hb⟩ := hbound ε hε
  filter_upwards [ball_mem_nhds (0 : W) hr] with w hw
  have hwr : ‖w‖ < r := by simpa only [mem_ball, dist_zero_right] using hw
  simpa only [Real.norm_of_nonneg (sq_nonneg ‖w‖)] using hb w hwr

/-- A quadratic homogeneous function with a vanishing quadratic remainder is zero.
Scaling along a fixed direction reduces the claim to little-o of constant functions. -/
theorem quadratic_homogeneous_eq_zero_of_isLittleO {q : W → ℝ}
    (hhom : ∀ (a : ℝ) (w : W), q (a • w) = a ^ 2 * q w)
    (hsmall : q =o[𝓝 (0 : W)] (fun w ↦ ‖w‖ ^ 2)) : ∀ w, q w = 0 := by
  intro w
  have hcont : Continuous (fun t : ℝ ↦ t • w) := continuous_id.smul continuous_const
  have ht : Tendsto (fun t : ℝ ↦ t • w) (𝓝[>] (0 : ℝ)) (𝓝 (0 : W)) := by
    simpa only [zero_smul] using
      (hcont.tendsto (0 : ℝ)).mono_left nhdsWithin_le_nhds
  have hscaled : (fun t : ℝ ↦ t ^ 2 * q w) =o[𝓝[>] (0 : ℝ)]
      (fun t ↦ t ^ 2 * ‖w‖ ^ 2) := by
    simpa only [Function.comp_def, hhom, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs] using
      hsmall.comp_tendsto ht
  have hnonzero : ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ), t ^ 2 ≠ 0 := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact pow_ne_zero 2 (ne_of_gt ht)
  have hdiv := (isLittleO_mul_iff_isLittleO_div hnonzero).mp hscaled
  have hconst : (fun _ : ℝ ↦ q w) =o[𝓝[>] (0 : ℝ)] (fun _ ↦ ‖w‖ ^ 2) := by
    apply hdiv.congr' EventuallyEq.rfl
    filter_upwards [hnonzero] with t ht
    exact mul_div_cancel_left₀ _ ht
  exact isLittleO_const_const_iff.mp hconst

/-- Homogeneous quadratic coefficients in two little-o expansions of the same
function coincide on the whole real normed space. -/
theorem quadratic_expansion_unique {f q₁ q₂ : W → ℝ}
    (h₁ : ∀ (a : ℝ) (w : W), q₁ (a • w) = a ^ 2 * q₁ w)
    (h₂ : ∀ (a : ℝ) (w : W), q₂ (a • w) = a ^ 2 * q₂ w)
    (hf₁ : (fun w ↦ f w - q₁ w) =o[𝓝 (0 : W)] (fun w ↦ ‖w‖ ^ 2))
    (hf₂ : (fun w ↦ f w - q₂ w) =o[𝓝 (0 : W)] (fun w ↦ ‖w‖ ^ 2)) :
    ∀ w, q₁ w = q₂ w := by
  have hhom : ∀ (a : ℝ) (w : W),
      q₁ (a • w) - q₂ (a • w) = a ^ 2 * (q₁ w - q₂ w) := by
    intro a w
    rw [h₁, h₂]
    ring
  have hsmall : (fun w ↦ q₁ w - q₂ w) =o[𝓝 (0 : W)] (fun w ↦ ‖w‖ ^ 2) :=
    (hf₂.sub hf₁).congr_left (fun w ↦ by ring)
  intro w
  exact sub_eq_zero.mp (quadratic_homogeneous_eq_zero_of_isLittleO hhom hsmall w)

end OTSelector.Geometry
