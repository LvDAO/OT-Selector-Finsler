import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Analysis.Calculus.ImmersionCenteredLowerBound

Conditions: An actual Fréchet derivative at a point is injective, with finite-dimensional source; no C1 neighborhood is assumed.

Objects: A positive local centered inverse bound on the distance from that center.

Proof detail: An injective linear map is bounded below on the finite-dimensional unit sphere. Make the derivative remainder smaller than half this lower bound and apply the reverse triangle inequality.

## Mathematical sources

- [Jiří Lebl, Basic Analysis II](https://www.jirka.org/ra/realanal2.pdf#page=37): Section 8.3, Proposition 8.3.6 and Theorem 8.3.7, pp. 37–38; Section 8.6, pp. 60–61.
- [Terence Tao, An Epsilon of Room, I](https://terrytao.wordpress.com/wp-content/uploads/2012/12/gsm-117-tao3-epsilon1.pdf#page=110): Sections 1.6.2 and 1.8.1, compactness by finite subcovers, pp. 78 and 101–102; Section 1.8.3, Proposition 1.8.10, pp. 107–108 (finite products).

Source relation: Differentiability-at-one-point consequence with a compact-sphere lower bound. This is weaker in conclusion than a local inverse theorem and uses no unjustified C1 hypothesis.
-/

/-!
# Centered local inverse bounds at an immersed point

An injective actual derivative on a finite-dimensional source bounds the source
displacement by the image displacement near its center. Only differentiability
at that center is needed.
-/

open Filter
open scoped Topology NNReal

namespace OTSelector.Geometry

variable {W E : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [FiniteDimensional ℝ W] [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Actual differentiability and an injective derivative give a centered local
inverse norm estimate, with a positive finite constant. -/
theorem exists_centered_inverse_bound_of_hasFDerivAt
    {f : W → E} {R : W →L[ℝ] E} {w : W} (hf : HasFDerivAt f R w)
    (hR : Function.Injective R) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ z in 𝓝 w, ‖z - w‖ ≤ C * ‖f z - f w‖ := by
  obtain ⟨K, hK, hanti⟩ :=
    R.toLinearMap.exists_antilipschitzWith (LinearMap.ker_eq_bot.mpr hR)
  have hK' : 0 < (K : ℝ) := hK
  let ε : ℝ := (2 * (K : ℝ))⁻¹
  have hε : 0 < ε := inv_pos.mpr (mul_pos (by norm_num) hK')
  have hKε : (K : ℝ) * ε = 1 / 2 := by
    dsimp [ε]
    field_simp
  refine ⟨2 * K, mul_pos (by norm_num) hK', ?_⟩
  filter_upwards [hf.isLittleO.def hε] with z hz
  have hl : ‖z - w‖ ≤ (K : ℝ) * ‖R (z - w)‖ := by
    simpa only [dist_eq_norm, map_zero, sub_zero] using! hanti.le_mul_dist (z - w) 0
  have ht : ‖R (z - w)‖ ≤ ‖f z - f w‖ + ε * ‖z - w‖ := by
    have hn := norm_sub_le (f z - f w) (f z - f w - R (z - w))
    have he : f z - f w - (f z - f w - R (z - w)) = R (z - w) := by abel
    rw [he] at hn
    exact hn.trans (add_le_add_right hz _)
  have hb := hl.trans (mul_le_mul_of_nonneg_left ht hK'.le)
  rw [mul_add, ← mul_assoc, hKε] at hb
  nlinarith

end OTSelector.Geometry
