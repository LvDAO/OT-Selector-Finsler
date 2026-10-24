import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Prod
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Reconstruction.OriginalCubeTraceCompactnessPoincare.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Reconstruction.OriginalCubeTraceCompactnessPoincare`; the selected original proof blocks follow. -/
section

/-!
Conditions: A continuous interval integrand or C1 scalar function on a nontrivial compact interval; mean-zero is stated for the Poincaré conclusions.

Objects: Integral Cauchy–Schwarz, pointwise oscillation energy and the interval mean-zero Poincaré bound.

Proof detail: Apply Cauchy–Schwarz to the FTC integral, use the mean-zero identity to control a value, then integrate that pointwise bound.

Sources: Jiří Lebl, Section 5.3.1, Theorem 5.3.1, pp. 200–201 (https://www.jirka.org/ra/realanal.pdf#page=200); Terence Tao, Section 1.4, Lemma 1.4.7 (Cauchy–Schwarz inequality), p. 48 (https://terrytao.wordpress.com/wp-content/uploads/2012/12/gsm-117-tao3-epsilon1.pdf#page=57); Sheldon Axler, Section 3A (integration), Theorem 3.31 (dominated convergence); Section 5B, Theorems 5.28/5.32 (Tonelli/Fubini) (https://measure.axler.net/MIRA.pdf).
Relation: Direct one-dimensional Poincaré proof with a nonoptimal explicit interval constant, not a sharp eigenvalue claim.
-/

/-! Actual one-dimensional energy and zero-mean Poincare estimates for cube slices. -/
open Set Function Filter MeasureTheory
open scoped ENNReal Topology
noncomputable section
namespace OTSelector.Reconstruction

/-- Cauchy-Schwarz on a literal compact interval, obtained by integrating
an actual nonnegative square without an assumed variance estimate. -/
theorem smooth_interval_integral_sq_le
    {g : ℝ → ℝ} (hg : Continuous g) {a b : ℝ} (hab : a ≤ b) :
    (∫ t in a..b, g t) ^ 2 ≤ (b - a) * (∫ t in a..b, (g t) ^ 2) := by
  rcases lt_or_eq_of_le hab with hlt | rfl
  · let c := b - a
    let I := ∫ t in a..b, g t
    have hc : 0 < c := sub_pos.mpr hlt
    have hn : 0 ≤ ∫ t in a..b, (c * g t - I) ^ 2 :=
      intervalIntegral.integral_nonneg hab (fun t _ ↦ sq_nonneg _)
    have hlin : IntervalIntegrable
        (fun t ↦ c ^ 2 * (g t) ^ 2 - (2 * c * I) * g t) volume a b :=
      (((hg.pow 2).const_mul _).sub (hg.const_mul _)).intervalIntegrable a b
    have he : (∫ t in a..b, (c * g t - I) ^ 2) =
        c * (c * (∫ t in a..b, (g t) ^ 2) - I ^ 2) := by
      calc
        _ = ∫ t in a..b, (c ^ 2 * (g t) ^ 2 - (2 * c * I) * g t) + I ^ 2 := by
          congr 1
          funext t
          ring
        _ = _ := by
          rw [intervalIntegral.integral_add hlin (continuous_const.intervalIntegrable a b),
            intervalIntegral.integral_sub (f := fun t ↦ c ^ 2 * (g t) ^ 2)
              (g := fun t ↦ (2 * c * I) * g t)
              (((hg.pow 2).const_mul _).intervalIntegrable a b)
              ((hg.const_mul _).intervalIntegrable a b),
            intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
            intervalIntegral.integral_const]
          dsimp only [I, c]
          simp only [smul_eq_mul]
          ring
    rw [he] at hn
    have hout : 0 ≤ c * (∫ t in a..b, (g t) ^ 2) - I ^ 2 :=
      nonneg_of_mul_nonneg_right hn hc
    dsimp only [c, I] at hout
    linarith
  · simp

/-- The actual C1 increment on a compact interval is controlled by its
original derivative L2 energy, with the true interval length. -/
theorem smooth_interval_sub_sq_le_energy
    {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f) {a b s t : ℝ}
    (hab : a ≤ b) (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) :
    (f t - f s) ^ 2 ≤ (b - a) * (∫ r in a..b, (deriv f r) ^ 2) := by
  have hdc := hf.continuous_deriv (by norm_num)
  have hE0 : 0 ≤ ∫ r in a..b, (deriv f r) ^ 2 :=
    intervalIntegral.integral_nonneg hab (fun r _ ↦ sq_nonneg _)
  have hcase : ∀ u v : ℝ, a ≤ u → u ≤ v → v ≤ b →
      (f v - f u) ^ 2 ≤ (b - a) * (∫ r in a..b, (deriv f r) ^ 2) := by
    intro u v hau huv hvb
    have hFTC : (∫ r in u..v, deriv f r) = f v - f u :=
      intervalIntegral.integral_deriv_eq_sub
        (fun r _ ↦ hf.differentiable (by norm_num) r) (hdc.intervalIntegrable u v)
    have hCS := smooth_interval_integral_sq_le hdc huv
    rw [hFTC] at hCS
    have hm := intervalIntegral.integral_mono_interval (μ := volume) hau huv hvb
      (Filter.Eventually.of_forall fun r ↦ sq_nonneg (deriv f r))
      ((hdc.pow 2).intervalIntegrable a b)
    exact hCS.trans ((mul_le_mul_of_nonneg_left hm (sub_nonneg.mpr huv)).trans
      (mul_le_mul_of_nonneg_right (by linarith) hE0))
  by_cases hst : s ≤ t
  · exact hcase s t hs.1 hst ht.2
  · rw [sub_sq_comm]
    exact hcase t s ht.1 (le_of_not_ge hst) hs.2

/-- A true zero-mean C1 slice satisfies the pointwise Poincare bound from
its original derivative energy, including both actual endpoint traces. -/
theorem smooth_interval_point_sq_le_energy_of_mean_zero
    {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f) {a b t : ℝ}
    (hab : a < b) (ht : t ∈ Icc a b) (hmean : (∫ r in a..b, f r) = 0) :
    (f t) ^ 2 ≤ (b - a) * (∫ r in a..b, (deriv f r) ^ 2) := by
  let c := b - a
  let E := ∫ r in a..b, (deriv f r) ^ 2
  have hc : 0 < c := sub_pos.mpr hab
  have hI : (∫ r in a..b, f t - f r) = c * f t := by
    rw [intervalIntegral.integral_sub (f := fun _ ↦ f t) (g := f)
      (continuous_const.intervalIntegrable a b) (hf.continuous.intervalIntegrable a b),
      intervalIntegral.integral_const, hmean]
    simp only [sub_zero, smul_eq_mul, c]
  have hCS := smooth_interval_integral_sq_le (g := fun r ↦ f t - f r)
    (continuous_const.sub hf.continuous) hab.le
  change (∫ r in a..b, f t - f r) ^ 2 ≤ c * (∫ r in a..b, (f t - f r) ^ 2) at hCS
  rw [hI] at hCS
  have hpoint : ∀ r ∈ Icc a b, (f t - f r) ^ 2 ≤ c * E := by
    intro r hr
    exact smooth_interval_sub_sq_le_energy hf hab.le hr ht
  have hm := intervalIntegral.integral_mono_on (μ := volume) hab.le
    (((continuous_const.sub hf.continuous).pow 2).intervalIntegrable a b)
    (continuous_const.intervalIntegrable a b) hpoint
  change (∫ r in a..b, (f t - f r) ^ 2) ≤ ∫ _ in a..b, c * E at hm
  rw [intervalIntegral.integral_const] at hm
  change (∫ r in a..b, (f t - f r) ^ 2) ≤ c * (c * E) at hm
  have hfinal : c ^ 2 * (f t) ^ 2 ≤ c ^ 2 * (c * E) := by
    calc
      _ = (c * f t) ^ 2 := by ring
      _ ≤ c * (∫ r in a..b, (f t - f r) ^ 2) := hCS
      _ ≤ c * (c * (c * E)) := mul_le_mul_of_nonneg_left hm hc.le
      _ = _ := by ring
  exact (mul_le_mul_iff_right₀ (sq_pos_of_pos hc)).1 hfinal

/-- The actual mean-zero interval Poincare inequality for C1 functions,
with a deterministic constant given by the squared original interval length. -/
theorem smooth_interval_poincare_sq
    {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f) {a b : ℝ}
    (hab : a < b) (hmean : (∫ r in a..b, f r) = 0) :
    (∫ t in a..b, (f t) ^ 2) ≤
      (b - a) ^ 2 * (∫ r in a..b, (deriv f r) ^ 2) := by
  have hpoint : ∀ t ∈ Icc a b, (f t) ^ 2 ≤
      (b - a) * (∫ r in a..b, (deriv f r) ^ 2) := by
    intro t ht
    exact smooth_interval_point_sq_le_energy_of_mean_zero hf hab ht hmean
  have hm := intervalIntegral.integral_mono_on (μ := volume) hab.le
    ((hf.continuous.pow 2).intervalIntegrable a b)
    (continuous_const.intervalIntegrable a b) hpoint
  change (∫ t in a..b, (f t) ^ 2) ≤
    ∫ _ in a..b, (b - a) * (∫ r in a..b, (deriv f r) ^ 2) at hm
  rw [intervalIntegral.integral_const] at hm
  simpa only [smul_eq_mul, ← mul_assoc, ← pow_two] using hm

end OTSelector.Reconstruction

end
end
