import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic

/-!
# Vanishing of the de-Poissonization error

After division by the sample size, the count-stability error of the marked
Poisson pressure is

`4 (C q n ^ (2/q) + |t| G) n ^ (-1/2)
   = 4 C q n ^ (2/q - 1/2) + 4 |t| G n ^ (-1/2)`,

which vanishes as `n → ∞` whenever `q > 4`.
-/

open Filter
open scoped Topology

noncomputable section
namespace OTSelector.Probability

/-- The de-Poissonization error bound vanishes for `q > 4`. -/
theorem tendsto_dePoissonError_zero {q : ℕ} (hq : 4 < q) (C G t : ℝ) :
    Tendsto (fun n : ℕ =>
      4 * ((n : ℝ) ^ (2 / (q : ℝ)) * (C * (q : ℝ)) + |t| * G) *
        (n : ℝ) ^ (-(1 / 2 : ℝ))) atTop (𝓝 0) := by
  have hq0 : 0 < q := by omega
  have hqR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq0
  have hq4R : (4 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  -- The two exponents are negative.
  have ha : 2 / (q : ℝ) - 1 / 2 < 0 := by
    have hlt : 2 / (q : ℝ) < 1 / 2 := by
      rw [div_lt_iff₀ hqR]
      nlinarith
    linarith
  have hb : (0 : ℝ) < 1 / 2 := by norm_num
  have h1 : Tendsto (fun n : ℕ => (n : ℝ) ^ (2 / (q : ℝ) - 1 / 2)) atTop (𝓝 0) := by
    have hpos : 0 < -(2 / (q : ℝ) - 1 / 2) := by linarith
    have h := (tendsto_rpow_neg_atTop hpos).comp tendsto_natCast_atTop_atTop
    convert h using 1
    funext n
    simp only [Function.comp_apply, neg_neg]
  have h2 : Tendsto (fun n : ℕ => (n : ℝ) ^ (-(1 / 2 : ℝ))) atTop (𝓝 0) := by
    have h := (tendsto_rpow_neg_atTop hb).comp tendsto_natCast_atTop_atTop
    convert h using 1
    funext n
    simp only [Function.comp_apply]
  -- Eventually the two forms agree.
  have hform : (fun n : ℕ =>
        4 * ((n : ℝ) ^ (2 / (q : ℝ)) * (C * (q : ℝ)) + |t| * G) *
          (n : ℝ) ^ (-(1 / 2 : ℝ))) =ᶠ[atTop]
      (fun n : ℕ =>
        4 * C * (q : ℝ) * (n : ℝ) ^ (2 / (q : ℝ) - 1 / 2) +
          4 * |t| * G * (n : ℝ) ^ (-(1 / 2 : ℝ))) := by
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    have hnR : (0 : ℝ) < (n : ℝ) := by
      exact_mod_cast (Nat.lt_of_lt_of_le Nat.zero_lt_one hn)
    rw [show (n : ℝ) ^ (2 / (q : ℝ) - 1 / 2) =
        (n : ℝ) ^ (2 / (q : ℝ)) * (n : ℝ) ^ (-(1 / 2 : ℝ)) from by
      rw [← Real.rpow_add hnR]
      congr 1]
    ring
  have hlim : Tendsto (fun n : ℕ =>
      4 * C * (q : ℝ) * (n : ℝ) ^ (2 / (q : ℝ) - 1 / 2) +
        4 * |t| * G * (n : ℝ) ^ (-(1 / 2 : ℝ))) atTop (𝓝 0) := by
    have := (h1.const_mul (4 * C * (q : ℝ))).add (h2.const_mul (4 * |t| * G))
    simpa only [mul_zero, add_zero] using this
  exact hlim.congr' hform.symm

end OTSelector.Probability
