import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Probability.PolynomialFourthRootExponentialSummability.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Probability.PolynomialFourthRootExponentialSummability`; the selected original proof blocks follow. -/
section

/-!
# Probability.PolynomialFourthRootExponentialSummability

**Conditions:** Fixed natural polynomial degree and the stated nonnegative constants for the displayed bound; the tail limit uses the corresponding summable sequence.

**Objects:** Polynomial fourth-moment square-root factors multiplied by exp(−n/2), and shifted infinite tails.

**Proof detail:** Bound the square-root expression by a fixed polynomial, apply polynomial-times-geometric summability and then the vanishing-tail theorem for convergent series.

**Sources:** [Terence Tao, Analysis I](https://github.com/teorth/analysis/blob/main/Analysis/Section_7_5.lean), Section 7.5, Corollary 7.5.3 (ratio test); [Terence Tao, Analysis I](https://github.com/teorth/analysis/blob/main/Analysis/Section_7_1.lean), Sections 4.3 (absolute value) and 7.1 (finite series), in particular Proposition 7.1.11; [Terence Tao, Analysis I](https://github.com/teorth/analysis/blob/main/Analysis/Section_6_4.lean), Section 6.4, Corollaries 6.4.14 (squeeze test) and 6.4.17 (zero test).

Source relation (corollary): The cited sections provide the stated mathematical foundations; the exact finite construction and quantitative bound in this module are local consequences, not a claim that the book states the Lean theorem verbatim.
-/

/-! # Summable tails of the exact polynomial fourth-moment bad-event bound -/
open Filter Topology
noncomputable section
namespace OTSelector.Probability
set_option maxHeartbeats 700000

/-- The existing explicit envelope mean-square bound is summable, so it also
controls errors at a random integer scale through a deterministic tail sum. -/
theorem summable_polynomialFourthRoot_exp_neg_half_nat
    (q : ℕ) {C v r : ℝ} (hC : 0 ≤ C) (hr : 0 ≤ r) :
    Summable (fun n : ℕ ↦
      (C * (1 + ((2 * (n : ℝ) + r) ^ q * v) ^ 4)) ^ (1 / 2 : ℝ) *
        Real.exp (-(n : ℝ) / 2)) := by
  have he : Summable (fun n : ℕ ↦ Real.exp (-(n : ℝ) / 2)) := by
    exact (Real.summable_exp_nat_mul_iff.mpr
      (by norm_num : -(1 / 2 : ℝ) < 0)).congr (fun n ↦ by congr 1; ring)
  have hp : Summable (fun n : ℕ ↦
      ((n : ℝ) + 1) ^ (2 * q) * Real.exp (-(n : ℝ) / 2)) := by
    have h : Summable (fun n : ℕ ↦ Real.exp (1 / 2) *
        (((n + 1 : ℕ) : ℝ) ^ (2 * q) *
          Real.exp (-(1 / 2 : ℝ) * ((n + 1 : ℕ) : ℝ)))) :=
      ((summable_nat_add_iff 1).2
        (Real.summable_pow_mul_exp_neg_nat_mul (2 * q)
          (r := 1 / 2) (by norm_num))).mul_left _
    apply h.congr
    intro n
    rw [Nat.cast_add, Nat.cast_one]
    have hexp : Real.exp (-(n : ℝ) / 2) =
        Real.exp (1 / 2) * Real.exp (-(1 / 2 : ℝ) * ((n : ℝ) + 1)) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [hexp]
    ring
  let b : ℕ → ℝ := fun n ↦ Real.sqrt C *
    (Real.exp (-(n : ℝ) / 2) +
      (v ^ 2 * (2 + r) ^ (2 * q)) *
        (((n : ℝ) + 1) ^ (2 * q) * Real.exp (-(n : ℝ) / 2)))
  have hb : Summable b := (he.add (hp.mul_left (v ^ 2 * (2 + r) ^ (2 * q)))).mul_left _
  apply hb.of_nonneg_of_le (fun n ↦ by positivity)
  intro n
  let R := 2 * (n : ℝ) + r
  let x := R ^ q * v
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hs : Real.sqrt (C * (1 + x ^ 4)) ≤ Real.sqrt C * (1 + x ^ 2) := by
    rw [Real.sqrt_mul hC]
    apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg _)
    apply Real.sqrt_le_iff.mpr
    refine ⟨by positivity, ?_⟩
    nlinarith [sq_nonneg x]
  have hRle : R ≤ (2 + r) * ((n : ℝ) + 1) := by
    dsimp [R]
    nlinarith [mul_nonneg hr (Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  have hx : x ^ 2 ≤ v ^ 2 * (2 + r) ^ (2 * q) * ((n : ℝ) + 1) ^ (2 * q) := by
    have hpow := pow_le_pow_left₀ hR hRle (2 * q)
    dsimp [x]
    rw [mul_pow, ← pow_mul, Nat.mul_comm q 2]
    calc
      _ ≤ ((2 + r) * ((n : ℝ) + 1)) ^ (2 * q) * v ^ 2 :=
        mul_le_mul_of_nonneg_right hpow (sq_nonneg v)
      _ = _ := by rw [mul_pow]; ring
  change (C * (1 + x ^ 4)) ^ (1 / 2 : ℝ) * Real.exp (-(n : ℝ) / 2) ≤ b n
  rw [← Real.sqrt_eq_rpow]
  calc
    _ ≤ (Real.sqrt C * (1 + x ^ 2)) * Real.exp (-(n : ℝ) / 2) :=
      mul_le_mul_of_nonneg_right hs (Real.exp_nonneg _)
    _ ≤ (Real.sqrt C * (1 + v ^ 2 * (2 + r) ^ (2 * q) *
        ((n : ℝ) + 1) ^ (2 * q))) * Real.exp (-(n : ℝ) / 2) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (by linarith [hx]) (Real.sqrt_nonneg C))
        (Real.exp_nonneg _)
    _ = b n := by dsimp only [b]; ring

/-- Tails of the same explicit summable envelope bound vanish. -/
theorem tendsto_tsum_polynomialFourthRoot_exp_neg_half_nat
    (q : ℕ) (C v r : ℝ) :
    Tendsto (fun N : ℕ ↦ ∑' n : ℕ,
      (C * (1 + ((2 * ((n + N : ℕ) : ℝ) + r) ^ q * v) ^ 4)) ^ (1 / 2 : ℝ) *
        Real.exp (-((n + N : ℕ) : ℝ) / 2)) atTop (𝓝 0) :=
  tendsto_sum_nat_add (fun n : ℕ ↦
    (C * (1 + ((2 * (n : ℝ) + r) ^ q * v) ^ 4)) ^ (1 / 2 : ℝ) *
      Real.exp (-(n : ℝ) / 2))

end OTSelector.Probability

end
end
