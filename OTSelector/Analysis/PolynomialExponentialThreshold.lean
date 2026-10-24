import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import OTSelector.Analysis.PolynomialExponentialSquareRootDecay

/-!
## Lemma skeleton

* **Conditions:** A nonnegative integrable family with one polynomial-exponential mean bound and nonnegative growth rate.
* **Objects:** One threshold K = rate + 1 with vanishing means.
* **Proof detail:** Choose the threshold, invoke the polynomial-exponential decay lemma and squeeze the means.

## Mathematical sources

* Terence Tao, *Analysis I*, Section 7.5, Corollary 7.5.3 (ratio test).
  https://github.com/teorth/analysis/blob/main/Analysis/Section_7_5.lean
* Terence Tao, *Analysis I*, Section 6.4, Corollaries 6.4.14 (squeeze test) and 6.4.17 (zero test).
  https://github.com/teorth/analysis/blob/main/Analysis/Section_6_4.lean

**Relationship to the sources:** The rate margin, fourth-moment prefactor and uniform threshold wrapper are explicitly derived here.
-/

/-! # One threshold for polynomially growing bad-event moments

A common rate estimate is a polynomial square-root prefactor times
`exp (-(K - rate) * n / 2)`. Choosing `K = rate + 1` makes this integrable
nonnegative family vanish in mean. Geometry and the choice of the bad event are
left to the caller.

## Mathematical source

Terence Tao, *Analysis I*, §6.4, Corollaries 6.4.14 and 6.4.17 (squeeze and zero
tests), together with §7.5, Corollary 7.5.3 (ratio test). For a polynomial times
`exp (-n / 2)`, the ratio of successive terms tends to `exp (-1 / 2) < 1`.
The square-root fourth-moment prefactor and the choice `K = rate + 1` are algebraic
corollaries implemented here; they are not a verbatim theorem from the book.
Author's statement-number companion: https://github.com/teorth/analysis .

-/

open MeasureTheory Filter
open scoped Topology

namespace OTSelector.Analysis

/-- Choose one threshold above the growth rate and squeeze the resulting means to zero. -/
theorem exists_threshold_mean_tendsto_zero
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (q : ℕ) {C v r rate : ℝ} (hC : 0 ≤ C) (hr : 0 ≤ r) (hrate : 0 ≤ rate)
    (f : ℝ → ℕ → Ω → ℝ) (hpos : ∀ K n s, 0 ≤ f K n s)
    (hbound : ∀ K n, 1 ≤ n → Integrable (f K n) μ ∧
      (∫ s, f K n s ∂μ) ≤
        (C * (1 + ((2 * (n : ℝ) + r) ^ q * v) ^ 4)) ^ (1 / 2 : ℝ) *
          Real.exp ((-(K - rate) * (n : ℝ)) * (1 / 2 : ℝ))) :
    ∃ K : ℝ, 0 < K ∧ (∀ n, 1 ≤ n → Integrable (f K n) μ) ∧
      Tendsto (fun n ↦ ∫ s, f K n s ∂μ) atTop (𝓝 0) := by
  let K := rate + 1
  have hrate' : K - rate = 1 := by dsimp only [K]; ring
  have hdecay := Probability.tendsto_polynomialFourthRoot_exp_neg_half_nat
    q (v := v) hC hr
  refine ⟨K, by dsimp only [K]; linarith, fun n hn ↦ (hbound K n hn).1, ?_⟩
  apply squeeze_zero' (Eventually.of_forall fun n ↦ integral_nonneg (hpos K n)) _ hdecay
  filter_upwards [eventually_ge_atTop 1] with n hn
  have h := (hbound K n hn).2
  rw [hrate'] at h
  simpa only [neg_one_mul, div_eq_mul_inv, one_mul] using h

end OTSelector.Analysis
