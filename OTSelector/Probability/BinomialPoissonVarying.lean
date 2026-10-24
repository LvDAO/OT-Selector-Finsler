import LeanLevy.RandomMeasure.PoissonRandomMeasure
import Mathlib.Analysis.MeanInequalities
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Probability.Distributions.Binomial
import Mathlib.Probability.Distributions.Poisson.PoissonLimitThm
import Mathlib.Probability.Moments.Variance
import OTSelector.Probability.BinomialDeviation
import OTSelector.Probability.BinomialPoissonExpectation

/-!
Conditions: Bounded-intensity binomial counts np_n→r, a limiting two-count functional with linear minimum-count growth and varying functionals whose minimum-count-weighted uniform error tends to zero.

Objects: Expectation convergence from the varying binomial pair readout to the genuine Poisson-pair series readout.

Proof detail: Bound the varying-vs-fixed functional mixture error by δ_n np_n, then apply the established fixed-functional binomial-to-Poisson expectation limit.

References: Gunter Last; Mathew Penrose: Section 1.3, Proposition 1.4, pp. 4–5; Section 3.3, Theorem 3.9, pp. 23–24; Gunter Last; Mathew Penrose: Section 1.1, equations (1.1)–(1.3), p. 1, and descending factorial definition (1.6), p. 2.
Relation: A controlled changing-functional Poissonization adapter. Pointwise convergence without the supplied weighted uniform error would not justify this conclusion.
-/


/-! Bounded-intensity Poissonization when the physical finite-cloud functional
also changes with sample size, as it does on rounded microscopic grids. -/
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal Topology unitInterval
noncomputable section
namespace OTSelector.Probability

def binomialPairExpectation (n : ℕ) (p : I) (F : ℕ → ℕ → ℝ) : ℝ :=
  ∑ m ∈ Finset.range (n + 1), ∑ k ∈ Finset.range (n + 1),
    binomialMass n p m * binomialMass n p k * F m k

/-- A finite-cloud perturbation bounded per matched point costs only the
original binomial mean, uniformly in the number of observations. -/
theorem binomialPairExpectation_abs_sub_le (n : ℕ) (p : I)
    (F G : ℕ → ℕ → ℝ) {δ : ℝ} (hδ : 0 ≤ δ)
    (hFG : ∀ m k, |F m k - G m k| ≤ δ * ((min m k : ℕ) : ℝ)) :
    |binomialPairExpectation n p F - binomialPairExpectation n p G| ≤
      δ * ((n : ℝ) * (p : ℝ)) := by
  classical
  have hsum : binomialPairExpectation n p F - binomialPairExpectation n p G =
      ∑ m ∈ Finset.range (n + 1), ∑ k ∈ Finset.range (n + 1),
        binomialMass n p m * binomialMass n p k * (F m k - G m k) := by
    simp only [binomialPairExpectation, mul_sub, Finset.sum_sub_distrib]
  rw [hsum]
  calc
    _ ≤ ∑ m ∈ Finset.range (n + 1), ∑ k ∈ Finset.range (n + 1),
        binomialMass n p m * binomialMass n p k * (δ * (m : ℝ)) := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun m _ ↦ ?_)
      refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k _ ↦ ?_)
      rw [abs_mul, abs_of_nonneg (mul_nonneg (binomialMass_nonneg n p m)
        (binomialMass_nonneg n p k))]
      apply mul_le_mul_of_nonneg_left _
        (mul_nonneg (binomialMass_nonneg n p m) (binomialMass_nonneg n p k))
      exact (hFG m k).trans (mul_le_mul_of_nonneg_left
        (Nat.cast_le.mpr (Nat.min_le_left m k)) hδ)
    _ = δ * ((n : ℝ) * (p : ℝ)) := by
      have hrow (m : ℕ) : (∑ k ∈ Finset.range (n + 1),
          binomialMass n p m * binomialMass n p k * (δ * (m : ℝ))) =
          δ * (binomialMass n p m * (m : ℝ)) := by
        calc
          _ = (δ * (binomialMass n p m * (m : ℝ))) *
              ∑ k ∈ Finset.range (n + 1), binomialMass n p k := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro k _
            ring
          _ = _ := by rw [binomialMass_sum_one, mul_one]
      simp_rw [hrow]
      rw [← Finset.mul_sum, binomialMass_sum_mul]

/-- Rounding and other vanishing per-edge perturbations can be retained while
passing from the original two independent binomial counts to the Poisson law. -/
theorem tendsto_two_count_binomial_poisson_varying
    (F : ℕ → ℕ → ℕ → ℝ) (G : ℕ → ℕ → ℝ) {B : ℝ} (hB : 0 ≤ B)
    (hG : ∀ m k, |G m k| ≤ B * ((min m k : ℕ) : ℝ))
    (δ : ℕ → ℝ) (hδ : ∀ n, 0 ≤ δ n) (hδlim : Tendsto δ atTop (𝓝 0))
    (hFG : ∀ n m k, |F n m k - G m k| ≤ δ n * ((min m k : ℕ) : ℝ))
    (p : ℕ → I) (r : ℝ≥0)
    (hr : Tendsto (fun n : ℕ ↦ (n : ℝ) * (p n : ℝ)) atTop (𝓝 (r : ℝ))) :
    Tendsto (fun n ↦ binomialPairExpectation n (p n) (F n)) atTop
      (𝓝 (∑' m, poissonMass r m * ∑' k, poissonMass r k * G m k)) := by
  have herr : Tendsto (fun n ↦ δ n * ((n : ℝ) * (p n : ℝ))) atTop (𝓝 0) := by
    simpa only [zero_mul] using hδlim.mul hr
  have hdiff : Tendsto
      (fun n ↦ binomialPairExpectation n (p n) (F n) - binomialPairExpectation n (p n) G)
      atTop (𝓝 0) := by
    apply squeeze_zero_norm _ herr
    intro n
    rw [Real.norm_eq_abs]
    exact binomialPairExpectation_abs_sub_le n (p n) (F n) G (hδ n) (hFG n)
  have hfixed := tendsto_two_count_binomial_poisson G hB hG p r hr
  simpa only [binomialPairExpectation, sub_add_cancel, zero_add] using hdiff.add hfixed

end OTSelector.Probability
