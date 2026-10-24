import LeanLevy.RandomMeasure.PoissonRandomMeasure
import Mathlib.Analysis.MeanInequalities
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Probability.Distributions.Binomial
import Mathlib.Probability.Distributions.Poisson.PoissonLimitThm
import Mathlib.Probability.Moments.Variance
import OTSelector.Probability.BinomialPoissonExpectation

/-!
Conditions: The genuine natural binomial law with p∈[0,1] and any natural sample size.

Objects: Exact first/factorial-second/variance sums and mean absolute centered deviation≤sqrt(np).

Proof detail: Shift finite binomial coefficients to compute the first two factorial moments, expand the variance to np(1−p) and apply the finite weighted Cauchy-Schwarz inequality.

References: Gunter Last; Mathew Penrose: Section 1.1, equations (1.1)–(1.3), p. 1, and descending factorial definition (1.6), p. 2; Rick Durrett: Section 1.6.1, Theorem 1.6.3, p. 29.
Relation: The standard binomial pmf supplies the distribution; moment recursions and the displayed absolute-deviation bound are computed locally, including endpoint parameters.
-/


/-!
# Mean absolute deviation of the binomial law

The first and second factorial moments of `Bin(n, p)` are computed from the
finite mass sums.  Cauchy–Schwarz then bounds the mean absolute deviation of the
count from its mean `n p` by `sqrt (n p)`.  This is the count-concentration input
for replacing multinomial cell counts by their means in the tile pressure
comparison.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal unitInterval Topology

noncomputable section
namespace OTSelector.Probability

/-- The shift identity for the binomial mass. -/
theorem binomialMass_succ_mul (m : ℕ) (p : I) (k : ℕ) :
    binomialMass (m + 1) p (k + 1) * ((k : ℝ) + 1) =
      (((m : ℝ) + 1) * (p : ℝ)) * binomialMass m p k := by
  unfold binomialMass
  by_cases hk : k ≤ m
  · have hsub : m + 1 - (k + 1) = m - k := by omega
    have hch : (↑((m + 1).choose (k + 1)) : ℝ) * ((k : ℝ) + 1) =
        ((m : ℝ) + 1) * (↑(m.choose k) : ℝ) := by
      exact_mod_cast (Nat.add_one_mul_choose_eq m k).symm
    rw [hsub, pow_succ]
    rw [show (↑((m + 1).choose (k + 1)) * (↑p ^ k * ↑p) * (1 - ↑p) ^ (m - k)) *
          ((k : ℝ) + 1)
        = ((↑((m + 1).choose (k + 1)) * ((k : ℝ) + 1)) *
            ((↑p ^ k * ↑p) * (1 - ↑p) ^ (m - k))) from by ring]
    rw [hch]
    ring
  · have hkm : m < k := by omega
    have hk' : m + 1 < k + 1 := by omega
    rw [Nat.choose_eq_zero_of_lt hkm, Nat.choose_eq_zero_of_lt hk']
    ring

/-- The first moment of the binomial law. -/
theorem integral_binomial_id (n : ℕ) (p : I) :
    ∫ k : ℕ, (k : ℝ) ∂(ProbabilityTheory.binomial n p) = (n : ℝ) * (p : ℝ) := by
  rw [integral_binomial_real]
  induction n with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ']
    simp only [Nat.cast_zero, mul_zero, add_zero]
    calc ∑ k ∈ Finset.range (m + 1),
          binomialMass (m + 1) p (k + 1) * ((k + 1 : ℕ) : ℝ)
        = ∑ k ∈ Finset.range (m + 1),
            (((m : ℝ) + 1) * (p : ℝ)) * binomialMass m p k := by
          apply Finset.sum_congr rfl
          intro k _
          have hcast : ((k + 1 : ℕ) : ℝ) = (k : ℝ) + 1 := by push_cast; ring
          rw [hcast]
          exact binomialMass_succ_mul m p k
      _ = (((m : ℝ) + 1) * (p : ℝ)) *
            ∑ k ∈ Finset.range (m + 1), binomialMass m p k := by
          rw [Finset.mul_sum]
      _ = (((m : ℝ) + 1) * (p : ℝ)) := by
          rw [binomialMass_sum_one, mul_one]
      _ = ((m + 1 : ℕ) : ℝ) * (p : ℝ) := by push_cast; ring

/-- The finite mass sum of the identity. -/
theorem binomialMass_sum_mul (n : ℕ) (p : I) :
    ∑ k ∈ Finset.range (n + 1), binomialMass n p k * (k : ℝ) =
      (n : ℝ) * (p : ℝ) := by
  have h := integral_binomial_id n p
  rwa [integral_binomial_real] at h

/-- The second factorial moment of the binomial law. -/
theorem integral_binomial_factorial (n : ℕ) (p : I) :
    ∫ k : ℕ, ((k : ℝ) * ((k : ℝ) - 1)) ∂(ProbabilityTheory.binomial n p) =
      (n : ℝ) * ((n : ℝ) - 1) * (p : ℝ) ^ 2 := by
  rw [integral_binomial_real]
  induction n with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ']
    simp only [Nat.cast_zero, zero_mul, mul_zero, add_zero]
    calc ∑ k ∈ Finset.range (m + 1),
          binomialMass (m + 1) p (k + 1) *
            (((k + 1 : ℕ) : ℝ) * (((k + 1 : ℕ) : ℝ) - 1))
        = ∑ k ∈ Finset.range (m + 1),
            (((m : ℝ) + 1) * (p : ℝ)) * (binomialMass m p k * (k : ℝ)) := by
          apply Finset.sum_congr rfl
          intro k _
          have hcast : (((k + 1 : ℕ) : ℝ) * (((k + 1 : ℕ) : ℝ) - 1)) =
              ((k : ℝ) + 1) * (k : ℝ) := by push_cast; ring
          rw [hcast, ← mul_assoc, binomialMass_succ_mul, mul_assoc]
      _ = (((m : ℝ) + 1) * (p : ℝ)) *
            ∑ k ∈ Finset.range (m + 1), binomialMass m p k * (k : ℝ) := by
          rw [Finset.mul_sum]
      _ = (((m : ℝ) + 1) * (p : ℝ)) * ((m : ℝ) * (p : ℝ)) := by
          have h := integral_binomial_id m p
          rw [integral_binomial_real] at h
          rw [h]
      _ = ((m + 1 : ℕ) : ℝ) * (((m + 1 : ℕ) : ℝ) - 1) * (p : ℝ) ^ 2 := by
          push_cast; ring

/-- The finite mass sum of the factorial moment `k(k-1)`. -/
theorem binomialMass_sum_factorial (n : ℕ) (p : I) :
    ∑ k ∈ Finset.range (n + 1), binomialMass n p k * ((k : ℝ) * ((k : ℝ) - 1)) =
      (n : ℝ) * ((n : ℝ) - 1) * (p : ℝ) ^ 2 := by
  have h := integral_binomial_factorial n p
  rwa [integral_binomial_real] at h

/-- Sum form of the variance. -/
theorem binomialMass_sum_variance (n : ℕ) (p : I) :
    ∑ k ∈ Finset.range (n + 1),
        binomialMass n p k * ((k : ℝ) - (n : ℝ) * (p : ℝ)) ^ 2 =
      (n : ℝ) * (p : ℝ) * (1 - (p : ℝ)) := by
  set μ : ℝ := (n : ℝ) * (p : ℝ) with hμ
  have hexp : ∀ k : ℕ, binomialMass n p k * ((k : ℝ) - μ) ^ 2 =
      binomialMass n p k * ((k : ℝ) * ((k : ℝ) - 1)) +
        (1 - 2 * μ) * (binomialMass n p k * (k : ℝ)) + μ ^ 2 * binomialMass n p k := by
    intro k
    ring
  simp_rw [hexp]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
    binomialMass_sum_factorial, binomialMass_sum_mul, binomialMass_sum_one, hμ]
  ring

/-- **Mean absolute deviation of the binomial law, finite-sum form.** -/
theorem binomialMass_sum_abs_sub_mean_le (n : ℕ) (p : I) :
    ∑ k ∈ Finset.range (n + 1),
        binomialMass n p k * |(k : ℝ) - (n : ℝ) * (p : ℝ)| ≤
      Real.sqrt ((n : ℝ) * (p : ℝ)) := by
  set μ : ℝ := (n : ℝ) * (p : ℝ) with hμ
  have hμ0 : 0 ≤ μ := mul_nonneg (Nat.cast_nonneg n) p.2.1
  have hmass0 : ∀ k, 0 ≤ binomialMass n p k := binomialMass_nonneg n p
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (s := Finset.range (n + 1))
    (f := fun k => Real.sqrt (binomialMass n p k))
    (g := fun k => Real.sqrt (binomialMass n p k) * |(k : ℝ) - μ|)
  have hleft : ∑ k ∈ Finset.range (n + 1),
      Real.sqrt (binomialMass n p k) *
        (Real.sqrt (binomialMass n p k) * |(k : ℝ) - μ|) =
      ∑ k ∈ Finset.range (n + 1), binomialMass n p k * |(k : ℝ) - μ| := by
    apply Finset.sum_congr rfl
    intro k _
    rw [← mul_assoc, Real.mul_self_sqrt (hmass0 k)]
  have hf2 : ∑ k ∈ Finset.range (n + 1),
      Real.sqrt (binomialMass n p k) ^ 2 = 1 := by
    calc ∑ k ∈ Finset.range (n + 1), Real.sqrt (binomialMass n p k) ^ 2
        = ∑ k ∈ Finset.range (n + 1), binomialMass n p k := by
          apply Finset.sum_congr rfl
          intro k _
          rw [Real.sq_sqrt (hmass0 k)]
      _ = 1 := binomialMass_sum_one n p
  have hg2 : ∑ k ∈ Finset.range (n + 1),
      (Real.sqrt (binomialMass n p k) * |(k : ℝ) - μ|) ^ 2 =
      ∑ k ∈ Finset.range (n + 1), binomialMass n p k * ((k : ℝ) - μ) ^ 2 := by
    apply Finset.sum_congr rfl
    intro k _
    rw [mul_pow, Real.sq_sqrt (hmass0 k), sq_abs]
  have hvar : ∑ k ∈ Finset.range (n + 1),
      binomialMass n p k * ((k : ℝ) - μ) ^ 2 = μ * (1 - (p : ℝ)) := by
    have h := binomialMass_sum_variance n p
    simpa only [hμ] using h
  have hsum0 : 0 ≤ ∑ k ∈ Finset.range (n + 1),
      binomialMass n p k * |(k : ℝ) - μ| :=
    Finset.sum_nonneg fun k _ => mul_nonneg (hmass0 k) (abs_nonneg _)
  have hsq : (∑ k ∈ Finset.range (n + 1),
      binomialMass n p k * |(k : ℝ) - μ|) ^ 2 ≤ μ := by
    calc (∑ k ∈ Finset.range (n + 1),
          binomialMass n p k * |(k : ℝ) - μ|) ^ 2
        = (∑ k ∈ Finset.range (n + 1),
            Real.sqrt (binomialMass n p k) *
              (Real.sqrt (binomialMass n p k) * |(k : ℝ) - μ|)) ^ 2 := by rw [hleft]
      _ ≤ (∑ k ∈ Finset.range (n + 1), Real.sqrt (binomialMass n p k) ^ 2) *
            ∑ k ∈ Finset.range (n + 1),
              (Real.sqrt (binomialMass n p k) * |(k : ℝ) - μ|) ^ 2 := hcs
      _ = μ * (1 - (p : ℝ)) := by rw [hf2, hg2, hvar, one_mul]
      _ ≤ μ := by
          have hp1 : (1 : ℝ) - (p : ℝ) ≤ 1 := by linarith [p.2.1]
          calc μ * (1 - (p : ℝ)) ≤ μ * 1 :=
                mul_le_mul_of_nonneg_left hp1 hμ0
            _ = μ := mul_one μ
  calc ∑ k ∈ Finset.range (n + 1), binomialMass n p k * |(k : ℝ) - μ|
      = Real.sqrt ((∑ k ∈ Finset.range (n + 1),
          binomialMass n p k * |(k : ℝ) - μ|) ^ 2) := by
        rw [Real.sqrt_sq hsum0]
    _ ≤ Real.sqrt μ := Real.sqrt_le_sqrt hsq
    _ = Real.sqrt ((n : ℝ) * (p : ℝ)) := by rw [hμ]

/-- **Mean absolute deviation of the binomial law.** -/
theorem integral_abs_binomial_sub_mean_le (n : ℕ) (p : I) :
    ∫ k : ℕ, |(k : ℝ) - (n : ℝ) * (p : ℝ)| ∂(ProbabilityTheory.binomial n p) ≤
      Real.sqrt ((n : ℝ) * (p : ℝ)) := by
  rw [integral_binomial_real]
  exact binomialMass_sum_abs_sub_mean_le n p

end OTSelector.Probability
