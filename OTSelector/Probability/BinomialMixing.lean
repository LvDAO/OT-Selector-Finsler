import LeanLevy.RandomMeasure.PoissonRandomMeasure
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Probability.Distributions.Binomial
import Mathlib.Probability.Distributions.Poisson.PoissonLimitThm
import Mathlib.Probability.Moments.Variance
import Mathlib.Topology.Algebra.Order.Floor
import OTSelector.Probability.BinomialDeviation
import OTSelector.Probability.BinomialPoissonExpectation

/-!
Conditions: Two genuine independent Bin(n,w) counts, a two-count Lipschitz functional with a supplied diagonal normalized limit and w>0; the scale-varying version additionally supplies its explicit vanishing Lipschitz error.

Objects: The normalized binomial mixture converges to w times the diagonal limit, including the stated changing-scale functional.

Proof detail: Compare both random counts with floor(nw), bound the expected Lipschitz change by their true mean absolute deviations plus rounding, and combine floor(nw)/n→w with the supplied diagonal limit.

References: Gunter Last; Mathew Penrose: Section 1.1, equations (1.1)–(1.3), p. 1, and descending factorial definition (1.6), p. 2; Rick Durrett: Section 1.6.1, Theorem 1.6.3, p. 29.
Relation: A local mean-count replacement theorem. The diagonal limit is an explicit input and the changing-scale version requires its own vanishing-error premise.
-/


/-!
# Binomial mixing of a Lipschitz functional with a diagonal limit

Let `E : ℕ → ℕ → ℝ` be Lipschitz in the two counts and suppose that the diagonal
values satisfy `E N N / N → p`.  Then the averages of `E` under two independent
`Bin(n, w)` counts, divided by `n`, converge to `w p`.

The proof compares the random counts with `N = ⌊n w⌋` using the Lipschitz bound,
then uses the binomial mean absolute deviation `E |count − n w| ≤ sqrt (n w)` and
`N / n → w`.  This is the count-concentration step replacing the random cell
counts of the physical sample by the deterministic intensity of the marked
model.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal unitInterval Topology

noncomputable section
namespace OTSelector.Probability

/-- The weighted deviation of a binomial count from a deterministic index. -/
theorem binomialMass_sum_abs_sub_index_le (n : ℕ) (w : I) (N : ℕ) :
    ∑ k ∈ Finset.range (n + 1),
        binomialMass n w k * |(k : ℝ) - (N : ℝ)| ≤
      Real.sqrt ((n : ℝ) * (w : ℝ)) + |(n : ℝ) * (w : ℝ) - (N : ℝ)| := by
  have hsum1 : ∑ k ∈ Finset.range (n + 1), binomialMass n w k = 1 :=
    binomialMass_sum_one n w
  have hnonneg (k : ℕ) : 0 ≤ binomialMass n w k := binomialMass_nonneg n w k
  calc ∑ k ∈ Finset.range (n + 1), binomialMass n w k * |(k : ℝ) - (N : ℝ)|
      ≤ ∑ k ∈ Finset.range (n + 1), binomialMass n w k *
          (|(k : ℝ) - (n : ℝ) * (w : ℝ)| + |(n : ℝ) * (w : ℝ) - (N : ℝ)|) := by
        apply Finset.sum_le_sum
        intro k _
        apply mul_le_mul_of_nonneg_left _ (hnonneg k)
        calc |(k : ℝ) - (N : ℝ)|
            = |((k : ℝ) - (n:ℝ) * (w:ℝ)) + ((n:ℝ) * (w:ℝ) - (N : ℝ))| := by
              congr 1
              ring
          _ ≤ |(k : ℝ) - (n : ℝ) * (w : ℝ)| + |(n : ℝ) * (w : ℝ) - (N : ℝ)| :=
              abs_add_le _ _
    _ = (∑ k ∈ Finset.range (n + 1),
            binomialMass n w k * |(k : ℝ) - (n : ℝ) * (w : ℝ)|) +
          (∑ k ∈ Finset.range (n + 1), binomialMass n w k) *
            |(n : ℝ) * (w : ℝ) - (N : ℝ)| := by
        simp only [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul]
    _ ≤ Real.sqrt ((n : ℝ) * (w : ℝ)) + 1 * |(n : ℝ) * (w : ℝ) - (N : ℝ)| := by
        have h1 := binomialMass_sum_abs_sub_mean_le n w
        have h2 : (∑ k ∈ Finset.range (n + 1), binomialMass n w k) *
            |(n : ℝ) * (w : ℝ) - (N : ℝ)| =
            1 * |(n : ℝ) * (w : ℝ) - (N : ℝ)| := by rw [hsum1]
        rw [h2]
        exact add_le_add h1 le_rfl
    _ = Real.sqrt ((n : ℝ) * (w : ℝ)) + |(n : ℝ) * (w : ℝ) - (N : ℝ)| := by ring

/-- **Binomial mixing of a Lipschitz two-count functional.** -/
theorem tendsto_binomial_double_sum_of_lipschitz
    (E : ℕ → ℕ → ℝ) {C p : ℝ} (hC : 0 ≤ C)
    (hE : ∀ m k m' k',
      |E m k - E m' k'| ≤ C * (|(m : ℝ) - (m' : ℝ)| + |(k : ℝ) - (k' : ℝ)|))
    (hdiag : Tendsto (fun N : ℕ => E N N / (N : ℝ)) atTop (𝓝 p))
    (w : I) (hw : 0 < (w : ℝ)) :
    Tendsto (fun n : ℕ =>
      (∑ m ∈ Finset.range (n + 1), ∑ k ∈ Finset.range (n + 1),
        binomialMass n w m * binomialMass n w k * E m k) / (n : ℝ))
      atTop (𝓝 ((w : ℝ) * p)) := by
  classical
  set μ : ℕ → ℝ := fun n => (n : ℝ) * (w : ℝ) with hμ
  set N : ℕ → ℕ := fun n => Nat.floor (μ n) with hN
  have hμtop : Tendsto μ atTop atTop := by
    have h3 : Tendsto (fun x : ℝ => (w : ℝ) * x) atTop atTop :=
      Tendsto.const_mul_atTop hw tendsto_id
    have h4 : Tendsto (fun n : ℕ => (w : ℝ) * (n : ℝ)) atTop atTop :=
      h3.comp tendsto_natCast_atTop_atTop
    simpa only [hμ, mul_comm] using h4
  have hNtop : Tendsto N atTop atTop := tendsto_nat_floor_atTop.comp hμtop
  have hdiagN : Tendsto (fun n : ℕ => E (N n) (N n) / (N n : ℝ)) atTop (𝓝 p) :=
    hdiag.comp hNtop
  have hNle (n : ℕ) : (N n : ℝ) ≤ μ n := Nat.floor_le (by rw [hμ]; positivity)
  have hNlt (n : ℕ) : μ n < (N n : ℝ) + 1 := Nat.lt_floor_add_one (μ n)
  have hNclose (n : ℕ) : |μ n - (N n : ℝ)| ≤ 1 := by
    have h0 : 0 ≤ μ n - (N n : ℝ) := by linarith [hNle n]
    rw [abs_of_nonneg h0]
    linarith [hNlt n]
  -- Weighted deviation from the deterministic index.
  have hdev (n : ℕ) :
      ∑ k ∈ Finset.range (n + 1),
          binomialMass n w k * |(k : ℝ) - (N n : ℝ)| ≤
        Real.sqrt (μ n) + 1 := by
    have h := binomialMass_sum_abs_sub_index_le n w (N n)
    have hμn : (n : ℝ) * (w : ℝ) = μ n := rfl
    rw [hμn] at h
    exact h.trans (add_le_add le_rfl (hNclose n))
  -- The double-sum difference from the diagonal value.
  have hdiff (n : ℕ) :
      (∑ m ∈ Finset.range (n + 1), ∑ k ∈ Finset.range (n + 1),
          binomialMass n w m * binomialMass n w k * E m k) - E (N n) (N n) =
        ∑ m ∈ Finset.range (n + 1), ∑ k ∈ Finset.range (n + 1),
          binomialMass n w m * binomialMass n w k * (E m k - E (N n) (N n)) := by
    have hsum1 : ∑ k ∈ Finset.range (n + 1), binomialMass n w k = 1 :=
      binomialMass_sum_one n w
    have hconst : (∑ m ∈ Finset.range (n + 1), ∑ k ∈ Finset.range (n + 1),
          binomialMass n w m * binomialMass n w k * E (N n) (N n)) = E (N n) (N n) := by
      have hdouble : (∑ m ∈ Finset.range (n + 1), ∑ k ∈ Finset.range (n + 1),
          binomialMass n w m * binomialMass n w k) = 1 := by
        rw [← Finset.sum_mul_sum, hsum1]; ring
      calc ∑ m ∈ Finset.range (n + 1), ∑ k ∈ Finset.range (n + 1),
            binomialMass n w m * binomialMass n w k * E (N n) (N n)
          = (∑ m ∈ Finset.range (n + 1), ∑ k ∈ Finset.range (n + 1),
              binomialMass n w m * binomialMass n w k) * E (N n) (N n) := by
            simp only [Finset.sum_mul]
        _ = E (N n) (N n) := by rw [hdouble, one_mul]
    conv_lhs => rw [← hconst]
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro m _
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro k _
    ring
  -- Bound the difference by the weighted count deviations.
  have hbound (n : ℕ) :
      |(∑ m ∈ Finset.range (n + 1), ∑ k ∈ Finset.range (n + 1),
          binomialMass n w m * binomialMass n w k * E m k) - E (N n) (N n)| ≤
        2 * C * (Real.sqrt (μ n) + 1) := by
    rw [hdiff n]
    -- Summation helpers for the row and column parts.
    have hdbl_row : ∀ (f : ℕ → ℝ),
        (∑ m ∈ Finset.range (n + 1), ∑ k ∈ Finset.range (n + 1),
            binomialMass n w m * binomialMass n w k * f m) =
          (∑ m ∈ Finset.range (n + 1), binomialMass n w m * f m) *
            (∑ k ∈ Finset.range (n + 1), binomialMass n w k) := by
      intro f
      rw [Finset.sum_mul_sum]
      apply Finset.sum_congr rfl
      intro m _
      apply Finset.sum_congr rfl
      intro k _
      ring
    have hdbl_col : ∀ (h : ℕ → ℝ),
        (∑ m ∈ Finset.range (n + 1), ∑ k ∈ Finset.range (n + 1),
            binomialMass n w m * binomialMass n w k * h k) =
          (∑ m ∈ Finset.range (n + 1), binomialMass n w m) *
            (∑ k ∈ Finset.range (n + 1), binomialMass n w k * h k) := by
      intro h
      rw [Finset.sum_mul_sum]
      apply Finset.sum_congr rfl
      intro m _
      apply Finset.sum_congr rfl
      intro k _
      ring

    have hnonneg (k : ℕ) : 0 ≤ binomialMass n w k := binomialMass_nonneg n w k
    have hsum1 : ∑ k ∈ Finset.range (n + 1), binomialMass n w k = 1 :=
      binomialMass_sum_one n w
    have hrow : (∑ m ∈ Finset.range (n + 1), ∑ k ∈ Finset.range (n + 1),
          binomialMass n w m * binomialMass n w k * |(m : ℝ) - (N n : ℝ)|) =
        ∑ m ∈ Finset.range (n + 1),
          binomialMass n w m * |(m : ℝ) - (N n : ℝ)| := by
      rw [hdbl_row, hsum1, mul_one]
    have hcol : (∑ m ∈ Finset.range (n + 1), ∑ k ∈ Finset.range (n + 1),
          binomialMass n w m * binomialMass n w k * |(k : ℝ) - (N n : ℝ)|) =
        ∑ k ∈ Finset.range (n + 1),
          binomialMass n w k * |(k : ℝ) - (N n : ℝ)| := by
      rw [hdbl_col, hsum1, one_mul]
    have hstep1 : |∑ m ∈ Finset.range (n + 1), ∑ k ∈ Finset.range (n + 1),
          binomialMass n w m * binomialMass n w k * (E m k - E (N n) (N n))| ≤
        ∑ m ∈ Finset.range (n + 1), ∑ k ∈ Finset.range (n + 1),
          binomialMass n w m * binomialMass n w k *
            (C * (|(m : ℝ) - (N n : ℝ)| + |(k : ℝ) - (N n : ℝ)|)) := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans
        (Finset.sum_le_sum fun m _ => ?_)
      refine (Finset.abs_sum_le_sum_abs _ _).trans
        (Finset.sum_le_sum fun k _ => ?_)
      rw [abs_mul, abs_of_nonneg (mul_nonneg (hnonneg m) (hnonneg k))]
      exact mul_le_mul_of_nonneg_left (hE m k (N n) (N n))
        (mul_nonneg (hnonneg m) (hnonneg k))
    have hstep2 : (∑ m ∈ Finset.range (n + 1), ∑ k ∈ Finset.range (n + 1),
          binomialMass n w m * binomialMass n w k *
            (C * (|(m : ℝ) - (N n : ℝ)| + |(k : ℝ) - (N n : ℝ)|))) ≤
        2 * C * (Real.sqrt (μ n) + 1) := by
      have hsplit : (∑ m ∈ Finset.range (n + 1), ∑ k ∈ Finset.range (n + 1),
            binomialMass n w m * binomialMass n w k *
              (C * (|(m : ℝ) - (N n : ℝ)| + |(k : ℝ) - (N n : ℝ)|))) =
          C * (∑ m ∈ Finset.range (n + 1), ∑ k ∈ Finset.range (n + 1),
              binomialMass n w m * binomialMass n w k * |(m : ℝ) - (N n : ℝ)|) +
            C * (∑ m ∈ Finset.range (n + 1), ∑ k ∈ Finset.range (n + 1),
              binomialMass n w m * binomialMass n w k * |(k : ℝ) - (N n : ℝ)|) := by
        simp only [mul_add, Finset.sum_add_distrib, Finset.mul_sum]
        congr 1
        · apply Finset.sum_congr rfl
          intro m _
          apply Finset.sum_congr rfl
          intro k _
          ring
        · apply Finset.sum_congr rfl
          intro m _
          apply Finset.sum_congr rfl
          intro k _
          ring
      rw [hsplit, hrow, hcol]
      have h1 := hdev n
      calc C * (∑ m ∈ Finset.range (n + 1),
            binomialMass n w m * |(m : ℝ) - (N n : ℝ)|) +
          C * (∑ k ∈ Finset.range (n + 1),
            binomialMass n w k * |(k : ℝ) - (N n : ℝ)|)
          ≤ C * (Real.sqrt (μ n) + 1) + C * (Real.sqrt (μ n) + 1) := by
            gcongr
        _ = 2 * C * (Real.sqrt (μ n) + 1) := by ring
    exact hstep1.trans hstep2
  -- The vanishing error.
  have hsqrtlim : Tendsto (fun n : ℕ => Real.sqrt (μ n) / (n : ℝ)) atTop (𝓝 0) := by
    have hdiv : Tendsto (fun n : ℕ => (w : ℝ) / (n : ℝ)) atTop (𝓝 0) :=
      tendsto_const_div_atTop_nhds_zero_nat _
    have hsqrt : Tendsto (fun n : ℕ => Real.sqrt ((w : ℝ) / (n : ℝ))) atTop (𝓝 0) := by
      have := Real.continuous_sqrt.continuousAt.tendsto.comp hdiv
      simpa only [Function.comp_def, Real.sqrt_zero] using this
    refine hsqrt.congr' ?_
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    have hμn : μ n = (n : ℝ) * (w : ℝ) := rfl
    have hsqrt_eq : Real.sqrt ((n : ℝ) * (w : ℝ)) / (n : ℝ) =
        Real.sqrt ((w : ℝ) / (n : ℝ)) := by
      nth_rewrite 2 [← Real.sqrt_sq hnpos.le]
      rw [← Real.sqrt_div (mul_nonneg hnpos.le hw.le) ((n : ℝ) ^ 2)]
      congr 1
      field_simp
    rw [hμn, hsqrt_eq]
  have herr : Tendsto (fun n : ℕ =>
      (2 * C * (Real.sqrt (μ n) + 1)) / (n : ℝ)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun n : ℕ => Real.sqrt (μ n) / (n : ℝ)) atTop (𝓝 0) := hsqrtlim
    have h2 : Tendsto (fun n : ℕ => (1 : ℝ) / (n : ℝ)) atTop (𝓝 0) :=
      tendsto_const_div_atTop_nhds_zero_nat _
    have hsum : Tendsto (fun n : ℕ =>
        Real.sqrt (μ n) / (n : ℝ) + (1 : ℝ) / (n : ℝ)) atTop (𝓝 0) := by
      simpa using h1.add h2
    have hscaled : Tendsto (fun n : ℕ =>
        2 * C * (Real.sqrt (μ n) / (n : ℝ) + 1 / (n : ℝ))) atTop (𝓝 0) := by
      simpa only [mul_zero] using hsum.const_mul (2 * C)
    have heq : (fun n : ℕ => 2 * C *
          (Real.sqrt (μ n) / (n : ℝ) + 1 / (n : ℝ))) =ᶠ[atTop]
        fun n : ℕ => (2 * C * (Real.sqrt (μ n) + 1)) / (n : ℝ) := by
      filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
      have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
      field_simp
    exact hscaled.congr' heq
  -- `N n / n → w`.
  have hNdiv : Tendsto (fun n : ℕ => (N n : ℝ) / (n : ℝ)) atTop (𝓝 (w : ℝ)) := by
    have hbase : Tendsto (fun n : ℕ => μ n / (n : ℝ)) atTop (𝓝 (w : ℝ)) := by
      have : (fun n : ℕ => μ n / (n : ℝ)) =ᶠ[atTop] fun _ => (w : ℝ) := by
        filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
        have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
        rw [hμ]
        field_simp
      exact tendsto_const_nhds.congr' this.symm
    have hd : Tendsto (fun n : ℕ => ((N n : ℝ) - μ n) / (n : ℝ)) atTop (𝓝 0) := by
      have hbd : ∀ n : ℕ, ‖((N n : ℝ) - μ n) / (n : ℝ)‖ ≤ 1 / (n : ℝ) := by
        intro n
        rw [Real.norm_eq_abs]
        rcases Nat.eq_zero_or_pos n with hn0 | hnpos'
        · subst hn0; simp
        · have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hnpos'
          rw [abs_div, abs_of_pos hnpos]
          gcongr
          rw [abs_sub_comm]
          exact hNclose n
      exact squeeze_zero_norm hbd (tendsto_const_div_atTop_nhds_zero_nat _)
    have := hd.add hbase
    have heq : (fun n : ℕ => ((N n : ℝ) - μ n) / (n : ℝ) + μ n / (n : ℝ)) =
        fun n : ℕ => (N n : ℝ) / (n : ℝ) := by
      funext n; ring
    simpa only [heq, zero_add] using this
  -- The vanishing error of the diagonal comparison.
  have hG : Tendsto (fun n : ℕ =>
      ((∑ m ∈ Finset.range (n + 1), ∑ k ∈ Finset.range (n + 1),
        binomialMass n w m * binomialMass n w k * E m k) - E (N n) (N n)) / (n : ℝ))
      atTop (𝓝 0) := by
    refine squeeze_zero_norm (fun n => ?_) herr
    rcases Nat.eq_zero_or_pos n with hn0 | hnpos'
    · subst hn0
      simp
    · have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hnpos'
      rw [Real.norm_eq_abs, abs_div, abs_of_pos hnpos]
      exact div_le_div_of_nonneg_right (hbound n) hnpos.le
  have hNev : ∀ᶠ n : ℕ in atTop, 0 < N n :=
    hNtop.eventually (eventually_ge_atTop 1)
  have hevent : (fun n : ℕ =>
      ((∑ m ∈ Finset.range (n + 1), ∑ k ∈ Finset.range (n + 1),
        binomialMass n w m * binomialMass n w k * E m k) - E (N n) (N n)) / (n : ℝ))
      =ᶠ[atTop] fun n : ℕ =>
        (∑ m ∈ Finset.range (n + 1), ∑ k ∈ Finset.range (n + 1),
          binomialMass n w m * binomialMass n w k * E m k) / (n : ℝ) -
          ((N n : ℝ) / (n : ℝ)) * (E (N n) (N n) / (N n : ℝ)) := by
    filter_upwards [hNev, eventually_ge_atTop (1 : ℕ)] with n hNn hn
    have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
    have hN0 : (N n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hNn)
    field_simp
  have hmain : Tendsto (fun n : ℕ =>
      (∑ m ∈ Finset.range (n + 1), ∑ k ∈ Finset.range (n + 1),
        binomialMass n w m * binomialMass n w k * E m k) / (n : ℝ) -
        ((N n : ℝ) / (n : ℝ)) * (E (N n) (N n) / (N n : ℝ))) atTop (𝓝 0) :=
    hG.congr' hevent
  have hprod : Tendsto (fun n : ℕ =>
      ((N n : ℝ) / (n : ℝ)) * (E (N n) (N n) / (N n : ℝ))) atTop
      (𝓝 ((w : ℝ) * p)) := hNdiv.mul hdiagN
  have hsum := hmain.add hprod
  simpa only [sub_add_cancel, zero_add] using hsum

/-- **Binomial mixing of a Lipschitz two-count functional.** -/
theorem tendsto_binomial_double_sum_of_lipschitz_scale
    (E : ℕ → ℕ → ℕ → ℝ) (C : ℕ → ℝ) {p : ℝ} (hC : ∀ N, 0 ≤ C N)
    (hE : ∀ N m k m' k',
      |E N m k - E N m' k'| ≤ C N * (|(m : ℝ) - (m' : ℝ)| + |(k : ℝ) - (k' : ℝ)|))
    (hdiag : Tendsto (fun N : ℕ => E N N N / (N : ℝ)) atTop (𝓝 p))
    (w : I) (hw : 0 < (w : ℝ))
    (herror : Tendsto (fun n : ℕ =>
      (2 * C (Nat.floor ((n : ℝ) * (w : ℝ))) *
        (Real.sqrt ((n : ℝ) * (w : ℝ)) + 1)) / (n : ℝ)) atTop (𝓝 0)) :
    Tendsto (fun n : ℕ =>
      (∑ m ∈ Finset.range (n + 1), ∑ k ∈ Finset.range (n + 1),
        binomialMass n w m * binomialMass n w k *
          E (Nat.floor ((n : ℝ) * (w : ℝ))) m k) / (n : ℝ))
      atTop (𝓝 ((w : ℝ) * p)) := by
  classical
  set μ : ℕ → ℝ := fun n => (n : ℝ) * (w : ℝ) with hμ
  set N : ℕ → ℕ := fun n => Nat.floor (μ n) with hN
  have hμtop : Tendsto μ atTop atTop := by
    have h3 : Tendsto (fun x : ℝ => (w : ℝ) * x) atTop atTop :=
      Tendsto.const_mul_atTop hw tendsto_id
    have h4 : Tendsto (fun n : ℕ => (w : ℝ) * (n : ℝ)) atTop atTop :=
      h3.comp tendsto_natCast_atTop_atTop
    simpa only [hμ, mul_comm] using h4
  have hNtop : Tendsto N atTop atTop := tendsto_nat_floor_atTop.comp hμtop
  have hdiagN : Tendsto (fun n : ℕ => E (N n) (N n) (N n) / (N n : ℝ)) atTop (𝓝 p) :=
    hdiag.comp hNtop
  have hNle (n : ℕ) : (N n : ℝ) ≤ μ n := Nat.floor_le (by rw [hμ]; positivity)
  have hNlt (n : ℕ) : μ n < (N n : ℝ) + 1 := Nat.lt_floor_add_one (μ n)
  have hNclose (n : ℕ) : |μ n - (N n : ℝ)| ≤ 1 := by
    have h0 : 0 ≤ μ n - (N n : ℝ) := by linarith [hNle n]
    rw [abs_of_nonneg h0]
    linarith [hNlt n]
  -- Weighted deviation from the deterministic index.
  have hdev (n : ℕ) :
      ∑ k ∈ Finset.range (n + 1),
          binomialMass n w k * |(k : ℝ) - (N n : ℝ)| ≤
        Real.sqrt (μ n) + 1 := by
    have h := binomialMass_sum_abs_sub_index_le n w (N n)
    have hμn : (n : ℝ) * (w : ℝ) = μ n := rfl
    rw [hμn] at h
    exact h.trans (add_le_add le_rfl (hNclose n))
  -- The double-sum difference from the diagonal value.
  have hdiff (n : ℕ) :
      (∑ m ∈ Finset.range (n + 1), ∑ k ∈ Finset.range (n + 1),
          binomialMass n w m * binomialMass n w k * E (N n) m k) - E (N n) (N n) (N n) =
        ∑ m ∈ Finset.range (n + 1), ∑ k ∈ Finset.range (n + 1),
          binomialMass n w m * binomialMass n w k * (E (N n) m k - E (N n) (N n) (N n)) := by
    have hsum1 : ∑ k ∈ Finset.range (n + 1), binomialMass n w k = 1 :=
      binomialMass_sum_one n w
    have hconst : (∑ m ∈ Finset.range (n + 1), ∑ k ∈ Finset.range (n + 1),
          binomialMass n w m * binomialMass n w k * E (N n) (N n) (N n)) = E (N n) (N n) (N n) := by
      have hdouble : (∑ m ∈ Finset.range (n + 1), ∑ k ∈ Finset.range (n + 1),
          binomialMass n w m * binomialMass n w k) = 1 := by
        rw [← Finset.sum_mul_sum, hsum1]; ring
      calc ∑ m ∈ Finset.range (n + 1), ∑ k ∈ Finset.range (n + 1),
            binomialMass n w m * binomialMass n w k * E (N n) (N n) (N n)
          = (∑ m ∈ Finset.range (n + 1), ∑ k ∈ Finset.range (n + 1),
              binomialMass n w m * binomialMass n w k) * E (N n) (N n) (N n) := by
            simp only [Finset.sum_mul]
        _ = E (N n) (N n) (N n) := by rw [hdouble, one_mul]
    conv_lhs => rw [← hconst]
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro m _
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro k _
    ring
  -- Bound the difference by the weighted count deviations.
  have hbound (n : ℕ) :
      |(∑ m ∈ Finset.range (n + 1), ∑ k ∈ Finset.range (n + 1),
          binomialMass n w m * binomialMass n w k * E (N n) m k) - E (N n) (N n) (N n)| ≤
        2 * C (N n) * (Real.sqrt (μ n) + 1) := by
    rw [hdiff n]
    -- Summation helpers for the row and column parts.
    have hdbl_row : ∀ (f : ℕ → ℝ),
        (∑ m ∈ Finset.range (n + 1), ∑ k ∈ Finset.range (n + 1),
            binomialMass n w m * binomialMass n w k * f m) =
          (∑ m ∈ Finset.range (n + 1), binomialMass n w m * f m) *
            (∑ k ∈ Finset.range (n + 1), binomialMass n w k) := by
      intro f
      rw [Finset.sum_mul_sum]
      apply Finset.sum_congr rfl
      intro m _
      apply Finset.sum_congr rfl
      intro k _
      ring
    have hdbl_col : ∀ (h : ℕ → ℝ),
        (∑ m ∈ Finset.range (n + 1), ∑ k ∈ Finset.range (n + 1),
            binomialMass n w m * binomialMass n w k * h k) =
          (∑ m ∈ Finset.range (n + 1), binomialMass n w m) *
            (∑ k ∈ Finset.range (n + 1), binomialMass n w k * h k) := by
      intro h
      rw [Finset.sum_mul_sum]
      apply Finset.sum_congr rfl
      intro m _
      apply Finset.sum_congr rfl
      intro k _
      ring

    have hnonneg (k : ℕ) : 0 ≤ binomialMass n w k := binomialMass_nonneg n w k
    have hsum1 : ∑ k ∈ Finset.range (n + 1), binomialMass n w k = 1 :=
      binomialMass_sum_one n w
    have hrow : (∑ m ∈ Finset.range (n + 1), ∑ k ∈ Finset.range (n + 1),
          binomialMass n w m * binomialMass n w k * |(m : ℝ) - (N n : ℝ)|) =
        ∑ m ∈ Finset.range (n + 1),
          binomialMass n w m * |(m : ℝ) - (N n : ℝ)| := by
      rw [hdbl_row, hsum1, mul_one]
    have hcol : (∑ m ∈ Finset.range (n + 1), ∑ k ∈ Finset.range (n + 1),
          binomialMass n w m * binomialMass n w k * |(k : ℝ) - (N n : ℝ)|) =
        ∑ k ∈ Finset.range (n + 1),
          binomialMass n w k * |(k : ℝ) - (N n : ℝ)| := by
      rw [hdbl_col, hsum1, one_mul]
    have hstep1 : |∑ m ∈ Finset.range (n + 1), ∑ k ∈ Finset.range (n + 1),
          binomialMass n w m * binomialMass n w k * (E (N n) m k - E (N n) (N n) (N n))| ≤
        ∑ m ∈ Finset.range (n + 1), ∑ k ∈ Finset.range (n + 1),
          binomialMass n w m * binomialMass n w k *
            (C (N n) * (|(m : ℝ) - (N n : ℝ)| + |(k : ℝ) - (N n : ℝ)|)) := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans
        (Finset.sum_le_sum fun m _ => ?_)
      refine (Finset.abs_sum_le_sum_abs _ _).trans
        (Finset.sum_le_sum fun k _ => ?_)
      rw [abs_mul, abs_of_nonneg (mul_nonneg (hnonneg m) (hnonneg k))]
      exact mul_le_mul_of_nonneg_left (hE (N n) m k (N n) (N n))
        (mul_nonneg (hnonneg m) (hnonneg k))
    have hstep2 : (∑ m ∈ Finset.range (n + 1), ∑ k ∈ Finset.range (n + 1),
          binomialMass n w m * binomialMass n w k *
            (C (N n) * (|(m : ℝ) - (N n : ℝ)| + |(k : ℝ) - (N n : ℝ)|))) ≤
        2 * C (N n) * (Real.sqrt (μ n) + 1) := by
      have hsplit : (∑ m ∈ Finset.range (n + 1), ∑ k ∈ Finset.range (n + 1),
            binomialMass n w m * binomialMass n w k *
              (C (N n) * (|(m : ℝ) - (N n : ℝ)| + |(k : ℝ) - (N n : ℝ)|))) =
          C (N n) * (∑ m ∈ Finset.range (n + 1), ∑ k ∈ Finset.range (n + 1),
              binomialMass n w m * binomialMass n w k * |(m : ℝ) - (N n : ℝ)|) +
            C (N n) * (∑ m ∈ Finset.range (n + 1), ∑ k ∈ Finset.range (n + 1),
              binomialMass n w m * binomialMass n w k * |(k : ℝ) - (N n : ℝ)|) := by
        simp only [mul_add, Finset.sum_add_distrib, Finset.mul_sum]
        congr 1
        · apply Finset.sum_congr rfl
          intro m _
          apply Finset.sum_congr rfl
          intro k _
          ring
        · apply Finset.sum_congr rfl
          intro m _
          apply Finset.sum_congr rfl
          intro k _
          ring
      rw [hsplit, hrow, hcol]
      have h1 := hdev n
      calc C (N n) * (∑ m ∈ Finset.range (n + 1),
            binomialMass n w m * |(m : ℝ) - (N n : ℝ)|) +
          C (N n) * (∑ k ∈ Finset.range (n + 1),
            binomialMass n w k * |(k : ℝ) - (N n : ℝ)|)
          ≤ C (N n) * (Real.sqrt (μ n) + 1) + C (N n) * (Real.sqrt (μ n) + 1) := by
            exact add_le_add (mul_le_mul_of_nonneg_left (hdev n) (hC (N n)))
              (mul_le_mul_of_nonneg_left (hdev n) (hC (N n)))
        _ = 2 * C (N n) * (Real.sqrt (μ n) + 1) := by ring
    exact hstep1.trans hstep2
  -- The vanishing error is the prescribed hypothesis.
  have herr : Tendsto (fun n : ℕ =>
      (2 * C (N n) * (Real.sqrt (μ n) + 1)) / (n : ℝ)) atTop (𝓝 0) := by
    simpa only [hμ, hN] using herror
  -- `N n / n → w`.
  have hNdiv : Tendsto (fun n : ℕ => (N n : ℝ) / (n : ℝ)) atTop (𝓝 (w : ℝ)) := by
    have hbase : Tendsto (fun n : ℕ => μ n / (n : ℝ)) atTop (𝓝 (w : ℝ)) := by
      have : (fun n : ℕ => μ n / (n : ℝ)) =ᶠ[atTop] fun _ => (w : ℝ) := by
        filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
        have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
        rw [hμ]
        field_simp
      exact tendsto_const_nhds.congr' this.symm
    have hd : Tendsto (fun n : ℕ => ((N n : ℝ) - μ n) / (n : ℝ)) atTop (𝓝 0) := by
      have hbd : ∀ n : ℕ, ‖((N n : ℝ) - μ n) / (n : ℝ)‖ ≤ 1 / (n : ℝ) := by
        intro n
        rw [Real.norm_eq_abs]
        rcases Nat.eq_zero_or_pos n with hn0 | hnpos'
        · subst hn0; simp
        · have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hnpos'
          rw [abs_div, abs_of_pos hnpos]
          gcongr
          rw [abs_sub_comm]
          exact hNclose n
      exact squeeze_zero_norm hbd (tendsto_const_div_atTop_nhds_zero_nat _)
    have := hd.add hbase
    have heq : (fun n : ℕ => ((N n : ℝ) - μ n) / (n : ℝ) + μ n / (n : ℝ)) =
        fun n : ℕ => (N n : ℝ) / (n : ℝ) := by
      funext n; ring
    simpa only [heq, zero_add] using this
  -- The vanishing error of the diagonal comparison.
  have hG : Tendsto (fun n : ℕ =>
      ((∑ m ∈ Finset.range (n + 1), ∑ k ∈ Finset.range (n + 1),
        binomialMass n w m * binomialMass n w k * E (N n) m k) - E (N n) (N n) (N n)) / (n : ℝ))
      atTop (𝓝 0) := by
    refine squeeze_zero_norm (fun n => ?_) herr
    rcases Nat.eq_zero_or_pos n with hn0 | hnpos'
    · subst hn0
      simp
    · have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hnpos'
      rw [Real.norm_eq_abs, abs_div, abs_of_pos hnpos]
      exact div_le_div_of_nonneg_right (hbound n) hnpos.le
  have hNev : ∀ᶠ n : ℕ in atTop, 0 < N n :=
    hNtop.eventually (eventually_ge_atTop 1)
  have hevent : (fun n : ℕ =>
      ((∑ m ∈ Finset.range (n + 1), ∑ k ∈ Finset.range (n + 1),
        binomialMass n w m * binomialMass n w k * E (N n) m k) - E (N n) (N n) (N n)) / (n : ℝ))
      =ᶠ[atTop] fun n : ℕ =>
        (∑ m ∈ Finset.range (n + 1), ∑ k ∈ Finset.range (n + 1),
          binomialMass n w m * binomialMass n w k * E (N n) m k) / (n : ℝ) -
          ((N n : ℝ) / (n : ℝ)) * (E (N n) (N n) (N n) / (N n : ℝ)) := by
    filter_upwards [hNev, eventually_ge_atTop (1 : ℕ)] with n hNn hn
    have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
    have hN0 : (N n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hNn)
    field_simp
  have hmain : Tendsto (fun n : ℕ =>
      (∑ m ∈ Finset.range (n + 1), ∑ k ∈ Finset.range (n + 1),
        binomialMass n w m * binomialMass n w k * E (N n) m k) / (n : ℝ) -
        ((N n : ℝ) / (n : ℝ)) * (E (N n) (N n) (N n) / (N n : ℝ))) atTop (𝓝 0) :=
    hG.congr' hevent
  have hprod : Tendsto (fun n : ℕ =>
      ((N n : ℝ) / (n : ℝ)) * (E (N n) (N n) (N n) / (N n : ℝ))) atTop
      (𝓝 ((w : ℝ) * p)) := hNdiv.mul hdiagN
  have hsum := hmain.add hprod
  simpa only [sub_add_cancel, zero_add] using hsum


end OTSelector.Probability
