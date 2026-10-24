import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Probability.Distributions.Beta
import OTSelector.Probability.BetaMixedMoments
import OTSelector.Probability.DirichletReference

/-!
Conditions: The actual recursively constructed unit-parameter Dirichlet law and arbitrary natural exponents; the elementary split product identity only requires the displayed x≤1.

Objects: Exact factorial mixed moments n!∏r_j!/(n+Σr_j)! for that reference law, through a genuine beta-recursion identity.

Proof detail: Factor a split simplex monomial into a one-dimensional beta monomial and the smaller simplex monomial. Tonelli factors the true independent product, then beta/gamma identities solve the recursion.

References: Günter Last and Mathew Penrose: Section 15.5, Exercise 15.1, p. 163; Thomas P. Minka: Section 1, equations (1)–(3), p. 1; equations (19)–(20), p. 2.
Relation: The factorial mixed-moment formula is computed locally from the standard density/beta splitting. It is not attributed to Minka’s printed first/second moments as if that paper stated every natural mixed moment.
-/


/-!
# Mixed moments of the Dirichlet reference law

The actual recursive beta construction factors each simplex monomial into a
one-dimensional beta monomial and a smaller simplex monomial. Its mixed-moment
recursion follows from the genuine product probability measure.
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators

namespace OTSelector.Probability

/-- The monomial factorization under the actual beta splitting map. -/
theorem prod_dirichletSplit_nat_powers {n : ℕ} {x : ℝ} (hx : x ≤ 1)
    (p : Fin (n + 1) → ℝ) (r : Fin (n + 2) → ℕ) :
    (∏ j, ENNReal.ofReal (dirichletSplit n (x, p) j) ^ r j) =
      ((ENNReal.ofReal x) ^ r 0 *
        (ENNReal.ofReal (1 - x)) ^ (∑ k : Fin (n + 1), r k.succ)) *
          ∏ k, (ENNReal.ofReal (p k)) ^ r k.succ := by
  rw [Fin.prod_univ_succ]
  simp only [dirichletSplit, Fin.cons_zero, Fin.cons_succ,
    ENNReal.ofReal_mul (sub_nonneg.mpr hx), mul_pow]
  rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, mul_assoc]

/-- Mixed moments factor into the existing beta moment and the smaller
Dirichlet mixed moment. -/
theorem lintegral_dirichletOne_nat_powers_succ (n : ℕ) (r : Fin (n + 2) → ℕ) :
    (∫⁻ p, ∏ j, ENNReal.ofReal (p j) ^ r j ∂dirichletOne (n + 1)) =
      ENNReal.ofReal (beta (1 + r 0) ((n : ℝ) + 1 + ∑ k : Fin (n + 1), (r k.succ : ℝ)) /
        beta 1 ((n : ℝ) + 1)) *
          ∫⁻ p, ∏ k, ENNReal.ofReal (p k) ^ r k.succ ∂dirichletOne n := by
  let := isProbabilityMeasureBeta (α := 1) (β := (n : ℝ) + 1) (by norm_num) (by positivity)
  have hmono : Measurable (fun p : Fin (n + 2) → ℝ ↦
      ∏ j, ENNReal.ofReal (p j) ^ r j) := by fun_prop
  have htail : Measurable (fun p : Fin (n + 1) → ℝ ↦
      ∏ k, ENNReal.ofReal (p k) ^ r k.succ) := by fun_prop
  rw [dirichletOne, lintegral_map hmono (measurable_dirichletSplit n)]
  have hx : ∀ᵐ z ∂(betaMeasure 1 ((n : ℝ) + 1)).prod (dirichletOne n), z.1 ≤ 1 := by
    apply (Measure.ae_prod_iff_ae_ae
      (measurableSet_le measurable_fst measurable_const)).mpr
    filter_upwards [ae_mem_Ioo_betaMeasure 1 ((n : ℝ) + 1)] with x hx
    exact Filter.Eventually.of_forall fun _ ↦ hx.2.le
  calc
    _ = ∫⁻ z : ℝ × (Fin (n + 1) → ℝ),
        ((ENNReal.ofReal z.1) ^ r 0 *
          (ENNReal.ofReal (1 - z.1)) ^ (∑ k : Fin (n + 1), r k.succ)) *
            ∏ k, (ENNReal.ofReal (z.2 k)) ^ r k.succ
          ∂(betaMeasure 1 ((n : ℝ) + 1)).prod (dirichletOne n) := by
      apply lintegral_congr_ae
      filter_upwards [hx] with z hz
      exact prod_dirichletSplit_nat_powers hz z.2 r
    _ = (∫⁻ x, (ENNReal.ofReal x) ^ r 0 *
          (ENNReal.ofReal (1 - x)) ^ (∑ k : Fin (n + 1), r k.succ) ∂betaMeasure 1 ((n : ℝ) + 1)) *
          ∫⁻ p, ∏ k, ENNReal.ofReal (p k) ^ r k.succ ∂dirichletOne n :=
      lintegral_prod_mul
        (f := fun x : ℝ ↦ (ENNReal.ofReal x) ^ r 0 *
          (ENNReal.ofReal (1 - x)) ^ (∑ k : Fin (n + 1), r k.succ))
        (g := fun p : Fin (n + 1) → ℝ ↦ ∏ k, ENNReal.ofReal (p k) ^ r k.succ)
        (by fun_prop) htail.aemeasurable
    _ = _ := by
      rw [lintegral_beta_nat_powers (by norm_num : (0 : ℝ) < 1)
        (by positivity : (0 : ℝ) < (n : ℝ) + 1)]
      simp only [Nat.cast_sum]

/-- All mixed moments of the explicit Dirichlet reference law are the standard
factorial ratios, including zero exponents. -/
theorem lintegral_dirichletOne_nat_powers (n : ℕ) (r : Fin (n + 1) → ℕ) :
    (∫⁻ p, ∏ j, ENNReal.ofReal (p j) ^ r j ∂dirichletOne n) =
      ENNReal.ofReal ((n.factorial : ℝ) * (∏ j, (r j).factorial : ℝ) /
        (n + ∑ j, r j).factorial) := by
  induction n with
  | zero =>
    have hf : ((r 0).factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero (r 0)
    simp [dirichletOne, hf]
  | succ n ih =>
    rw [lintegral_dirichletOne_nat_powers_succ, ih (fun k ↦ r k.succ)]
    let R : ℕ := ∑ k : Fin (n + 1), r k.succ
    have hsum : (∑ k : Fin (n + 1), (r k.succ : ℝ)) = R := by simp [R]
    have hβ : 0 ≤ beta (1 + r 0) ((n : ℝ) + 1 + ∑ k : Fin (n + 1), (r k.succ : ℝ)) /
        beta 1 ((n : ℝ) + 1) :=
      (div_pos (beta_pos (by positivity) (by positivity))
        (beta_pos (by norm_num) (by positivity))).le
    rw [← ENNReal.ofReal_mul hβ]
    congr 1
    have hbase : beta 1 ((n : ℝ) + 1) = (n.factorial : ℝ) / (n + 1).factorial := by
      simpa using beta_nat_succ_eq_factorial 0 n
    have hshape : (n : ℝ) + 1 + R = (n + R : ℕ) + 1 := by push_cast; ring
    have hprod : (∏ j : Fin (n + 2), ((r j).factorial : ℝ)) =
        ((r 0).factorial : ℝ) * ∏ k : Fin (n + 1), ((r k.succ).factorial : ℝ) :=
      Fin.prod_univ_succ _
    have hsumAll : (∑ j, r j) = r 0 + R := Fin.sum_univ_succ r
    rw [hsum, show (1 : ℝ) + r 0 = (r 0 : ℝ) + 1 by ring, hshape,
      beta_nat_succ_eq_factorial, hbase, hprod, hsumAll]
    change
      (((r 0).factorial : ℝ) * (n + R).factorial / (r 0 + (n + R) + 1).factorial /
        ((n.factorial : ℝ) / (n + 1).factorial)) *
          ((n.factorial : ℝ) * (∏ k : Fin (n + 1), (r k.succ).factorial : ℝ) / (n + R).factorial) =
        ((n + 1).factorial : ℝ) * (((r 0).factorial : ℝ) * ∏ k : Fin (n + 1), ((r k.succ).factorial : ℝ)) /
          (n + 1 + (r 0 + R)).factorial
    rw [show n + 1 + (r 0 + R) = r 0 + (n + R) + 1 by omega]
    have hn : (n.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
    have hnR : ((n + R).factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero (n + R)
    have hn1 : ((n + 1).factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero (n + 1)
    have hden : ((r 0 + (n + R) + 1).factorial : ℝ) ≠ 0 := by
      exact_mod_cast Nat.factorial_ne_zero (r 0 + (n + R) + 1)
    field_simp

end OTSelector.Probability
