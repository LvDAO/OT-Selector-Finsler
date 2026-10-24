import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Probability.Distributions.Beta
import OTSelector.Probability.DirichletReference
import OTSelector.Probability.DirichletReferenceMoments

/-!
Conditions: Natural Dirichlet dimension, natural monomial powers and the actual unit-parameter reference probability.

Objects: Bochner-integrable monomials and exact real mixed, coordinate, square and summed-square moments, including E p_i=1/(n+1) and EΣp_i²=2/(n+2).

Proof detail: Compact simplex support bounds all monomials. Convert the computed nonnegative factorial moments to real integrals and specialize the exponent vector.

References: Günter Last and Mathew Penrose: Section 15.5, Exercise 15.1, p. 163; Thomas P. Minka: Section 1, equations (1)–(3), p. 1; equations (19)–(20), p. 2.
Relation: The first/second coordinate moments match the author-paper formulas. The arbitrary monomial and summed identities are local specializations of the proved factorial mixed moments.
-/


/-!
# Real moments of the original Dirichlet reference weights

The existing factorial mixed moments give real coordinate moments. Compact
simplex support supplies their Bochner integrability. These identities are used
for the local masses of the actual weighted random target configuration.
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators

noncomputable section
namespace OTSelector.Probability

/-- Every real simplex monomial is integrable under the original Dirichlet law. -/
theorem integrable_dirichletOne_nat_powers (n : ℕ) (r : Fin (n + 1) → ℕ) :
    Integrable (fun p ↦ ∏ j, p j ^ r j) (dirichletOne n) := by
  have hc : Continuous (fun p : Fin (n + 1) → ℝ ↦ ∏ j, p j ^ r j) := by fun_prop
  have h := hc.continuousOn.integrableOn_compact (isCompact_stdSimplex ℝ (Fin (n + 1)))
    (μ := dirichletOne n)
  simpa only [IntegrableOn,
    Measure.restrict_eq_self_of_ae_mem (ae_mem_stdSimplex_dirichletOne n)] using h

/-- Real mixed moments are the factorial ratios already proved for the nonnegative
integral; no separate probability model for the weights is introduced. -/
theorem integral_dirichletOne_nat_powers (n : ℕ) (r : Fin (n + 1) → ℕ) :
    (∫ p, ∏ j, p j ^ r j ∂dirichletOne n) =
      (n.factorial : ℝ) * (∏ j, (r j).factorial : ℝ) / (n + ∑ j, r j).factorial := by
  have hnonneg : ∀ᵐ p ∂dirichletOne n, 0 ≤ ∏ j, p j ^ r j :=
    (ae_mem_stdSimplex_dirichletOne n).mono fun p hp ↦
      Finset.prod_nonneg fun j _ ↦ pow_nonneg (hp.1 j) _
  rw [integral_eq_lintegral_of_nonneg_ae hnonneg
    (integrable_dirichletOne_nat_powers n r).aestronglyMeasurable]
  have heq : (∫⁻ p, ENNReal.ofReal (∏ j, p j ^ r j) ∂dirichletOne n) =
      ∫⁻ p, ∏ j, ENNReal.ofReal (p j) ^ r j ∂dirichletOne n := by
    apply lintegral_congr_ae
    filter_upwards [ae_mem_stdSimplex_dirichletOne n] with p hp
    rw [ENNReal.ofReal_prod_of_nonneg (fun j _ ↦ pow_nonneg (hp.1 j) _)]
    exact Finset.prod_congr rfl fun j _ ↦ ENNReal.ofReal_pow (hp.1 j) _
  rw [heq, lintegral_dirichletOne_nat_powers, ENNReal.toReal_ofReal (by positivity)]

/-- The kth moment of any one of the n+1 original Dirichlet coordinates. -/
theorem integral_dirichletOne_coordinate_pow (n : ℕ) (i : Fin (n + 1)) (k : ℕ) :
    (∫ p, p i ^ k ∂dirichletOne n) =
      (n.factorial : ℝ) * k.factorial / (n + k).factorial := by
  simpa [apply_ite] using
    integral_dirichletOne_nat_powers n (fun j ↦ if j = i then k else 0)

/-- Coordinate powers are integrable, including the zero exponent. -/
theorem integrable_dirichletOne_coordinate_pow (n : ℕ) (i : Fin (n + 1)) (k : ℕ) :
    Integrable (fun p ↦ p i ^ k) (dirichletOne n) := by
  simpa [apply_ite] using
    integrable_dirichletOne_nat_powers n (fun j ↦ if j = i then k else 0)

/-- The actual Dirichlet coordinate mean. -/
theorem integral_dirichletOne_coordinate (n : ℕ) (i : Fin (n + 1)) :
    (∫ p, p i ∂dirichletOne n) = 1 / ((n : ℝ) + 1) := by
  have h := integral_dirichletOne_coordinate_pow n i 1
  have hfac : (n.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  norm_num [Nat.factorial_succ] at h
  rw [h]
  field_simp

/-- The actual Dirichlet coordinate second moment. -/
theorem integral_dirichletOne_coordinate_sq (n : ℕ) (i : Fin (n + 1)) :
    (∫ p, (p i) ^ 2 ∂dirichletOne n) = 2 / (((n : ℝ) + 1) * ((n : ℝ) + 2)) := by
  rw [integral_dirichletOne_coordinate_pow]
  have hfac : (n.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  simp only [show n + 2 = (n + 1) + 1 by omega, Nat.factorial_succ,
    Nat.factorial_zero, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  field_simp
  ring

/-- The total diagonal quadratic weight of the actual Dirichlet vector. -/
theorem integral_dirichletOne_sum_sq (n : ℕ) :
    (∫ p, ∑ i, (p i) ^ 2 ∂dirichletOne n) = 2 / ((n : ℝ) + 2) := by
  rw [integral_finsetSum _ (fun i _ ↦ integrable_dirichletOne_coordinate_pow n i 2)]
  simp_rw [integral_dirichletOne_coordinate_sq]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    Nat.cast_add, Nat.cast_one]
  have hn : (n : ℝ) + 1 ≠ 0 := by positivity
  field_simp

end OTSelector.Probability
