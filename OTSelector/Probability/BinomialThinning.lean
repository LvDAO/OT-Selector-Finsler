import OTSelector.Probability.MarkedCountBlockLaw
import Mathlib.Data.Nat.Choose.Sum

/-! Exact composition of two original binomial restrictions.
Finite-sample thinning is evaluated before any asymptotic limit. -/
open Set Function MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal unitInterval
noncomputable section
namespace OTSelector.Probability
set_option backward.isDefEq.respectTransparency false

/-- The finite binomial-composition identity, before specializing its four
weights to probabilities. It includes impossible retained counts. -/
theorem sum_choose_compound {R : Type*} [CommSemiring R]
    (N k : ℕ) (x y z w : R) :
    (∑ m ∈ Finset.range (N + 1), (N.choose m : R) * x ^ m * y ^ (N - m) *
      (m.choose k : R) * z ^ k * w ^ (m - k)) =
      (N.choose k : R) * (x * z) ^ k * (x * w + y) ^ (N - k) := by
  classical
  by_cases hk : k ≤ N
  · let f : ℕ → R := fun m ↦ (N.choose m : R) * x ^ m * y ^ (N - m) *
      (m.choose k : R) * z ^ k * w ^ (m - k)
    have hzero : ∑ m ∈ Finset.range k, f m = 0 := by
      apply Finset.sum_eq_zero
      intro m hm
      simp only [f, Nat.choose_eq_zero_of_lt (Finset.mem_range.mp hm),
        Nat.cast_zero, mul_zero, zero_mul]
    have hshift : (∑ m ∈ Finset.range (N + 1), f m) =
        ∑ j ∈ Finset.range (N - k + 1), f (j + k) := by
      rw [show N + 1 = k + (N - k + 1) by omega, Finset.sum_range_add, hzero, zero_add]
      simp only [Nat.add_comm]
    have hterm (j : ℕ) : f (j + k) =
        ((N.choose k : R) * (x * z) ^ k) *
          ((x * w) ^ j * y ^ (N - k - j) * ((N - k).choose j : R)) := by
      have hcoef : (N.choose (j + k) : R) * ((j + k).choose k : R) =
          (N.choose k : R) * ((N - k).choose j : R) := by
        have h := congrArg (Nat.cast : ℕ → R)
          (Nat.choose_mul (n := N) (k := j + k) (s := k) (Nat.le_add_left k j))
        simpa only [Nat.cast_mul, Nat.add_sub_cancel_right] using h
      have hsub : N - (j + k) = N - k - j := by omega
      dsimp only [f]
      rw [pow_add, Nat.add_sub_cancel_right, hsub]
      calc
        _ = ((N.choose (j + k) : R) * ((j + k).choose k : R)) *
            x ^ j * x ^ k * y ^ (N - k - j) * z ^ k * w ^ j := by ring
        _ = _ := by rw [hcoef, mul_pow, mul_pow]; ring
    change (∑ m ∈ Finset.range (N + 1), f m) = _
    rw [hshift]
    simp_rw [hterm]
    rw [← Finset.mul_sum, ← add_pow]
  · have hNk : N < k := Nat.lt_of_not_ge hk
    rw [Nat.choose_eq_zero_of_lt hNk, Nat.cast_zero, zero_mul, zero_mul]
    apply Finset.sum_eq_zero
    intro m hm
    have hmk : m < k := lt_of_le_of_lt (Nat.le_of_lt_succ (Finset.mem_range.mp hm)) hNk
    simp only [Nat.choose_eq_zero_of_lt hmk, Nat.cast_zero, mul_zero, zero_mul]

/-- Original binomial probabilities compose exactly: first keep probability p,
then keep probability s among those original points. -/
theorem binomialMass_compound (N k : ℕ) (p s : I) :
    (∑ m ∈ Finset.range (N + 1), binomialMass N p m * binomialMass m s k) =
      binomialMass N (p * s) k := by
  have h := sum_choose_compound N k (p : ℝ) (1 - (p : ℝ)) (s : ℝ) (1 - (s : ℝ))
  have hbase : (p : ℝ) * (1 - (s : ℝ)) + (1 - (p : ℝ)) = 1 - (p : ℝ) * s := by ring
  simp only [binomialMass, Set.Icc.coe_mul]
  simp only [hbase] at h
  convert h using 1
  apply Finset.sum_congr rfl
  intro m _
  ring

/-- The corresponding exact singleton identity for the original probability
measures. All terms outside the original finite count range vanish. -/
theorem binomial_measure_compound (N k : ℕ) (p s : I) :
    (∑' m : ℕ, ProbabilityTheory.binomial N p {m} * ProbabilityTheory.binomial m s {k}) =
      ProbabilityTheory.binomial N (p * s) {k} := by
  rw [tsum_eq_sum (s := Finset.range (N + 1)) (fun m hm ↦ ?_)]
  · calc
      _ = ∑ m ∈ Finset.range (N + 1),
          ENNReal.ofReal (binomialMass N p m * binomialMass m s k) := by
        apply Finset.sum_congr rfl
        intro m _
        rw [binomial_singleton, binomial_singleton,
          ENNReal.ofReal_mul (binomialMass_nonneg N p m)]
        rfl
      _ = ENNReal.ofReal (∑ m ∈ Finset.range (N + 1),
          binomialMass N p m * binomialMass m s k) :=
        (ENNReal.ofReal_sum_of_nonneg (fun m _ ↦
          mul_nonneg (binomialMass_nonneg N p m) (binomialMass_nonneg m s k))).symm
      _ = _ := by rw [binomialMass_compound, binomial_singleton]; rfl
  · have hNm : N < m := by simp only [Finset.mem_range] at hm; omega
    rw [binomial_singleton, Nat.choose_eq_zero_of_lt hNm, Nat.cast_zero, zero_mul,
      zero_mul, ENNReal.ofReal_zero, zero_mul]

/-- Existing retained-prefix binomial weights obey the same exact thinning
identity, so no original finite count law is changed. -/
theorem binomWeight_compound (N k : ℕ) (p s : I) :
    (∑' m : ℕ, binomWeight N (Real.toNNReal (p : ℝ)) m *
      binomWeight m (Real.toNNReal (s : ℝ)) k) =
        binomWeight N (Real.toNNReal ((p * s : I) : ℝ)) k := by
  simpa only [binomial_singleton_eq_binomWeight] using binomial_measure_compound N k p s

/-- The exact same identity in the original NNReal retained-mass convention. -/
theorem binomWeight_compound_nnreal (N k : ℕ) (p s : ℝ≥0)
    (hp : p ≤ 1) (hs : s ≤ 1) :
    (∑' m : ℕ, binomWeight N p m * binomWeight m s k) = binomWeight N (p * s) k := by
  let pI : I := ⟨p, p.coe_nonneg, by exact_mod_cast hp⟩
  let sI : I := ⟨s, s.coe_nonneg, by exact_mod_cast hs⟩
  simpa only [pI, sI, Set.Icc.coe_mul, Real.toNNReal_mul p.coe_nonneg,
    Real.toNNReal_coe] using binomWeight_compound N k pI sI

end OTSelector.Probability
