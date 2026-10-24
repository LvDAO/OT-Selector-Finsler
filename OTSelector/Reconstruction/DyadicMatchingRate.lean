import OTSelector.Reconstruction.IIDTypedCountAsymptotics
import Mathlib.Algebra.Field.GeomSum
import Mathlib.Algebra.Order.Archimedean.Basic

/-!
# The high-dimensional dyadic cutoff

A finite cutoff balances terminal squared diameter and iid histogram fluctuations.
The constants depend only on dimension; no density or atomlessness is used.
-/

open Set Function MeasureTheory ProbabilityTheory
open scoped BigOperators

noncomputable section
namespace OTSelector.Reconstruction

/-- The growing ratio in the coarse-scale fluctuation sum. -/
def dyadicFluctuationRatio (q : ℝ) : ℝ := (2 : ℝ) ^ (q / 2 - 2)

theorem one_lt_dyadicFluctuationRatio {q : ℝ} (hq : 4 < q) :
    1 < dyadicFluctuationRatio q :=
  Real.one_lt_rpow (by norm_num) (by linarith)

/-- A cutoff at the population sample scale gives the precise high-dimensional
power, with an explicit constant for both terminal and coarse-scale terms. -/
theorem exists_dyadic_matching_cutoff {q m A : ℝ} (hq : 4 < q) (hm : 1 ≤ m)
    (hA : 0 ≤ A) :
    ∃ K : ℕ, m * (1 / 4 : ℝ) ^ K +
        A * Real.sqrt m * (dyadicFluctuationRatio q) ^ K /
          (dyadicFluctuationRatio q - 1) ≤
      (4 + A / (dyadicFluctuationRatio q - 1)) * m ^ (1 - 2 / q) := by
  have hq0 : 0 < q := by linarith
  have hm0 : 0 < m := lt_of_lt_of_le zero_lt_one hm
  have ha : 0 < q / 2 - 2 := by linarith
  have hR := one_lt_dyadicFluctuationRatio hq
  have hs1 : 1 ≤ m ^ (1 / q) := Real.one_le_rpow hm (by positivity)
  obtain ⟨K, hKlo, hKhi⟩ := exists_nat_pow_near hs1 (by norm_num : (1 : ℝ) < 2)
  refine ⟨K, ?_⟩
  let t : ℝ := 2 ^ K
  let s : ℝ := m ^ (1 / q)
  let g : ℝ := m ^ (1 - 2 / q)
  have ht : 0 < t := by dsimp [t]; positivity
  have hs : 0 < s := Real.rpow_pos_of_pos hm0 _
  have hg : 0 < g := Real.rpow_pos_of_pos hm0 _
  have hsbound : s < 2 * t := by simpa only [pow_succ, mul_comm] using hKhi
  have hsg : g * s ^ 2 = m := by
    dsimp [g, s]
    rw [← Real.rpow_natCast _ 2, ← Real.rpow_mul hm0.le, ← Real.rpow_add hm0]
    have he : 1 - 2 / q + 1 / q * (2 : ℝ) = 1 := by ring
    norm_num only [Nat.cast_ofNat]
    rw [he, Real.rpow_one]
  have hbaseid : (1 / 4 : ℝ) ^ K * t ^ 2 = 1 := by
    dsimp [t]
    rw [← pow_mul, Nat.mul_comm K 2, pow_mul, ← mul_pow]
    norm_num
  have hbase : m * (1 / 4 : ℝ) ^ K ≤ 4 * g := by
    apply (mul_le_mul_iff_of_pos_right (sq_pos_of_pos ht)).mp
    have hs2 : s ^ 2 ≤ 4 * t ^ 2 := by nlinarith
    have hh := mul_le_mul_of_nonneg_left hs2 hg.le
    rw [hsg] at hh
    nlinarith [hbaseid]
  have hRp : (dyadicFluctuationRatio q) ^ K = t ^ (q / 2 - 2) := by
    dsimp [dyadicFluctuationRatio, t]
    rw [← Real.rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 2),
      ← Real.rpow_natCast_mul (by norm_num : (0 : ℝ) ≤ 2)]
    congr 1
    ring
  have hupper : (dyadicFluctuationRatio q) ^ K ≤ s ^ (q / 2 - 2) := by
    rw [hRp]
    exact Real.rpow_le_rpow ht.le hKlo ha.le
  have hpower : Real.sqrt m * s ^ (q / 2 - 2) = g := by
    dsimp [s, g]
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hm0.le, ← Real.rpow_add hm0]
    congr 1
    field_simp
    ring
  have hcoarse : A * Real.sqrt m * (dyadicFluctuationRatio q) ^ K /
      (dyadicFluctuationRatio q - 1) ≤ A / (dyadicFluctuationRatio q - 1) * g := by
    have hh := mul_le_mul_of_nonneg_left hupper
      (mul_nonneg hA (Real.sqrt_nonneg m))
    apply (div_le_iff₀ (sub_pos.mpr hR)).mpr
    calc
      _ ≤ A * Real.sqrt m * s ^ (q / 2 - 2) := hh
      _ = A * g := by rw [mul_assoc, hpower]
      _ = _ := by field_simp [ne_of_gt (sub_pos.mpr hR)]
  exact (add_le_add hbase hcoarse).trans_eq (by dsimp [g]; ring)

/-- A dyadic histogram term is bounded by its dimension-only geometric ratio. -/
theorem dyadicCube_fluctuation_term_le (q k : ℕ) {m : ℝ} (hm : 0 ≤ m) :
    (1 / 4 : ℝ) ^ k * Real.sqrt (2 * m * ((2 : ℝ) ^ (k + 1) + 1) ^ q) ≤
      Real.sqrt (2 * m) * (2 : ℝ) ^ q * (dyadicFluctuationRatio q) ^ k := by
  have hp : (1 : ℝ) ≤ 2 ^ (k + 1) := one_le_pow₀ (by norm_num)
  have hbase : (2 : ℝ) ^ (k + 1) + 1 ≤ 2 ^ (k + 2) := by
    rw [show k + 2 = (k + 1) + 1 by omega, pow_succ (2 : ℝ) (k + 1)]
    linarith
  have hpow := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ 2 ^ (k + 1) + 1) hbase q
  have hle := mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt
    (mul_le_mul_of_nonneg_left hpow (by positivity : (0 : ℝ) ≤ 2 * m)))
      (by positivity : (0 : ℝ) ≤ (1 / 4 : ℝ) ^ k)
  apply hle.trans_eq
  rw [Real.sqrt_mul (by positivity : (0 : ℝ) ≤ 2 * m)]
  have hsp : Real.sqrt (((2 : ℝ) ^ (k + 2)) ^ q) =
      (Real.sqrt ((2 : ℝ) ^ q)) ^ (k + 2) := by
    rw [← pow_mul, Nat.mul_comm (k + 2) q, pow_mul]
    simp only [Real.sqrt_eq_rpow]
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity : (0 : ℝ) ≤ 2 ^ q),
      mul_comm, Real.rpow_mul_natCast (by positivity : (0 : ℝ) ≤ 2 ^ q)]
  have hr : Real.sqrt ((2 : ℝ) ^ q) / 4 = dyadicFluctuationRatio q := by
    unfold dyadicFluctuationRatio
    rw [Real.rpow_sub (by norm_num : (0 : ℝ) < 2)]
    norm_num only [Real.rpow_natCast, show (2 : ℝ) ^ (2 : ℝ) = 4 by norm_num]
    congr 1
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    congr 1
    ring
  rw [hsp, pow_add, Real.sq_sqrt (by positivity : (0 : ℝ) ≤ 2 ^ q), ← hr]
  simp only [div_pow, one_pow]
  ring

/-- The full finite-cutoff expression is bounded by one geometric sum. -/
theorem dyadicCube_multiscale_le (q K : ℕ) (hq : 4 < q) {m : ℝ} (hm : 0 ≤ m) :
    m * (1 / 4 : ℝ) ^ K + (1 / 2 : ℝ) *
      (∑ k ∈ Finset.range K, (1 / 4 : ℝ) ^ k *
        Real.sqrt (2 * m * ((2 : ℝ) ^ (k + 1) + 1) ^ q)) ≤
    m * (1 / 4 : ℝ) ^ K + ((2 : ℝ) ^ q * Real.sqrt 2) * Real.sqrt m *
      (dyadicFluctuationRatio q) ^ K / (dyadicFluctuationRatio q - 1) := by
  have hqR : (4 : ℝ) < q := by exact_mod_cast hq
  have hR := one_lt_dyadicFluctuationRatio hqR
  have hs := Finset.sum_le_sum (s := Finset.range K)
    (fun k _ ↦ dyadicCube_fluctuation_term_le q k hm)
  have hsum0 : 0 ≤ ∑ k ∈ Finset.range K, (1 / 4 : ℝ) ^ k *
      Real.sqrt (2 * m * ((2 : ℝ) ^ (k + 1) + 1) ^ q) := by positivity
  have hhalf : (1 / 2 : ℝ) * (∑ k ∈ Finset.range K, (1 / 4 : ℝ) ^ k *
      Real.sqrt (2 * m * ((2 : ℝ) ^ (k + 1) + 1) ^ q)) ≤
      ∑ k ∈ Finset.range K, (1 / 4 : ℝ) ^ k *
        Real.sqrt (2 * m * ((2 : ℝ) ^ (k + 1) + 1) ^ q) := by linarith
  apply add_le_add le_rfl
  apply (hhalf.trans hs).trans
  rw [← Finset.mul_sum, geom_sum_eq hR.ne' K]
  have hsqrt : Real.sqrt (2 * m) = Real.sqrt 2 * Real.sqrt m :=
    Real.sqrt_mul (by norm_num) m
  rw [hsqrt]
  have hc : 0 ≤ Real.sqrt 2 * Real.sqrt m * (2 : ℝ) ^ q := by positivity
  have hh := mul_le_mul_of_nonneg_left
    (div_le_div_of_nonneg_right (show dyadicFluctuationRatio q ^ K - 1 ≤
      dyadicFluctuationRatio q ^ K by linarith) (sub_pos.mpr hR).le) hc
  convert hh using 1
  ring

/-- Explicit dimension-only constant for arbitrary laws on the closed unit cube. -/
def dyadicMatchingConstant (q : ℕ) : ℝ :=
  4 + ((2 : ℝ) ^ q * Real.sqrt 2) / (dyadicFluctuationRatio q - 1)

theorem dyadicMatchingConstant_pos {q : ℕ} (hq : 4 < q) :
    0 < dyadicMatchingConstant q := by
  have hqR : (4 : ℝ) < q := by exact_mod_cast hq
  have hR := one_lt_dyadicFluctuationRatio hqR
  unfold dyadicMatchingConstant
  positivity

/-- Finite-depth squared matching estimates admit a cutoff at the correct rate. -/
theorem exists_dyadicCube_rate_cutoff {q : ℕ} (hq : 4 < q) {m : ℝ} (hm : 1 ≤ m) :
    ∃ K : ℕ, m * (1 / 4 : ℝ) ^ K + (1 / 2 : ℝ) *
      (∑ k ∈ Finset.range K, (1 / 4 : ℝ) ^ k *
        Real.sqrt (2 * m * ((2 : ℝ) ^ (k + 1) + 1) ^ q)) ≤
      dyadicMatchingConstant q * m ^ (1 - 2 / (q : ℝ)) := by
  have hqR : (4 : ℝ) < q := by exact_mod_cast hq
  obtain ⟨K, hK⟩ := exists_dyadic_matching_cutoff (A := (2 : ℝ) ^ q * Real.sqrt 2)
    hqR hm (by positivity)
  exact ⟨K, (dyadicCube_multiscale_le q K hq (by linarith)).trans hK⟩

end OTSelector.Reconstruction
