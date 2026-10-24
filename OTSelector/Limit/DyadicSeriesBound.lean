import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Field.GeomSum
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# The dyadic geometric-series bound

This module isolates the pure real-analysis estimate behind the upper dyadic
matching lemma of the paper.  At level `k` the expected color discrepancy is
bounded by `min (2 m) (sqrt (2 m * 2 ^ (k * q)))`, and each discrepancy costs a
factor `(1 / 4) ^ k`.  The paper uses the two displayed constants `4 q` and
`8 q`; here we keep them, so the reader can compare with
`lem:general-upper-dyadic`.

## The requested inequality and its correction

The literal statement sometimes proposed for this step is

`m * (4 q * (1/4)^K) + (1/2) * sum_{k<K} 8 q (1/4)^k sqrt (2 m 2^(k q))
  <= C * (max 1 m) ^ (1 - 2/q)`

for *every* `m` and *every* `K`.  That statement is false for two independent
reasons.

* At `K = 0` it reads `4 q m <= C * (max 1 m) ^ (1 - 2/q)`, which fails as
  `m -> infinity` because `1 - 2/q < 1`.
* For fixed `m >= 1` and `K -> infinity` the summand grows like
  `(2^(q/2 - 2))^k` with `2^(q/2 - 2) > 1`, so the left side is unbounded
  while the right side is constant.

The paper itself caps the discrepancy by `m`, which gives the true
uniform-in-`K` finite-depth expression formalized below as
`exists_dyadic_series_bound`: for every `m` and `K`,
`sum_{k <= K} 4 q (1/4)^k min (2m) (sqrt (2 m 2^(kq)))` is bounded by
`C * (max 1 m) ^ (1 - 2/q)`.  The summand is the paper's
`min (2m, sqrt (2m) 2^(kq/2))` after moving `(1/4)^k` inside.

The version with the exact left side requested above, including the finite
stopping-depth term `m * 4 q * (1/4)^K`, is
`exists_dyadic_series_bound_of_depth`.  There `K` is tied to `m` by the two
natural crossing conditions
`max 1 m <= 2^(Kq)` and `2^((K-1)q) <= max 1 m`; these say precisely that the
stopping depth is at (or one level past) the first dyadic scale whose cell
count is comparable to the sample size.  Without such a depth restriction the
displayed inequality has no finite constant.

## Main ingredients

* `sqrt_two_mul_two_pow`: the exact one-level factorisation
  `sqrt (2 m 2^(kq)) = sqrt (2m) * sqrt (2^(kq))`.
* `quarter_pow_mul_sqrt_two_pow`: after pulling out `sqrt (2m)`, the remaining
  weight is the pure geometric term `r^k`, where `r = 2^(q/2 - 2) > 1`.
* `sum_range_ratio_le_rpow` and `sum_range_ratio_le_pow_pred`: the geometric
  series is dominated by its last term, with explicit constant `r / (r - 1)`.
  The cutoff for the min-version is `floor (log_2 (max 1 m) / q) + 1`, where
  the two branches `sqrt (...)` and `2m` balance.
-/

open scoped BigOperators
open Filter

namespace OTSelector

noncomputable section

/-- The common ratio `r = 2 ^ (q / 2 - 2)` of the weighted discrepancy series.
For `q > 4` this is strictly larger than one. -/
def dyadicRatio (q : ℕ) : ℝ := (2 : ℝ) ^ ((q : ℝ) / 2 - 2)

/-- One-level factorisation of the square root appearing in the dyadic
discrepancy bound. -/
theorem sqrt_two_mul_two_pow (m k q : ℕ) :
    Real.sqrt (2 * (m : ℝ) * (2 : ℝ) ^ (k * q)) =
      Real.sqrt (2 * (m : ℝ)) * Real.sqrt ((2 : ℝ) ^ (k * q)) := by
  rw [show (2 : ℝ) * (m : ℝ) * (2 : ℝ) ^ (k * q) =
      ((2 : ℝ) * (m : ℝ)) * (2 : ℝ) ^ (k * q) by ring]
  exact Real.sqrt_mul (by positivity) _

/-- For a nonnegative base, the square root of a natural power is the
corresponding real power with half the exponent. -/
theorem sqrt_two_pow_eq_rpow (k q : ℕ) :
    Real.sqrt ((2 : ℝ) ^ (k * q)) = (2 : ℝ) ^ (((k * q : ℕ) : ℝ) / 2) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast (2 : ℝ) (k * q),
    ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
  congr 1
  ring

/-- The base case of the geometric reduction: one power of `1/4` together with
`sqrt (2^q)` is exactly `dyadicRatio q`. -/
theorem quarter_mul_sqrt_two_pow (q : ℕ) :
    (1 / 4 : ℝ) * Real.sqrt ((2 : ℝ) ^ q) = dyadicRatio q := by
  unfold dyadicRatio
  rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast (2 : ℝ) q,
    ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
  have hbase : (1 / 4 : ℝ) = (2 : ℝ) ^ (-2 : ℝ) := by
    norm_num [Real.rpow_neg, Real.rpow_natCast]
  rw [hbase, ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
  congr 1
  ring

/-- The weighted discrepancy term `(1/4)^k * sqrt (2^(kq))` is the pure
geometric term `r^k`, where `r = 2^(q/2 - 2)`. -/
theorem quarter_pow_mul_sqrt_two_pow (k q : ℕ) :
    ((1 / 4 : ℝ) ^ k) * Real.sqrt ((2 : ℝ) ^ (k * q)) = (dyadicRatio q) ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
      have hexp : (k + 1) * q = k * q + q := by ring
      calc ((1 / 4 : ℝ) ^ (k + 1)) * Real.sqrt ((2 : ℝ) ^ ((k + 1) * q))
          = (((1 / 4 : ℝ) ^ k) * (1 / 4)) *
              (Real.sqrt ((2 : ℝ) ^ (k * q)) * Real.sqrt ((2 : ℝ) ^ q)) := by
              rw [pow_succ, hexp, pow_add, Real.sqrt_mul (by positivity)]
        _ = (((1 / 4 : ℝ) ^ k) * Real.sqrt ((2 : ℝ) ^ (k * q))) *
              ((1 / 4 : ℝ) * Real.sqrt ((2 : ℝ) ^ q)) := by ring
        _ = (dyadicRatio q) ^ k * dyadicRatio q := by
              rw [ih, quarter_mul_sqrt_two_pow]
        _ = (dyadicRatio q) ^ (k + 1) := by rw [pow_succ]

/-- For `q > 4` the geometric ratio `2^(q/2 - 2)` is strictly larger than
one. -/
theorem one_lt_dyadicRatio {q : ℕ} (hq : 4 < q) : 1 < dyadicRatio q := by
  have hq5 : (5 : ℕ) ≤ q := by omega
  have hq5' : (5 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq5
  have hexp : (0 : ℝ) < (q : ℝ) / 2 - 2 := by nlinarith
  simpa [dyadicRatio] using
    Real.one_lt_rpow (by norm_num : (1 : ℝ) < 2) hexp

/-- A partial geometric series with ratio `r > 1` is bounded by its last term
times `r / (r - 1)`, expressed through a real exponent `x` with
`K <= x + 1`. -/
theorem sum_range_ratio_le_rpow {r x : ℝ} (hr : 1 < r) (K : ℕ)
    (hK : (K : ℝ) ≤ x + 1) :
    ∑ k ∈ Finset.range K, r ^ k ≤ (r / (r - 1)) * r ^ x := by
  have hrne : r ≠ 1 := ne_of_gt hr
  have hrpos : 0 < r := lt_trans zero_lt_one hr
  have hpos : 0 < r - 1 := sub_pos.mpr hr
  rw [geom_sum_eq hrne]
  have hKpow : r ^ K ≤ r ^ (x + 1) := by
    rw [← Real.rpow_natCast r K]
    exact Real.rpow_le_rpow_of_exponent_le (le_of_lt hr) hK
  calc (r ^ K - 1) / (r - 1) ≤ r ^ K / (r - 1) := by
        rw [div_le_div_iff_of_pos_right hpos]
        linarith
    _ ≤ r ^ (x + 1) / (r - 1) := by
        rw [div_le_div_iff_of_pos_right hpos]
        linarith
    _ = (r / (r - 1)) * r ^ x := by
        rw [Real.rpow_add hrpos, Real.rpow_one]
        ring

/-- A partial geometric series with ratio `r > 1` is bounded by
`r ^ (K - 1)` times `r / (r - 1)`; the empty sum also satisfies the bound. -/
theorem sum_range_ratio_le_pow_pred {r : ℝ} (hr : 1 < r) (K : ℕ) :
    ∑ k ∈ Finset.range K, r ^ k ≤ (r / (r - 1)) * r ^ (K - 1) := by
  cases K with
  | zero =>
      simp only [Finset.range_zero, Finset.sum_empty, Nat.zero_sub, pow_zero]
      simpa using div_nonneg (le_of_lt (lt_trans zero_lt_one hr)) (sub_pos.mpr hr).le
  | succ n =>
      have hrne : r ≠ 1 := ne_of_gt hr
      have hpos : 0 < r - 1 := sub_pos.mpr hr
      rw [geom_sum_eq hrne]
      have hsub : n + 1 - 1 = n := Nat.add_sub_cancel _ _
      rw [hsub, pow_succ]
      calc (r ^ n * r - 1) / (r - 1) ≤ (r ^ n * r) / (r - 1) := by
            rw [div_le_div_iff_of_pos_right hpos]
            linarith
        _ = (r / (r - 1)) * r ^ n := by ring

/-- The partial geometric series with ratio `1/4` is bounded by `4/3`. -/
theorem sum_range_quarter_le (K : ℕ) :
    ∑ k ∈ Finset.range K, ((1 / 4 : ℝ) ^ k) ≤ 4 / 3 := by
  rw [geom_sum_eq (by norm_num : (1 / 4 : ℝ) ≠ 1)]
  rw [show ((1 / 4 : ℝ) ^ K - 1) / (1 / 4 - 1) =
      (1 - (1 / 4 : ℝ) ^ K) / (3 / 4) by ring]
  rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 3 / 4)]
  nlinarith [show (0 : ℝ) ≤ (1 / 4 : ℝ) ^ K by positivity]

/-- The weighted square-root summand with the factor `1/2` and `8 q` is a
constant times `sqrt (2m)` and the geometric term `r^k`. -/
theorem weighted_sqrt_eq (m k q : ℕ) :
    (1 / 2 : ℝ) * ((8 * (q : ℝ)) * (1 / 4 : ℝ) ^ k *
      Real.sqrt (2 * (m : ℝ) * (2 : ℝ) ^ (k * q))) =
    4 * (q : ℝ) * Real.sqrt (2 * (m : ℝ)) * (dyadicRatio q) ^ k := by
  rw [sqrt_two_mul_two_pow m k q]
  calc (1 / 2 : ℝ) * ((8 * (q : ℝ)) * (1 / 4 : ℝ) ^ k *
        (Real.sqrt (2 * (m : ℝ)) * Real.sqrt ((2 : ℝ) ^ (k * q))))
      = 4 * (q : ℝ) * Real.sqrt (2 * (m : ℝ)) *
          (((1 / 4 : ℝ) ^ k) * Real.sqrt ((2 : ℝ) ^ (k * q))) := by ring
    _ = 4 * (q : ℝ) * Real.sqrt (2 * (m : ℝ)) * (dyadicRatio q) ^ k := by
        rw [quarter_pow_mul_sqrt_two_pow]

/-- `(1/4)^x = M^(-2/q)` when `x = log_2 M / q`. -/
theorem quarter_rpow_logb_div (q : ℕ) (M : ℝ) (hM : 0 < M)
    (hq : (q : ℝ) ≠ 0) :
    (1 / 4 : ℝ) ^ (Real.logb 2 M / (q : ℝ)) = M ^ (-(2 / (q : ℝ))) := by
  have h2 : (0 : ℝ) ≤ 2 := by norm_num
  have hbase : (1 / 4 : ℝ) = (2 : ℝ) ^ (-2 : ℝ) := by
    norm_num [Real.rpow_neg, Real.rpow_natCast]
  rw [hbase, ← Real.rpow_mul h2]
  have hexp : (-2 : ℝ) * (Real.logb 2 M / (q : ℝ)) =
      Real.logb 2 M * (-(2 / (q : ℝ))) := by
    field_simp
  rw [hexp, Real.rpow_mul h2]
  rw [Real.rpow_logb (by norm_num : (0 : ℝ) < 2)
    (by norm_num : (2 : ℝ) ≠ 1) hM]

/-- `r^x = M^(1/2 - 2/q)` when `r = 2^(q/2 - 2)` and `x = log_2 M / q`. -/
theorem dyadicRatio_rpow_logb_div (q : ℕ) (M : ℝ) (hM : 0 < M)
    (hq : (q : ℝ) ≠ 0) :
    (dyadicRatio q) ^ (Real.logb 2 M / (q : ℝ)) =
      M ^ ((1 : ℝ) / 2 - 2 / (q : ℝ)) := by
  unfold dyadicRatio
  rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
  have hexp : ((q : ℝ) / 2 - 2) * (Real.logb 2 M / (q : ℝ)) =
      Real.logb 2 M * ((1 : ℝ) / 2 - 2 / (q : ℝ)) := by
    field_simp
  rw [hexp, Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
  rw [Real.rpow_logb (by norm_num : (0 : ℝ) < 2)
    (by norm_num : (2 : ℝ) ≠ 1) hM]

/-- `(2^(Kq))^(-2/q) = (1/4)^K` for `q ≠ 0`. -/
theorem two_pow_mul_rpow_neg_eq_quarter_pow (K q : ℕ) (hq : (q : ℝ) ≠ 0) :
    ((2 : ℝ) ^ (K * q)) ^ (-(2 / (q : ℝ))) = (1 / 4 : ℝ) ^ K := by
  have h2 : (0 : ℝ) ≤ 2 := by norm_num
  rw [← Real.rpow_natCast (2 : ℝ) (K * q), ← Real.rpow_mul h2]
  have hexp : (((K * q : ℕ) : ℝ)) * (-(2 / (q : ℝ))) = -2 * (K : ℝ) := by
    push_cast
    field_simp
  rw [hexp]
  have hbase : (1 / 4 : ℝ) = (2 : ℝ) ^ (-2 : ℝ) := by
    norm_num [Real.rpow_neg, Real.rpow_natCast]
  rw [hbase, ← Real.rpow_natCast ((2 : ℝ) ^ (-2 : ℝ)) K,
    ← Real.rpow_mul h2]

/-- `M^(1/2) * M^(1/2 - 2/q) = M^(1 - 2/q)` for `M > 0`. -/
theorem rpow_half_mul_rpow_half_sub (q : ℕ) (M : ℝ) (hM : 0 < M) :
    M ^ ((1 : ℝ) / 2) * M ^ ((1 : ℝ) / 2 - 2 / (q : ℝ)) =
      M ^ (1 - 2 / (q : ℝ)) := by
  rw [← Real.rpow_add hM]
  congr 1
  ring

/-- `M * M^(-2/q) = M^(1 - 2/q)` for `M > 0`. -/
theorem mul_rpow_neg_eq_rpow (q : ℕ) (M : ℝ) (hM : 0 < M) :
    M * M ^ (-(2 / (q : ℝ))) = M ^ (1 - 2 / (q : ℝ)) := by
  calc M * M ^ (-(2 / (q : ℝ))) = M ^ (1 : ℝ) * M ^ (-(2 / (q : ℝ))) := by
        rw [Real.rpow_one]
    _ = M ^ ((1 : ℝ) + (-(2 / (q : ℝ)))) := by rw [Real.rpow_add hM]
    _ = M ^ (1 - 2 / (q : ℝ)) := by congr 1

/-- The min-capped finite-depth dyadic sum is uniformly bounded in the depth.
This is the paper's geometric-series summation after inserting the cap
`min (2m) (sqrt (2 m 2^(kq)))` at every level. -/
theorem dyadic_min_sum_le (q : ℕ) (hq : 4 < q) (m N : ℕ) :
    (∑ k ∈ Finset.range N,
      (1 / 2 : ℝ) * ((8 * (q : ℝ)) * (1 / 4 : ℝ) ^ k *
        min (2 * (m : ℝ)) (Real.sqrt (2 * (m : ℝ) * (2 : ℝ) ^ (k * q)))))
      ≤ (4 * (q : ℝ) * Real.sqrt 2 * (dyadicRatio q / (dyadicRatio q - 1)) +
          (32 / 3) * (q : ℝ)) * (max 1 (m : ℝ)) ^ (1 - 2 / (q : ℝ)) := by
  let M : ℝ := max 1 (m : ℝ)
  let x : ℝ := Real.logb 2 M / (q : ℝ)
  let N₀ : ℕ := Nat.floor x + 1
  let r : ℝ := dyadicRatio q
  let f : ℕ → ℝ := fun k =>
    (1 / 2 : ℝ) * ((8 * (q : ℝ)) * (1 / 4 : ℝ) ^ k *
      min (2 * (m : ℝ)) (Real.sqrt (2 * (m : ℝ) * (2 : ℝ) ^ (k * q))))
  have hq5 : 5 ≤ q := by omega
  have hqpos_nat : 0 < q := by omega
  have hqpos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hqpos_nat
  have hqne : (q : ℝ) ≠ 0 := ne_of_gt hqpos
  have hr1 : 1 < r := by simpa [r] using one_lt_dyadicRatio hq
  have hr0 : 0 ≤ r := le_of_lt (lt_trans zero_lt_one hr1)
  have hrm1 : 0 < r - 1 := sub_pos.mpr hr1
  have hratio_nonneg : 0 ≤ r / (r - 1) := div_nonneg hr0 hrm1.le
  have hM1 : 1 ≤ M := le_max_left _ _
  have hMpos : 0 < M := lt_of_lt_of_le zero_lt_one hM1
  have hmM : (m : ℝ) ≤ M := le_max_right _ _
  have hx_nonneg : 0 ≤ x := by
    have hlog : 0 ≤ Real.logb 2 M :=
      Real.logb_nonneg (by norm_num : (1 : ℝ) < 2) hM1
    exact div_nonneg hlog hqpos.le
  have hN₀_gt : x < (N₀ : ℝ) := by
    have h := Nat.lt_floor_add_one x
    simpa [N₀] using h
  have hN₀_le : (N₀ : ℝ) ≤ x + 1 := by
    have h := Nat.floor_le hx_nonneg
    simp only [N₀]
    push_cast
    linarith
  have hN₀_pos : 1 ≤ N₀ := by
    have : (0 : ℝ) ≤ x := hx_nonneg
    have h := Nat.floor_le hx_nonneg
    have : (0 : ℕ) ≤ Nat.floor x := Nat.zero_le _
    dsimp [N₀]
    omega
  have hf_small : ∀ k : ℕ,
      f k ≤ 4 * (q : ℝ) * Real.sqrt (2 * (m : ℝ)) * r ^ k := by
    intro k
    have hmin : min (2 * (m : ℝ))
        (Real.sqrt (2 * (m : ℝ) * (2 : ℝ) ^ (k * q))) ≤
        Real.sqrt (2 * (m : ℝ) * (2 : ℝ) ^ (k * q)) := min_le_right _ _
    calc f k
        = (1 / 2 : ℝ) * ((8 * (q : ℝ)) * (1 / 4 : ℝ) ^ k *
            min (2 * (m : ℝ))
              (Real.sqrt (2 * (m : ℝ) * (2 : ℝ) ^ (k * q)))) := by
            simp only [f]
        _ ≤ (1 / 2 : ℝ) * ((8 * (q : ℝ)) * (1 / 4 : ℝ) ^ k *
            Real.sqrt (2 * (m : ℝ) * (2 : ℝ) ^ (k * q))) := by
            gcongr
        _ = 4 * (q : ℝ) * Real.sqrt (2 * (m : ℝ)) * (dyadicRatio q) ^ k :=
            weighted_sqrt_eq m k q
        _ = 4 * (q : ℝ) * Real.sqrt (2 * (m : ℝ)) * r ^ k := by rfl
  have hf_big : ∀ k : ℕ,
      f k ≤ 8 * (q : ℝ) * (m : ℝ) * (1 / 4 : ℝ) ^ k := by
    intro k
    have hmin : min (2 * (m : ℝ))
        (Real.sqrt (2 * (m : ℝ) * (2 : ℝ) ^ (k * q))) ≤ 2 * (m : ℝ) :=
      min_le_left _ _
    calc f k
        = (1 / 2 : ℝ) * ((8 * (q : ℝ)) * (1 / 4 : ℝ) ^ k *
            min (2 * (m : ℝ))
              (Real.sqrt (2 * (m : ℝ) * (2 : ℝ) ^ (k * q)))) := by
            simp only [f]
        _ ≤ (1 / 2 : ℝ) * ((8 * (q : ℝ)) * (1 / 4 : ℝ) ^ k *
            (2 * (m : ℝ))) := by
            gcongr
        _ = 8 * (q : ℝ) * (m : ℝ) * (1 / 4 : ℝ) ^ k := by ring
  have hf_nonneg : ∀ k : ℕ, 0 ≤ f k := by
    intro k
    have hmin : 0 ≤ min (2 * (m : ℝ))
        (Real.sqrt (2 * (m : ℝ) * (2 : ℝ) ^ (k * q))) :=
      le_min (by positivity) (Real.sqrt_nonneg _)
    simp only [f]
    exact mul_nonneg (by norm_num) (mul_nonneg (by positivity) hmin)
  have hsqrt_le : Real.sqrt (2 * (m : ℝ)) ≤ Real.sqrt 2 * M ^ ((1 : ℝ) / 2) := by
    calc Real.sqrt (2 * (m : ℝ)) ≤ Real.sqrt (2 * M) := by
          apply Real.sqrt_le_sqrt
          nlinarith [hmM]
      _ = Real.sqrt 2 * M ^ ((1 : ℝ) / 2) := by
          rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
          simp only [Real.sqrt_eq_rpow]
  have hrx : r ^ x = M ^ ((1 : ℝ) / 2 - 2 / (q : ℝ)) := by
    have h := dyadicRatio_rpow_logb_div q M hMpos hqne
    simpa [r, x] using h
  have hMpow := rpow_half_mul_rpow_half_sub q M hMpos
  have hsmall_part : ∀ K : ℕ, K ≤ N₀ →
      ∑ k ∈ Finset.range K, f k ≤
        4 * (q : ℝ) * Real.sqrt 2 * (r / (r - 1)) *
          M ^ (1 - 2 / (q : ℝ)) := by
    intro K hK
    have hsub : Finset.range K ⊆ Finset.range N₀ :=
      Finset.range_subset_range.mpr hK
    have hmono : ∑ k ∈ Finset.range K, f k ≤ ∑ k ∈ Finset.range N₀, f k :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub
        (fun i _ _ => hf_nonneg i)
    have hfirst : ∑ k ∈ Finset.range N₀, f k ≤
        4 * (q : ℝ) * Real.sqrt (2 * (m : ℝ)) *
          ∑ k ∈ Finset.range N₀, r ^ k := by
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum (fun k _ => hf_small k)
    have hgeo : ∑ k ∈ Finset.range N₀, r ^ k ≤ (r / (r - 1)) * r ^ x :=
      sum_range_ratio_le_rpow hr1 N₀ hN₀_le
    calc ∑ k ∈ Finset.range K, f k
        ≤ 4 * (q : ℝ) * Real.sqrt (2 * (m : ℝ)) *
            ∑ k ∈ Finset.range N₀, r ^ k := le_trans hmono hfirst
      _ ≤ 4 * (q : ℝ) * Real.sqrt (2 * (m : ℝ)) *
            ((r / (r - 1)) * r ^ x) := by
          exact mul_le_mul_of_nonneg_left hgeo
            (by positivity : (0 : ℝ) ≤
              4 * (q : ℝ) * Real.sqrt (2 * (m : ℝ)))
      _ ≤ 4 * (q : ℝ) * (Real.sqrt 2 * M ^ ((1 : ℝ) / 2)) *
            ((r / (r - 1)) * M ^ ((1 : ℝ) / 2 - 2 / (q : ℝ))) := by
          rw [hrx]
          have hleft : 4 * (q : ℝ) * Real.sqrt (2 * (m : ℝ)) ≤
              4 * (q : ℝ) * (Real.sqrt 2 * M ^ ((1 : ℝ) / 2)) :=
            mul_le_mul_of_nonneg_left hsqrt_le (by positivity)
          have hX : 0 ≤ (r / (r - 1)) *
              M ^ ((1 : ℝ) / 2 - 2 / (q : ℝ)) :=
            mul_nonneg hratio_nonneg (Real.rpow_nonneg hMpos.le _)
          exact mul_le_mul_of_nonneg_right hleft hX
      _ = (4 * (q : ℝ) * Real.sqrt 2 * (r / (r - 1))) *
            (M ^ ((1 : ℝ) / 2) * M ^ ((1 : ℝ) / 2 - 2 / (q : ℝ))) := by
          ring
      _ = 4 * (q : ℝ) * Real.sqrt 2 * (r / (r - 1)) *
            M ^ (1 - 2 / (q : ℝ)) := by
          rw [hMpow]
  have hquarter_rpow : (1 / 4 : ℝ) ^ x = M ^ (-(2 / (q : ℝ))) := by
    have h := quarter_rpow_logb_div q M hMpos hqne
    simpa [x] using h
  have hquarter : (1 / 4 : ℝ) ^ N₀ ≤ M ^ (-(2 / (q : ℝ))) := by
    have hle : (1 / 4 : ℝ) ^ N₀ ≤ (1 / 4 : ℝ) ^ x := by
      rw [← Real.rpow_natCast (1 / 4 : ℝ) N₀]
      exact Real.rpow_le_rpow_of_exponent_ge (by norm_num) (by norm_num)
        (le_of_lt hN₀_gt)
    rw [hquarter_rpow] at hle
    exact hle
  have hMM := mul_rpow_neg_eq_rpow q M hMpos
  have htail_part : ∀ L : ℕ,
      ∑ j ∈ Finset.range L, f (N₀ + j) ≤
        (32 / 3) * (q : ℝ) * M ^ (1 - 2 / (q : ℝ)) := by
    intro L
    have hsum_le : ∑ j ∈ Finset.range L, f (N₀ + j) ≤
        ∑ j ∈ Finset.range L,
          8 * (q : ℝ) * (m : ℝ) * (1 / 4 : ℝ) ^ (N₀ + j) :=
      Finset.sum_le_sum (fun j _ => hf_big (N₀ + j))
    have hfactor : ∑ j ∈ Finset.range L,
          8 * (q : ℝ) * (m : ℝ) * (1 / 4 : ℝ) ^ (N₀ + j) =
        8 * (q : ℝ) * (m : ℝ) * ((1 / 4 : ℝ) ^ N₀) *
          ∑ j ∈ Finset.range L, (1 / 4 : ℝ) ^ j := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      rw [pow_add]
      ring
    have hquarter_sum : ∑ j ∈ Finset.range L, (1 / 4 : ℝ) ^ j ≤ 4 / 3 :=
      sum_range_quarter_le L
    have hmul_le : 8 * (q : ℝ) * (m : ℝ) * ((1 / 4 : ℝ) ^ N₀) *
          ∑ j ∈ Finset.range L, (1 / 4 : ℝ) ^ j ≤
        8 * (q : ℝ) * (m : ℝ) * ((1 / 4 : ℝ) ^ N₀) * (4 / 3) := by
      gcongr
    calc ∑ j ∈ Finset.range L, f (N₀ + j)
        ≤ ∑ j ∈ Finset.range L,
            8 * (q : ℝ) * (m : ℝ) * (1 / 4 : ℝ) ^ (N₀ + j) := hsum_le
      _ = 8 * (q : ℝ) * (m : ℝ) * ((1 / 4 : ℝ) ^ N₀) *
            ∑ j ∈ Finset.range L, (1 / 4 : ℝ) ^ j := hfactor
      _ ≤ 8 * (q : ℝ) * (m : ℝ) * ((1 / 4 : ℝ) ^ N₀) * (4 / 3) := hmul_le
      _ = (32 / 3) * (q : ℝ) * (m : ℝ) * ((1 / 4 : ℝ) ^ N₀) := by ring
      _ ≤ (32 / 3) * (q : ℝ) * M * M ^ (-(2 / (q : ℝ))) := by
          gcongr
      _ = (32 / 3) * (q : ℝ) * (M * M ^ (-(2 / (q : ℝ)))) := by ring
      _ = (32 / 3) * (q : ℝ) * M ^ (1 - 2 / (q : ℝ)) := by
          rw [hMM]
  by_cases hNK : N ≤ N₀
  · have h1 := hsmall_part N hNK
    have hB : 0 ≤ (32 / 3) * (q : ℝ) := by positivity
    have hP : 0 ≤ M ^ (1 - 2 / (q : ℝ)) := Real.rpow_nonneg hMpos.le _
    have hle : 4 * (q : ℝ) * Real.sqrt 2 * (r / (r - 1)) *
          M ^ (1 - 2 / (q : ℝ)) ≤
        (4 * (q : ℝ) * Real.sqrt 2 * (r / (r - 1)) +
          (32 / 3) * (q : ℝ)) * M ^ (1 - 2 / (q : ℝ)) := by
      calc 4 * (q : ℝ) * Real.sqrt 2 * (r / (r - 1)) *
            M ^ (1 - 2 / (q : ℝ))
          = (4 * (q : ℝ) * Real.sqrt 2 * (r / (r - 1))) *
              M ^ (1 - 2 / (q : ℝ)) := by ring
        _ ≤ (4 * (q : ℝ) * Real.sqrt 2 * (r / (r - 1)) +
              (32 / 3) * (q : ℝ)) * M ^ (1 - 2 / (q : ℝ)) :=
            mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hB) hP
    simpa only [M, r] using le_trans h1 hle
  · have hN₀N : N₀ ≤ N := le_of_lt (lt_of_not_ge hNK)
    obtain ⟨L, hL⟩ : ∃ L, N = N₀ + L :=
      ⟨N - N₀, (Nat.add_sub_of_le hN₀N).symm⟩
    rw [hL, Finset.sum_range_add]
    have h1 := hsmall_part N₀ le_rfl
    have h2 := htail_part L
    have htotal : ∑ k ∈ Finset.range N₀, f k +
          ∑ j ∈ Finset.range L, f (N₀ + j) ≤
        (4 * (q : ℝ) * Real.sqrt 2 * (r / (r - 1)) +
            (32 / 3) * (q : ℝ)) * M ^ (1 - 2 / (q : ℝ)) := by
      calc ∑ k ∈ Finset.range N₀, f k + ∑ j ∈ Finset.range L, f (N₀ + j)
          ≤ (4 * (q : ℝ) * Real.sqrt 2 * (r / (r - 1)) *
                M ^ (1 - 2 / (q : ℝ))) +
              ((32 / 3) * (q : ℝ) * M ^ (1 - 2 / (q : ℝ))) :=
            add_le_add h1 h2
        _ = (4 * (q : ℝ) * Real.sqrt 2 * (r / (r - 1)) +
              (32 / 3) * (q : ℝ)) * M ^ (1 - 2 / (q : ℝ)) := by ring
    simpa only [M, r] using htotal

/-- The paper's dyadic geometric-series bound, in its correct uniform form:
for every sample size `m` and every depth `K`, the min-capped level sum is at
most a constant times `(max 1 m)^(1 - 2/q)`.

The cap `min (2m) (sqrt (2 m 2^(kq)))` is essential: without it the summand
grows like `2^(k (q/2 - 2))` with `q/2 - 2 > 0`, so no bound uniform in `K`
can hold. -/
theorem exists_dyadic_series_bound (q : ℕ) (hq : 4 < q) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (m K : ℕ),
      (1 / 2) * ∑ k ∈ Finset.range (K + 1),
        (8 * (q : ℝ)) * (1 / 4 : ℝ) ^ k *
          min (2 * (m : ℝ)) (Real.sqrt (2 * (m : ℝ) * (2 : ℝ) ^ (k * q)))
      ≤ C * (max 1 (m : ℝ)) ^ (1 - 2 / (q : ℝ)) := by
  refine ⟨4 * (q : ℝ) * Real.sqrt 2 *
      (dyadicRatio q / (dyadicRatio q - 1)) + (32 / 3) * (q : ℝ), ?_, ?_⟩
  · have hq5 : 5 ≤ q := by omega
    have hqpos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast (by omega : 0 < q)
    have hr1 : 1 < dyadicRatio q := one_lt_dyadicRatio hq
    have hr0 : 0 ≤ dyadicRatio q :=
      le_of_lt (lt_trans zero_lt_one hr1)
    have hrm1 : 0 < dyadicRatio q - 1 := sub_pos.mpr hr1
    have hratio : 0 ≤ dyadicRatio q / (dyadicRatio q - 1) :=
      div_nonneg hr0 hrm1.le
    have hA : 0 ≤ 4 * (q : ℝ) * Real.sqrt 2 *
        (dyadicRatio q / (dyadicRatio q - 1)) := by positivity
    have hB : 0 ≤ (32 / 3) * (q : ℝ) := by positivity
    exact add_nonneg hA hB
  · intro m K
    rw [Finset.mul_sum]
    exact dyadic_min_sum_le q hq m (K + 1)

/-- The requested finite-depth inequality with the exact left side
`m * 4q * (1/4)^K + (1/2) * sum_{k<K} 8q (1/4)^k sqrt (2 m 2^(kq))`.

The two hypotheses tie the stopping depth `K` to the sample size.  They say
that `K` is the first dyadic level at which the cell count `2^(Kq)` has
reached the sample scale, up to one level: `max 1 m <= 2^(Kq)` and
`2^((K-1)q) <= max 1 m`.  For `K = 0` the second condition is `1 <= max 1 m`.

Without these conditions the displayed inequality is false; see the module
documentation for the two counterexamples. -/
theorem exists_dyadic_series_bound_of_depth (q : ℕ) (hq : 4 < q) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (m K : ℕ),
      max 1 (m : ℝ) ≤ (2 : ℝ) ^ (K * q) →
      (2 : ℝ) ^ ((K - 1) * q) ≤ max 1 (m : ℝ) →
      (m : ℝ) * ((4 * (q : ℝ)) * (1 / 4 : ℝ) ^ K) +
        (1 / 2) * ∑ k ∈ Finset.range K,
          (8 * (q : ℝ)) * (1 / 4 : ℝ) ^ k *
            Real.sqrt (2 * (m : ℝ) * (2 : ℝ) ^ (k * q))
      ≤ C * (max 1 (m : ℝ)) ^ (1 - 2 / (q : ℝ)) := by
  refine ⟨4 * (q : ℝ) +
      4 * (q : ℝ) * Real.sqrt 2 * (dyadicRatio q / (dyadicRatio q - 1)), ?_, ?_⟩
  · have hqpos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast (by omega : 0 < q)
    have hr1 : 1 < dyadicRatio q := one_lt_dyadicRatio hq
    have hr0 : 0 ≤ dyadicRatio q :=
      le_of_lt (lt_trans zero_lt_one hr1)
    have hrm1 : 0 < dyadicRatio q - 1 := sub_pos.mpr hr1
    have hratio : 0 ≤ dyadicRatio q / (dyadicRatio q - 1) :=
      div_nonneg hr0 hrm1.le
    have hA : 0 ≤ 4 * (q : ℝ) := by positivity
    have hB : 0 ≤ 4 * (q : ℝ) * Real.sqrt 2 *
        (dyadicRatio q / (dyadicRatio q - 1)) := by positivity
    exact add_nonneg hA hB
  · intro m K hlo hhi
    let M : ℝ := max 1 (m : ℝ)
    let r : ℝ := dyadicRatio q
    have hq5 : 5 ≤ q := by omega
    have hqpos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast (by omega : 0 < q)
    have hqne : (q : ℝ) ≠ 0 := ne_of_gt hqpos
    have hr1 : 1 < r := by simpa [r] using one_lt_dyadicRatio hq
    have hr0 : 0 ≤ r := le_of_lt (lt_trans zero_lt_one hr1)
    have hrm1 : 0 < r - 1 := sub_pos.mpr hr1
    have hM1 : 1 ≤ M := le_max_left _ _
    have hMpos : 0 < M := lt_of_lt_of_le zero_lt_one hM1
    have hmM : (m : ℝ) ≤ M := le_max_right _ _
    have hlo' : M ≤ (2 : ℝ) ^ (K * q) := by simpa [M] using hlo
    have hhi' : (2 : ℝ) ^ ((K - 1) * q) ≤ M := by simpa [M] using hhi
    have hexp_nonneg : (0 : ℝ) ≤ (1 : ℝ) / 2 - 2 / (q : ℝ) := by
      have hq4 : (4 : ℝ) < (q : ℝ) := by exact_mod_cast hq
      have : (0 : ℝ) < (q : ℝ) := hqpos
      field_simp
      nlinarith
    have hbase : (m : ℝ) * ((4 * (q : ℝ)) * (1 / 4 : ℝ) ^ K) ≤
        4 * (q : ℝ) * M ^ (1 - 2 / (q : ℝ)) := by
      have hquarter : (1 / 4 : ℝ) ^ K ≤ M ^ (-(2 / (q : ℝ))) := by
        rw [← two_pow_mul_rpow_neg_eq_quarter_pow K q hqne]
        exact Real.rpow_le_rpow_of_nonpos hMpos hlo'
          (neg_nonpos.mpr (by positivity))
      have hMM := mul_rpow_neg_eq_rpow q M hMpos
      calc (m : ℝ) * ((4 * (q : ℝ)) * (1 / 4 : ℝ) ^ K)
          = 4 * (q : ℝ) * (m : ℝ) * (1 / 4 : ℝ) ^ K := by ring
        _ ≤ 4 * (q : ℝ) * M * (1 / 4 : ℝ) ^ K := by gcongr
        _ ≤ 4 * (q : ℝ) * M * M ^ (-(2 / (q : ℝ))) := by gcongr
        _ = 4 * (q : ℝ) * (M * M ^ (-(2 / (q : ℝ)))) := by ring
        _ = 4 * (q : ℝ) * M ^ (1 - 2 / (q : ℝ)) := by rw [hMM]
    have hsum : (1 / 2) * ∑ k ∈ Finset.range K,
          (8 * (q : ℝ)) * (1 / 4 : ℝ) ^ k *
            Real.sqrt (2 * (m : ℝ) * (2 : ℝ) ^ (k * q)) ≤
        4 * (q : ℝ) * Real.sqrt 2 * (r / (r - 1)) *
          M ^ (1 - 2 / (q : ℝ)) := by
      rw [Finset.mul_sum]
      have hrewrite : ∑ k ∈ Finset.range K,
            (1 / 2) * ((8 * (q : ℝ)) * (1 / 4 : ℝ) ^ k *
              Real.sqrt (2 * (m : ℝ) * (2 : ℝ) ^ (k * q))) =
          4 * (q : ℝ) * Real.sqrt (2 * (m : ℝ)) *
            ∑ k ∈ Finset.range K, r ^ k := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k _
        simpa [r] using weighted_sqrt_eq m k q
      rw [hrewrite]
      have hgeo : ∑ k ∈ Finset.range K, r ^ k ≤ (r / (r - 1)) * r ^ (K - 1) :=
        sum_range_ratio_le_pow_pred hr1 K
      have hrpred : r ^ (K - 1) ≤ M ^ ((1 : ℝ) / 2 - 2 / (q : ℝ)) := by
        by_cases hK : K = 0
        · subst K
          simp only [Nat.zero_sub, pow_zero]
          exact Real.one_le_rpow hM1 hexp_nonneg
        · have hKpos : 0 < K := Nat.pos_of_ne_zero hK
          have hpow : ((2 : ℝ) ^ ((K - 1) * q)) ^
              ((1 : ℝ) / 2 - 2 / (q : ℝ)) ≤
              M ^ ((1 : ℝ) / 2 - 2 / (q : ℝ)) :=
            Real.rpow_le_rpow (by positivity) hhi' hexp_nonneg
          have hr_eq : r ^ (K - 1) =
              ((2 : ℝ) ^ ((K - 1) * q)) ^
                ((1 : ℝ) / 2 - 2 / (q : ℝ)) := by
            simp only [r, dyadicRatio]
            rw [← Real.rpow_natCast ((2 : ℝ) ^ ((q : ℝ) / 2 - 2)) (K - 1),
              ← Real.rpow_natCast (2 : ℝ) ((K - 1) * q),
              ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2),
              ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
            congr 1
            push_cast
            field_simp
          rw [hr_eq]
          exact hpow
      have hsqrt_le : Real.sqrt (2 * (m : ℝ)) ≤
          Real.sqrt 2 * M ^ ((1 : ℝ) / 2) := by
        calc Real.sqrt (2 * (m : ℝ)) ≤ Real.sqrt (2 * M) := by
              apply Real.sqrt_le_sqrt
              nlinarith [hmM]
          _ = Real.sqrt 2 * M ^ ((1 : ℝ) / 2) := by
              rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
              simp only [Real.sqrt_eq_rpow]
      have hMpow := rpow_half_mul_rpow_half_sub q M hMpos
      calc 4 * (q : ℝ) * Real.sqrt (2 * (m : ℝ)) *
            ∑ k ∈ Finset.range K, r ^ k
          ≤ 4 * (q : ℝ) * Real.sqrt (2 * (m : ℝ)) *
              ((r / (r - 1)) * r ^ (K - 1)) := by
            exact mul_le_mul_of_nonneg_left hgeo
              (by positivity : (0 : ℝ) ≤
                4 * (q : ℝ) * Real.sqrt (2 * (m : ℝ)))
        _ ≤ 4 * (q : ℝ) * Real.sqrt (2 * (m : ℝ)) *
              ((r / (r - 1)) * M ^ ((1 : ℝ) / 2 - 2 / (q : ℝ))) := by
            exact mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_left hrpred (div_nonneg hr0 hrm1.le))
              (by positivity : (0 : ℝ) ≤
                4 * (q : ℝ) * Real.sqrt (2 * (m : ℝ)))
        _ ≤ 4 * (q : ℝ) * (Real.sqrt 2 * M ^ ((1 : ℝ) / 2)) *
              ((r / (r - 1)) * M ^ ((1 : ℝ) / 2 - 2 / (q : ℝ))) := by
            have hleft : 4 * (q : ℝ) * Real.sqrt (2 * (m : ℝ)) ≤
                4 * (q : ℝ) * (Real.sqrt 2 * M ^ ((1 : ℝ) / 2)) :=
              mul_le_mul_of_nonneg_left hsqrt_le (by positivity)
            have hX : 0 ≤ (r / (r - 1)) *
                M ^ ((1 : ℝ) / 2 - 2 / (q : ℝ)) :=
              mul_nonneg (div_nonneg hr0 hrm1.le)
                (Real.rpow_nonneg hMpos.le _)
            exact mul_le_mul_of_nonneg_right hleft hX
        _ = (4 * (q : ℝ) * Real.sqrt 2 * (r / (r - 1))) *
              (M ^ ((1 : ℝ) / 2) * M ^ ((1 : ℝ) / 2 - 2 / (q : ℝ))) := by
            ring
        _ = 4 * (q : ℝ) * Real.sqrt 2 * (r / (r - 1)) *
              M ^ (1 - 2 / (q : ℝ)) := by
            rw [hMpow]
    have hP : 0 ≤ M ^ (1 - 2 / (q : ℝ)) := Real.rpow_nonneg hMpos.le _
    calc (m : ℝ) * ((4 * (q : ℝ)) * (1 / 4 : ℝ) ^ K) +
          (1 / 2) * ∑ k ∈ Finset.range K,
            (8 * (q : ℝ)) * (1 / 4 : ℝ) ^ k *
              Real.sqrt (2 * (m : ℝ) * (2 : ℝ) ^ (k * q))
        ≤ 4 * (q : ℝ) * M ^ (1 - 2 / (q : ℝ)) +
            4 * (q : ℝ) * Real.sqrt 2 * (r / (r - 1)) *
              M ^ (1 - 2 / (q : ℝ)) := add_le_add hbase hsum
      _ = (4 * (q : ℝ) +
            4 * (q : ℝ) * Real.sqrt 2 * (r / (r - 1))) *
            M ^ (1 - 2 / (q : ℝ)) := by ring

end

end OTSelector
