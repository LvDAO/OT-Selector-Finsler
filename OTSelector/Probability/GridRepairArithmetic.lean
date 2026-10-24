/-
Copyright (c) 2026 OT-Selector contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OT-Selector contributors
-/

import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic

/-!
# Arithmetic estimates for the weighted grid-repair discrepancy

This file contains the purely real-analytic Estimate used in the smooth-length
grid repair argument.  Writing `L ^ q = R / m ^ q`, the weighted grid-repair
discrepancy sum is bounded by a constant depending only on `q` times
`(C + |t| * G) * R * (L ^ (2 / q - 1 / 2) + L ^ (-1 / 2))`.

The proof is elementary: each square-root factor is controlled by a geometric
progression, and the two resulting geometric sums are estimated using
`2 ^ J ≤ 2 * m`.
-/

open scoped BigOperators

namespace OTSelector.Probability

/-- A geometric sum with ratio `r > 1` is bounded by `r / (r - 1) * r ^ J`. -/
private lemma geom_sum_Icc_le {r : ℝ} (hr : 1 < r) (J : ℕ) :
    ∑ k ∈ Finset.Icc 1 J, r ^ k ≤ r / (r - 1) * r ^ J := by
  have hr1 : r ≠ 1 := ne_of_gt hr
  have hrpos : 0 < r - 1 := by linarith
  rw [← Finset.Ico_add_one_right_eq_Icc (a := 1) (b := J)]
  rw [geom_sum_Ico (x := r) hr1 (m := 1) (n := J + 1) (by omega : 1 ≤ J + 1)]
  calc (r ^ (J + 1) - r ^ 1) / (r - 1) ≤ r ^ (J + 1) / (r - 1) := by
        apply div_le_div_of_nonneg_right _ (le_of_lt hrpos)
        rw [pow_one]
        linarith [pow_nonneg (le_of_lt (lt_trans zero_lt_one hr)) (J + 1)]
    _ = r / (r - 1) * r ^ J := by
        rw [pow_succ]
        field_simp

/-- The elementary square-root bound for a single block. -/
private lemma sqrt_block_le (q k : ℕ) (R : ℝ) (hR : 0 ≤ R) :
    Real.sqrt (2 * R * (((2 ^ k + 1) ^ q : ℕ) : ℝ)) ≤
      Real.sqrt (2 * R) * ((2 : ℝ) ^ ((q : ℝ) / 2)) ^ (k + 1) := by
  have hbase : 2 ^ k + 1 ≤ 2 ^ (k + 1) := by
    have h1 : (1 : ℕ) ≤ 2 ^ k := Nat.one_le_pow k 2 (by norm_num)
    have h2 : 2 ^ (k + 1) = 2 ^ k + 2 ^ k := by rw [pow_succ]; ring
    omega
  have hpow_nat : (2 ^ k + 1) ^ q ≤ (2 ^ (k + 1)) ^ q :=
    Nat.pow_le_pow_left hbase q
  have hpow : (((2 ^ k + 1) ^ q : ℕ) : ℝ) ≤ (((2 ^ (k + 1)) ^ q : ℕ) : ℝ) := by
    exact_mod_cast hpow_nat
  have h2R : 0 ≤ 2 * R := by positivity
  have hcast : (((2 ^ (k + 1)) ^ q : ℕ) : ℝ) = (2 : ℝ) ^ ((k + 1) * q) := by
    push_cast
    rw [← pow_mul]
  have hsqrt_eq :
      Real.sqrt (((2 ^ (k + 1)) ^ q : ℕ) : ℝ) =
        ((2 : ℝ) ^ ((q : ℝ) / 2)) ^ (k + 1) := by
    rw [hcast, Real.sqrt_eq_rpow, ← Real.rpow_natCast (2 : ℝ) ((k + 1) * q)]
    rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    rw [show ((((k + 1) * q : ℕ) : ℝ) * (1 / 2 : ℝ)) =
        ((q : ℝ) / 2) * ((k + 1 : ℕ) : ℝ) by push_cast; ring]
    rw [Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2), Real.rpow_natCast]
  calc Real.sqrt (2 * R * (((2 ^ k + 1) ^ q : ℕ) : ℝ))
      ≤ Real.sqrt (2 * R * (((2 ^ (k + 1)) ^ q : ℕ) : ℝ)) :=
        Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hpow h2R)
    _ = Real.sqrt (2 * R) * Real.sqrt (((2 ^ (k + 1)) ^ q : ℕ) : ℝ) :=
        Real.sqrt_mul h2R _
    _ = Real.sqrt (2 * R) * ((2 : ℝ) ^ ((q : ℝ) / 2)) ^ (k + 1) := by
        rw [hsqrt_eq]

/-- The kinetic `rpow` identity: `R * L ^ (2 / q - 1 / 2)` equals
`R ^ (2 / q) * sqrt R * m ^ (q / 2 - 2)` when `L = R / m ^ q`. -/
private lemma kinetic_rpow_identity {R m : ℝ} (hR : 0 < R) (hm : 0 < m)
    {q : ℕ} (hq : 0 < q) :
    R * (R / m ^ q) ^ (2 / (q : ℝ) - 1 / 2) =
      R ^ (2 / (q : ℝ)) * Real.sqrt R * m ^ ((q : ℝ) / 2 - 2) := by
  have hmq_pos : 0 < m ^ q := pow_pos hm q
  have hqR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have hz : (q : ℝ) * (2 / (q : ℝ) - 1 / 2) = -((q : ℝ) / 2 - 2) := by
    field_simp
    ring
  have hmqz : (m ^ q) ^ (2 / (q : ℝ) - 1 / 2) =
      (m ^ ((q : ℝ) / 2 - 2))⁻¹ := by
    calc (m ^ q) ^ (2 / (q : ℝ) - 1 / 2)
        = (m ^ (q : ℝ)) ^ (2 / (q : ℝ) - 1 / 2) := by
            rw [Real.rpow_natCast]
      _ = m ^ ((q : ℝ) * (2 / (q : ℝ) - 1 / 2)) :=
            (Real.rpow_mul (le_of_lt hm) (q : ℝ) _).symm
      _ = m ^ (-((q : ℝ) / 2 - 2)) := by rw [hz]
      _ = (m ^ ((q : ℝ) / 2 - 2))⁻¹ := Real.rpow_neg (le_of_lt hm) _
  have hdiv : (R / m ^ q) ^ (2 / (q : ℝ) - 1 / 2) =
      R ^ (2 / (q : ℝ) - 1 / 2) * m ^ ((q : ℝ) / 2 - 2) := by
    rw [Real.div_rpow (le_of_lt hR) (le_of_lt hmq_pos), hmqz, div_inv_eq_mul]
  have hRmul : R * R ^ (2 / (q : ℝ) - 1 / 2) =
      R ^ (2 / (q : ℝ)) * Real.sqrt R := by
    calc R * R ^ (2 / (q : ℝ) - 1 / 2)
        = R ^ (1 : ℝ) * R ^ (2 / (q : ℝ) - 1 / 2) := by rw [Real.rpow_one]
      _ = R ^ (1 + (2 / (q : ℝ) - 1 / 2)) := (Real.rpow_add hR 1 _).symm
      _ = R ^ (2 / (q : ℝ) + 1 / 2) := by congr 1; ring
      _ = R ^ (2 / (q : ℝ)) * R ^ (1 / 2) := Real.rpow_add hR _ _
      _ = R ^ (2 / (q : ℝ)) * Real.sqrt R := by rw [← Real.sqrt_eq_rpow]
  calc R * (R / m ^ q) ^ (2 / (q : ℝ) - 1 / 2)
      = R * (R ^ (2 / (q : ℝ) - 1 / 2) * m ^ ((q : ℝ) / 2 - 2)) := by
          rw [hdiv]
    _ = (R * R ^ (2 / (q : ℝ) - 1 / 2)) * m ^ ((q : ℝ) / 2 - 2) := by
          ring
    _ = (R ^ (2 / (q : ℝ)) * Real.sqrt R) * m ^ ((q : ℝ) / 2 - 2) := by
          rw [hRmul]
    _ = R ^ (2 / (q : ℝ)) * Real.sqrt R * m ^ ((q : ℝ) / 2 - 2) := by
          ring

/-- The probe `rpow` identity: `R * L ^ (-1 / 2)` equals
`sqrt R * m ^ (q / 2)` when `L = R / m ^ q`. -/
private lemma probe_rpow_identity {R m : ℝ} (hR : 0 < R) (hm : 0 < m)
    {q : ℕ} :
    R * (R / m ^ q) ^ ((-(1 / 2) : ℝ)) =
      Real.sqrt R * m ^ ((q : ℝ) / 2) := by
  have hmq_pos : 0 < m ^ q := pow_pos hm q
  have hmqz : (m ^ q) ^ ((-(1 / 2) : ℝ)) = (m ^ ((q : ℝ) / 2))⁻¹ := by
    calc (m ^ q) ^ ((-(1 / 2) : ℝ))
        = (m ^ (q : ℝ)) ^ ((-(1 / 2) : ℝ)) := by
            rw [Real.rpow_natCast]
      _ = m ^ ((q : ℝ) * ((-(1 / 2) : ℝ))) :=
            (Real.rpow_mul (le_of_lt hm) (q : ℝ) _).symm
      _ = m ^ (-((q : ℝ) / 2)) := by congr 1; ring
      _ = (m ^ ((q : ℝ) / 2))⁻¹ := Real.rpow_neg (le_of_lt hm) _
  have hdiv : (R / m ^ q) ^ ((-(1 / 2) : ℝ)) =
      R ^ ((-(1 / 2) : ℝ)) * m ^ ((q : ℝ) / 2) := by
    rw [Real.div_rpow (le_of_lt hR) (le_of_lt hmq_pos), hmqz, div_inv_eq_mul]
  have hRmul : R * R ^ ((-(1 / 2) : ℝ)) = Real.sqrt R := by
    calc R * R ^ ((-(1 / 2) : ℝ))
        = R ^ ((1 : ℝ)) * R ^ ((-(1 / 2) : ℝ)) := by rw [Real.rpow_one]
      _ = R ^ ((1 : ℝ) + (-(1 / 2) : ℝ)) :=
            (Real.rpow_add hR (1 : ℝ) (-(1 / 2) : ℝ)).symm
      _ = R ^ ((1 / 2 : ℝ)) := by norm_num
      _ = Real.sqrt R := (Real.sqrt_eq_rpow R).symm
  calc R * (R / m ^ q) ^ ((-(1 / 2) : ℝ))
      = R * (R ^ ((-(1 / 2) : ℝ)) * m ^ ((q : ℝ) / 2)) := by rw [hdiv]
    _ = (R * R ^ ((-(1 / 2) : ℝ))) * m ^ ((q : ℝ) / 2) := by ring
    _ = Real.sqrt R * m ^ ((q : ℝ) / 2) := by rw [hRmul]

/-- The explicit constant of the weighted grid-repair bound.  It depends only on
the dimension `q`, not on the block count `m` or the hierarchy depth `J`. -/
noncomputable def gridRepairConstant (q : ℕ) : ℝ :=
  let S : ℝ := (2 : ℝ) ^ ((q : ℝ) / 2)
  let r : ℝ := S / 4
  let c : ℝ := (q : ℝ) / 2 - 2
  32 * (q : ℝ) * Real.sqrt 2 * S * r / (r - 1) * (2 : ℝ) ^ c +
    Real.sqrt 2 * S ^ 3 / (S - 1)

set_option maxHeartbeats 4000000 in
/-- Weighted grid-repair discrepancy estimate.  If `L ^ q = R / m ^ q`, then the
weighted sum of block square-root costs is bounded by a constant depending only
on `q`, times `(C + |t| * G) * R * (L ^ (2 / q - 1 / 2) + L ^ (-1 / 2))`. -/
theorem grid_repair_sum_le
    (q J : ℕ) (hq : 4 < q) (m : ℕ) (hm : 0 < m) (hJ2 : 2 ^ J ≤ 2 * m)
    {R C G t : ℝ} (hR : 0 ≤ R) (hC0 : 0 ≤ C) (hG0 : 0 ≤ G) :
    0 ≤ gridRepairConstant q ∧
      (1 / 2) * (∑ k ∈ Finset.Icc 1 J,
        (16 * (R ^ (2 / (q : ℝ)) * (C * (q : ℝ))) * (1 / 4 : ℝ) ^ (k - 1) +
            2 * |t| * G) *
          Real.sqrt (2 * R * (((2 ^ k + 1) ^ q : ℕ) : ℝ)))
        ≤ gridRepairConstant q * (C + |t| * G) * R *
          (Real.rpow (R / (m : ℝ) ^ q) (2 / (q : ℝ) - 1 / 2) +
            Real.rpow (R / (m : ℝ) ^ q) (-(1 / 2))) := by
  have hq0 : 0 < q := by omega
  let S : ℝ := (2 : ℝ) ^ ((q : ℝ) / 2)
  let r : ℝ := S / 4
  let c : ℝ := (q : ℝ) / 2 - 2
  let K1 : ℝ := 32 * (q : ℝ) * Real.sqrt 2 * S * r / (r - 1) * (2 : ℝ) ^ c
  let K2 : ℝ := Real.sqrt 2 * S ^ 3 / (S - 1)
  have hqR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq0
  have hq4R : (4 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have h2lt : (2 : ℝ) < (q : ℝ) / 2 := by linarith
  have hc_pos : 0 < c := by dsimp only [c]; linarith
  have hc_nonneg : 0 ≤ c := le_of_lt hc_pos
  have hS_pos : 0 < S := by
    dsimp only [S]
    exact Real.rpow_pos_of_pos (by norm_num) _
  have hS_gt4 : (4 : ℝ) < S := by
    dsimp only [S]
    have h2sq : (2 : ℝ) ^ ((2 : ℝ)) = 4 := by
      rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
      norm_num
    have h := Real.rpow_lt_rpow_of_exponent_lt (show (1 : ℝ) < 2 by norm_num) h2lt
    rwa [h2sq] at h
  have hS_gt1 : (1 : ℝ) < S := by linarith
  have hS1_ne : S - 1 ≠ 0 := ne_of_gt (by linarith)
  have hr_gt1 : (1 : ℝ) < r := by dsimp only [r]; linarith
  have hr_pos : (0 : ℝ) < r := lt_trans zero_lt_one hr_gt1
  have hr1_ne : r - 1 ≠ 0 := ne_of_gt (by linarith)
  have hS_eq : S = 4 * (2 : ℝ) ^ c := by
    dsimp only [S, c]
    calc (2 : ℝ) ^ ((q : ℝ) / 2)
        = (2 : ℝ) ^ (((q : ℝ) / 2 - 2) + 2) := by congr 1; ring
      _ = (2 : ℝ) ^ ((q : ℝ) / 2 - 2) * (2 : ℝ) ^ ((2 : ℝ)) :=
            Real.rpow_add (by norm_num : (0 : ℝ) < 2) _ _
      _ = (2 : ℝ) ^ ((q : ℝ) / 2 - 2) * 4 := by
            have h2sq : (2 : ℝ) ^ ((2 : ℝ)) = 4 := by
              rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
              norm_num
            rw [h2sq]
      _ = 4 * (2 : ℝ) ^ ((q : ℝ) / 2 - 2) := by ring
  have hr_eq : r = (2 : ℝ) ^ c := by
    dsimp only [r]
    rw [hS_eq]
    ring
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have h2J : (2 : ℝ) ^ J ≤ 2 * (m : ℝ) := by
    have h' : ((2 ^ J : ℕ) : ℝ) ≤ ((2 * m : ℕ) : ℝ) := by exact_mod_cast hJ2
    simpa [Nat.cast_pow, Nat.cast_mul] using h'
  have hrJ : r ^ J ≤ (2 : ℝ) ^ c * (m : ℝ) ^ c := by
    have hpow : r ^ J = ((2 : ℝ) ^ J) ^ c := by
      rw [hr_eq]
      exact Real.rpow_pow_comm (by norm_num : (0 : ℝ) ≤ 2) c J
    rw [hpow]
    calc ((2 : ℝ) ^ J) ^ c ≤ (2 * (m : ℝ)) ^ c :=
          Real.rpow_le_rpow (by positivity) h2J hc_nonneg
      _ = (2 : ℝ) ^ c * (m : ℝ) ^ c :=
          Real.mul_rpow (by norm_num) (le_of_lt hmR)
  have hSJ : S ^ J ≤ S * (m : ℝ) ^ ((q : ℝ) / 2) := by
    have hpow : S ^ J = ((2 : ℝ) ^ J) ^ ((q : ℝ) / 2) := by
      dsimp only [S]
      exact Real.rpow_pow_comm (by norm_num : (0 : ℝ) ≤ 2) ((q : ℝ) / 2) J
    rw [hpow]
    calc ((2 : ℝ) ^ J) ^ ((q : ℝ) / 2)
        ≤ (2 * (m : ℝ)) ^ ((q : ℝ) / 2) :=
          Real.rpow_le_rpow (by positivity) h2J (by linarith)
      _ = (2 : ℝ) ^ ((q : ℝ) / 2) * (m : ℝ) ^ ((q : ℝ) / 2) :=
          Real.mul_rpow (by norm_num) (le_of_lt hmR)
      _ = S * (m : ℝ) ^ ((q : ℝ) / 2) := by dsimp only [S]
  have hKsum :
      ∑ k ∈ Finset.Icc 1 J, (1 / 4 : ℝ) ^ (k - 1) * S ^ (k + 1) ≤
        4 * S * (r / (r - 1)) * ((2 : ℝ) ^ c * (m : ℝ) ^ c) := by
    have hterm : ∀ k ∈ Finset.Icc 1 J,
        (1 / 4 : ℝ) ^ (k - 1) * S ^ (k + 1) = (4 * S) * r ^ k := by
      intro k hk
      have hk1 : 1 ≤ k := (Finset.mem_Icc.mp hk).1
      have hquarter : (1 / 4 : ℝ) ^ (k - 1) = 4 * (1 / 4 : ℝ) ^ k := by
        have hk' : (k - 1) + 1 = k := Nat.sub_add_cancel hk1
        calc (1 / 4 : ℝ) ^ (k - 1)
            = (1 / 4 : ℝ) ^ (k - 1) * 1 := by ring
          _ = (1 / 4 : ℝ) ^ (k - 1) * ((1 / 4 : ℝ) * 4) := by norm_num
          _ = ((1 / 4 : ℝ) ^ (k - 1) * (1 / 4 : ℝ)) * 4 := by ring
          _ = (1 / 4 : ℝ) ^ k * 4 := by rw [← pow_succ, hk']
          _ = 4 * (1 / 4 : ℝ) ^ k := by ring
      calc (1 / 4 : ℝ) ^ (k - 1) * S ^ (k + 1)
          = (4 * (1 / 4 : ℝ) ^ k) * (S ^ k * S) := by rw [hquarter, pow_succ]
        _ = (4 * S) * ((1 / 4 : ℝ) ^ k * S ^ k) := by ring
        _ = (4 * S) * (((1 / 4 : ℝ) * S) ^ k) := by rw [← mul_pow]
        _ = (4 * S) * r ^ k := by
              congr 1
              dsimp only [r]
              congr 1
              ring
    calc ∑ k ∈ Finset.Icc 1 J, (1 / 4 : ℝ) ^ (k - 1) * S ^ (k + 1)
        = ∑ k ∈ Finset.Icc 1 J, (4 * S) * r ^ k := Finset.sum_congr rfl hterm
      _ = (4 * S) * ∑ k ∈ Finset.Icc 1 J, r ^ k := by rw [Finset.mul_sum]
      _ ≤ (4 * S) * (r / (r - 1) * r ^ J) := by
            apply mul_le_mul_of_nonneg_left (geom_sum_Icc_le hr_gt1 J)
            positivity
      _ = 4 * S * (r / (r - 1)) * r ^ J := by ring
      _ ≤ 4 * S * (r / (r - 1)) * ((2 : ℝ) ^ c * (m : ℝ) ^ c) := by
            apply mul_le_mul_of_nonneg_left hrJ
            positivity
  have hSsum :
      ∑ k ∈ Finset.Icc 1 J, S ^ (k + 1) ≤
        S ^ 3 / (S - 1) * (m : ℝ) ^ ((q : ℝ) / 2) := by
    have h1 : ∑ k ∈ Finset.Icc 1 J, S ^ (k + 1) =
        S * ∑ k ∈ Finset.Icc 1 J, S ^ k := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun k _ => by rw [pow_succ]; ring)
    rw [h1]
    have hgeo := geom_sum_Icc_le hS_gt1 J
    calc S * (∑ k ∈ Finset.Icc 1 J, S ^ k)
        ≤ S * (S / (S - 1) * S ^ J) :=
            mul_le_mul_of_nonneg_left hgeo (le_of_lt hS_pos)
      _ = S ^ 2 / (S - 1) * S ^ J := by field_simp
      _ ≤ S ^ 2 / (S - 1) * (S * (m : ℝ) ^ ((q : ℝ) / 2)) := by
            apply mul_le_mul_of_nonneg_left hSJ
            positivity
      _ = S ^ 3 / (S - 1) * (m : ℝ) ^ ((q : ℝ) / 2) := by field_simp
  have hsqrt_le : ∀ k : ℕ,
      Real.sqrt (2 * R * (((2 ^ k + 1) ^ q : ℕ) : ℝ)) ≤
        Real.sqrt (2 * R) * S ^ (k + 1) := by
    intro k
    simpa [S] using sqrt_block_le q k R hR
  have hpoint : ∀ k ∈ Finset.Icc 1 J,
      (16 * (R ^ (2 / (q : ℝ)) * (C * (q : ℝ))) * (1 / 4 : ℝ) ^ (k - 1) +
          2 * |t| * G) *
        Real.sqrt (2 * R * (((2 ^ k + 1) ^ q : ℕ) : ℝ))
      ≤ (C + |t| * G) *
          ((16 * (q : ℝ) * R ^ (2 / (q : ℝ)) * (1 / 4 : ℝ) ^ (k - 1) + 2) *
            (Real.sqrt (2 * R) * S ^ (k + 1))) := by
    intro k hk
    have hRp : 0 ≤ R ^ (2 / (q : ℝ)) := Real.rpow_nonneg hR _
    have hX : 0 ≤ 16 * (q : ℝ) * R ^ (2 / (q : ℝ)) * (1 / 4 : ℝ) ^ (k - 1) := by
      positivity
    have hcoeff :
        16 * (R ^ (2 / (q : ℝ)) * (C * (q : ℝ))) * (1 / 4 : ℝ) ^ (k - 1) +
            2 * |t| * G
        ≤ (C + |t| * G) *
            (16 * (q : ℝ) * R ^ (2 / (q : ℝ)) * (1 / 4 : ℝ) ^ (k - 1) + 2) := by
      have hCX :
          C * (16 * (q : ℝ) * R ^ (2 / (q : ℝ)) * (1 / 4 : ℝ) ^ (k - 1)) ≤
            (C + |t| * G) *
              (16 * (q : ℝ) * R ^ (2 / (q : ℝ)) * (1 / 4 : ℝ) ^ (k - 1)) := by
        apply mul_le_mul_of_nonneg_right _ hX
        linarith [mul_nonneg (abs_nonneg t) hG0]
      have hY2 : 2 * (|t| * G) ≤ (C + |t| * G) * 2 := by
        have : |t| * G ≤ C + |t| * G := by
          linarith [mul_nonneg (abs_nonneg t) hG0]
        linarith
      calc 16 * (R ^ (2 / (q : ℝ)) * (C * (q : ℝ))) * (1 / 4 : ℝ) ^ (k - 1) +
            2 * |t| * G
          = C * (16 * (q : ℝ) * R ^ (2 / (q : ℝ)) * (1 / 4 : ℝ) ^ (k - 1)) +
              2 * (|t| * G) := by ring
        _ ≤ (C + |t| * G) *
              (16 * (q : ℝ) * R ^ (2 / (q : ℝ)) * (1 / 4 : ℝ) ^ (k - 1)) +
              (C + |t| * G) * 2 := by linarith
        _ = (C + |t| * G) *
              (16 * (q : ℝ) * R ^ (2 / (q : ℝ)) * (1 / 4 : ℝ) ^ (k - 1) + 2) := by
              ring
    have hcoeff_nonneg :
        0 ≤ 16 * (R ^ (2 / (q : ℝ)) * (C * (q : ℝ))) * (1 / 4 : ℝ) ^ (k - 1) +
            2 * |t| * G := by
      positivity
    have hsqrt_nonneg : 0 ≤ Real.sqrt (2 * R) * S ^ (k + 1) := by positivity
    calc (16 * (R ^ (2 / (q : ℝ)) * (C * (q : ℝ))) * (1 / 4 : ℝ) ^ (k - 1) +
            2 * |t| * G) *
          Real.sqrt (2 * R * (((2 ^ k + 1) ^ q : ℕ) : ℝ))
        ≤ (16 * (R ^ (2 / (q : ℝ)) * (C * (q : ℝ))) * (1 / 4 : ℝ) ^ (k - 1) +
            2 * |t| * G) * (Real.sqrt (2 * R) * S ^ (k + 1)) :=
            mul_le_mul_of_nonneg_left (hsqrt_le k) hcoeff_nonneg
      _ ≤ ((C + |t| * G) *
            (16 * (q : ℝ) * R ^ (2 / (q : ℝ)) * (1 / 4 : ℝ) ^ (k - 1) + 2)) *
            (Real.sqrt (2 * R) * S ^ (k + 1)) :=
            mul_le_mul_of_nonneg_right hcoeff hsqrt_nonneg
      _ = (C + |t| * G) *
            ((16 * (q : ℝ) * R ^ (2 / (q : ℝ)) * (1 / 4 : ℝ) ^ (k - 1) + 2) *
              (Real.sqrt (2 * R) * S ^ (k + 1))) := by ring
  have hsum1 :
      ∑ k ∈ Finset.Icc 1 J,
        (16 * (R ^ (2 / (q : ℝ)) * (C * (q : ℝ))) * (1 / 4 : ℝ) ^ (k - 1) +
            2 * |t| * G) *
          Real.sqrt (2 * R * (((2 ^ k + 1) ^ q : ℕ) : ℝ))
      ≤ (C + |t| * G) *
          (∑ k ∈ Finset.Icc 1 J,
            (16 * (q : ℝ) * R ^ (2 / (q : ℝ)) * (1 / 4 : ℝ) ^ (k - 1) + 2) *
              (Real.sqrt (2 * R) * S ^ (k + 1))) := by
    calc ∑ k ∈ Finset.Icc 1 J,
          (16 * (R ^ (2 / (q : ℝ)) * (C * (q : ℝ))) * (1 / 4 : ℝ) ^ (k - 1) +
              2 * |t| * G) *
            Real.sqrt (2 * R * (((2 ^ k + 1) ^ q : ℕ) : ℝ))
        ≤ ∑ k ∈ Finset.Icc 1 J,
            (C + |t| * G) *
              ((16 * (q : ℝ) * R ^ (2 / (q : ℝ)) * (1 / 4 : ℝ) ^ (k - 1) + 2) *
                (Real.sqrt (2 * R) * S ^ (k + 1))) := Finset.sum_le_sum hpoint
      _ = (C + |t| * G) *
          (∑ k ∈ Finset.Icc 1 J,
            (16 * (q : ℝ) * R ^ (2 / (q : ℝ)) * (1 / 4 : ℝ) ^ (k - 1) + 2) *
              (Real.sqrt (2 * R) * S ^ (k + 1))) := by rw [Finset.mul_sum]
  have hinner_eq :
      (∑ k ∈ Finset.Icc 1 J,
        (16 * (q : ℝ) * R ^ (2 / (q : ℝ)) * (1 / 4 : ℝ) ^ (k - 1) + 2) *
          (Real.sqrt (2 * R) * S ^ (k + 1)))
      = 16 * (q : ℝ) * R ^ (2 / (q : ℝ)) * Real.sqrt (2 * R) *
          (∑ k ∈ Finset.Icc 1 J, (1 / 4 : ℝ) ^ (k - 1) * S ^ (k + 1)) +
        2 * Real.sqrt (2 * R) * (∑ k ∈ Finset.Icc 1 J, S ^ (k + 1)) := by
    rw [Finset.mul_sum, Finset.mul_sum]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k _
    ring
  have hinner_le :
      (∑ k ∈ Finset.Icc 1 J,
        (16 * (q : ℝ) * R ^ (2 / (q : ℝ)) * (1 / 4 : ℝ) ^ (k - 1) + 2) *
          (Real.sqrt (2 * R) * S ^ (k + 1)))
      ≤ 16 * (q : ℝ) * R ^ (2 / (q : ℝ)) * Real.sqrt (2 * R) *
          (4 * S * (r / (r - 1)) * ((2 : ℝ) ^ c * (m : ℝ) ^ c)) +
        2 * Real.sqrt (2 * R) *
          (S ^ 3 / (S - 1) * (m : ℝ) ^ ((q : ℝ) / 2)) := by
    rw [hinner_eq]
    apply add_le_add
    · exact mul_le_mul_of_nonneg_left hKsum (by positivity)
    · exact mul_le_mul_of_nonneg_left hSsum (by positivity)
  have hsqrt2R : Real.sqrt (2 * R) = Real.sqrt 2 * Real.sqrt R :=
    Real.sqrt_mul (by norm_num) R
  have hfactor :
      (1 / 2) * (16 * (q : ℝ) * R ^ (2 / (q : ℝ)) * Real.sqrt (2 * R) *
            (4 * S * (r / (r - 1)) * ((2 : ℝ) ^ c * (m : ℝ) ^ c)) +
          2 * Real.sqrt (2 * R) *
            (S ^ 3 / (S - 1) * (m : ℝ) ^ ((q : ℝ) / 2)))
      = K1 * (R ^ (2 / (q : ℝ)) * Real.sqrt R * (m : ℝ) ^ c) +
        K2 * (Real.sqrt R * (m : ℝ) ^ ((q : ℝ) / 2)) := by
    rw [hsqrt2R]
    dsimp only [K1, K2]
    field_simp [hr1_ne, hS1_ne]
    ring
  have hK1_nonneg : 0 ≤ K1 := by
    dsimp only [K1]
    positivity
  have hK2_nonneg : 0 ≤ K2 := by
    dsimp only [K2]
    positivity
  have hKdef : gridRepairConstant q = K1 + K2 := by
    simp only [gridRepairConstant, K1, K2, S, r, c]
  constructor
  · rw [hKdef]
    linarith
  · rw [hKdef, Real.rpow_eq_pow]
    rcases hR.eq_or_lt with hR0 | hRpos
    · subst hR0
      have hqne : (q : ℝ) ≠ 0 := ne_of_gt hqR
      have h0pow : (0 : ℝ) ^ (2 / (q : ℝ)) = 0 := Real.zero_rpow (by
        exact div_ne_zero (by norm_num) hqne)
      simp [h0pow]
    · set A1 : ℝ := (R / (m : ℝ) ^ q) ^ (2 / (q : ℝ) - 1 / 2) with hA1
      set B1 : ℝ := (R / (m : ℝ) ^ q) ^ ((-(1 / 2) : ℝ)) with hB1
      have hRA : R * A1 = R ^ (2 / (q : ℝ)) * Real.sqrt R * (m : ℝ) ^ c := by
        rw [hA1]
        simpa [c] using kinetic_rpow_identity hRpos hmR hq0
      have hRB : R * B1 = Real.sqrt R * (m : ℝ) ^ ((q : ℝ) / 2) := by
        rw [hB1]
        exact probe_rpow_identity hRpos hmR
      have hCG : 0 ≤ C + |t| * G := by positivity
      have hA1_nonneg : 0 ≤ A1 := by
        rw [hA1]
        exact Real.rpow_nonneg (div_nonneg hR (pow_nonneg (le_of_lt hmR) q)) _
      have hB1_nonneg : 0 ≤ B1 := by
        rw [hB1]
        exact Real.rpow_nonneg (div_nonneg hR (pow_nonneg (le_of_lt hmR) q)) _
      have hcmp : K1 * (R * A1) + K2 * (R * B1) ≤ (K1 + K2) * R * (A1 + B1) := by
        have h1 : 0 ≤ K1 * (R * B1) :=
          mul_nonneg hK1_nonneg (mul_nonneg hR hB1_nonneg)
        have h2 : 0 ≤ K2 * (R * A1) :=
          mul_nonneg hK2_nonneg (mul_nonneg hR hA1_nonneg)
        nlinarith
      calc (1 / 2) * (∑ k ∈ Finset.Icc 1 J,
            (16 * (R ^ (2 / (q : ℝ)) * (C * (q : ℝ))) * (1 / 4 : ℝ) ^ (k - 1) +
                2 * |t| * G) *
              Real.sqrt (2 * R * (((2 ^ k + 1) ^ q : ℕ) : ℝ)))
          ≤ (1 / 2) * ((C + |t| * G) *
              (∑ k ∈ Finset.Icc 1 J,
                (16 * (q : ℝ) * R ^ (2 / (q : ℝ)) * (1 / 4 : ℝ) ^ (k - 1) + 2) *
                  (Real.sqrt (2 * R) * S ^ (k + 1)))) := by
              apply mul_le_mul_of_nonneg_left hsum1
              norm_num
        _ = (C + |t| * G) * ((1 / 2) *
              (∑ k ∈ Finset.Icc 1 J,
                (16 * (q : ℝ) * R ^ (2 / (q : ℝ)) * (1 / 4 : ℝ) ^ (k - 1) + 2) *
                  (Real.sqrt (2 * R) * S ^ (k + 1)))) := by ring
        _ ≤ (C + |t| * G) * ((1 / 2) *
              (16 * (q : ℝ) * R ^ (2 / (q : ℝ)) * Real.sqrt (2 * R) *
                  (4 * S * (r / (r - 1)) * ((2 : ℝ) ^ c * (m : ℝ) ^ c)) +
                2 * Real.sqrt (2 * R) *
                  (S ^ 3 / (S - 1) * (m : ℝ) ^ ((q : ℝ) / 2)))) := by
              apply mul_le_mul_of_nonneg_left
              · apply mul_le_mul_of_nonneg_left hinner_le
                norm_num
              · exact hCG
        _ = (C + |t| * G) *
              (K1 * (R ^ (2 / (q : ℝ)) * Real.sqrt R * (m : ℝ) ^ c) +
                K2 * (Real.sqrt R * (m : ℝ) ^ ((q : ℝ) / 2))) := by
              rw [hfactor]
        _ = (C + |t| * G) * (K1 * (R * A1) + K2 * (R * B1)) := by
              rw [← hRA, ← hRB]
        _ ≤ (K1 + K2) * (C + |t| * G) * R * (A1 + B1) := by
              calc (C + |t| * G) * (K1 * (R * A1) + K2 * (R * B1))
                  ≤ (C + |t| * G) * ((K1 + K2) * R * (A1 + B1)) :=
                    mul_le_mul_of_nonneg_left hcmp hCG
                _ = (K1 + K2) * (C + |t| * G) * R * (A1 + B1) := by ring

end OTSelector.Probability
