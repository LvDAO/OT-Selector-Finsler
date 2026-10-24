import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Analysis.Convex.Birkhoff
import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Real.Basic
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.Tactic
import Mathlib.Tactic.Linarith
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.MetricSpace.Lipschitz
import OTSelector.Finite.HierarchicalAssignment

/-!
# Finite.DyadicCellCost

**Conditions:** Finite-dimensional real coordinates; geometric distance estimates assume both points lie in the half-open unit cube and positive depth.

**Objects:** Total floor/modulo dyadic cell labels and a geometric-series partition-distance upper bound for squared distance.

**Proof detail:** Use quotient-remainder identities to prove nesting, bound coordinate separation in equal cells, and split at the first unequal scale; sum coordinate squares and the weighted geometric contributions.

**Sources:** [Thomas W. Judson, Abstract Algebra: Theory and Applications (author online edition)](https://twjudson.github.io/aata-files/aata-html/integers-section-division-algorithm.html), Section 2.2, Theorem 2.2.1 (Division Algorithm); [Terence Tao, Analysis I](https://github.com/teorth/analysis/blob/main/Analysis/Section_7_1.lean), Sections 4.3 (absolute value) and 7.1 (finite series), in particular Proposition 7.1.11; [OTSelector project, Distribution-free squared matching above dimension four](main.tex#lem:general-upper-dyadic), main.tex label lem:general-upper-dyadic, line 1634.

Source relation (composition): The cited sections provide the stated mathematical foundations; the exact finite construction and quantitative bound in this module are local consequences, not a claim that the book states the Lean theorem verbatim.
-/

/-!
# Dyadic cells and the geometric cost of mismatching them

This file supplies the deterministic geometric input for the dyadic matching
bound.  A point `x : Fin q → ℝ` is assigned, at level `k`, the vector of
integer cells `⌊2 ^ k * x i⌋` reduced modulo `2 ^ k`; the reduction makes the
definition total without an a priori assumption `0 ≤ x i`.

The main estimate compares the squared Euclidean distance of two points in the
unit cube with the sum, over all dyadic levels below `K`, of the partition
distance of their cells, weighted by `8 q (1 / 4) ^ k`, plus the terminal
diameter term `4 q (1 / 4) ^ K`.  This is the geometric inequality behind
`lem:general-upper-dyadic`.

The proofs rest on three observations:

* on the unit cube the modulo in the cell label is redundant;
* equality of finer cells implies equality of coarser cells;
* if the cells first disagree at level `k₀`, then the two points lie in a
  common cell of level `k₀ - 1`, so their squared distance is at most
  `q (1 / 4) ^ (k₀ - 1)`, while every level from `k₀` onwards contributes a
  full unit of partition distance.
-/

open scoped BigOperators
open OTSelector.Reconstruction

noncomputable section
namespace OTSelector

/-- The dyadic cell of `x` at level `k`, coordinate by coordinate.

The floor `⌊2 ^ k * x i⌋₊` is reduced modulo `2 ^ k`, which keeps the
definition meaningful for arbitrary real coordinates; on the unit cube the
reduction does nothing. -/
noncomputable def dyadicCell (q k : ℕ) (x : Fin q → ℝ) : Fin q → Fin (2 ^ k) :=
  fun i => ⟨⌊(2 : ℝ) ^ k * x i⌋₊ % 2 ^ k,
    Nat.mod_lt _ (Nat.pow_pos (by norm_num : 0 < 2))⟩

/-- On the unit cube the modulo in `dyadicCell` is redundant: the level-`k`
cell label is exactly `⌊2 ^ k * x i⌋₊`. -/
theorem dyadicCell_eq_floor_of_nonneg {q k : ℕ} {x : Fin q → ℝ} (hx : ∀ i, 0 ≤ x i)
    (hx1 : ∀ i, x i < 1) (i : Fin q) :
    (dyadicCell q k x i : ℕ) = ⌊(2 : ℝ) ^ k * x i⌋₊ := by
  have hp : (0 : ℝ) < (2 : ℝ) ^ k := by positivity
  have hlt : ⌊(2 : ℝ) ^ k * x i⌋₊ < 2 ^ k := by
    by_contra h
    have hge : ((2 : ℝ) ^ k) ≤ (⌊(2 : ℝ) ^ k * x i⌋₊ : ℝ) := by
      exact_mod_cast Nat.le_of_not_lt h
    have hfloor := Nat.floor_le (mul_nonneg hp.le (hx i))
    have hxlt : (2 : ℝ) ^ k * x i < (2 : ℝ) ^ k := by
      simpa using mul_lt_mul_of_pos_left (hx1 i) hp
    nlinarith
  exact Nat.mod_eq_of_lt hlt

/-- Dividing a natural floor by a positive integer is the floor after the same
division: this is the arithmetic coarsening step for dyadic cells. -/
private theorem nat_div_mod_mul (A m d : ℕ) (hm : 0 < m) (hd : 0 < d) :
    A / d % m = A % (m * d) / d := by
  have hA : (m * d) * (A / (m * d)) + A % (m * d) = A := Nat.div_add_mod A (m * d)
  conv_lhs => rw [← hA]
  have hmul : (m * d) * (A / (m * d)) = (m * (A / (m * d))) * d := by ring
  rw [hmul]
  rw [Nat.add_comm ((m * (A / (m * d))) * d) (A % (m * d))]
  rw [Nat.add_mul_div_right (A % (m * d)) (m * (A / (m * d))) hd]
  rw [Nat.mul_comm m (A / (m * d))]
  rw [Nat.add_mul_mod_self_right]
  have hlt : A % (m * d) / d < m := by
    apply Nat.div_lt_of_lt_mul
    rw [Nat.mul_comm d m]
    exact Nat.mod_lt _ (Nat.mul_pos hm hd)
  rw [Nat.mod_eq_of_lt hlt]

/-- At a coarser level, the floor label is the finer floor label divided by the
ratio of the two cell counts. -/
private theorem floor_coarsen {k l : ℕ} (hkl : k ≤ l) (a : ℝ) :
    ⌊(2 : ℝ) ^ l * a⌋₊ / 2 ^ (l - k) = ⌊(2 : ℝ) ^ k * a⌋₊ := by
  have hpos : 0 < 2 ^ (l - k) := Nat.pow_pos (by norm_num : 0 < 2)
  have hcast : ((2 ^ (l - k) : ℕ) : ℝ) = (2 : ℝ) ^ (l - k) := by
    rw [Nat.cast_pow]
    norm_num
  have harg : (2 : ℝ) ^ l * a = ((2 : ℝ) ^ k * a) * ((2 ^ (l - k) : ℕ) : ℝ) := by
    rw [hcast]
    calc
      (2 : ℝ) ^ l * a = (2 : ℝ) ^ (k + (l - k)) * a := by
        rw [Nat.add_sub_of_le hkl]
      _ = ((2 : ℝ) ^ k * a) * (2 : ℝ) ^ (l - k) := by
        rw [pow_add]
        ring
  rw [harg]
  exact Nat.mul_cast_floor_div_cancel (Nat.ne_of_gt hpos) ((2 : ℝ) ^ k * a)

/-- Nestedness of dyadic cells for arbitrary real coordinates. -/
theorem dyadicCell_nested_global {q k l : ℕ} (hkl : k ≤ l) {x y : Fin q → ℝ}
    (h : dyadicCell q l x = dyadicCell q l y) :
    dyadicCell q k x = dyadicCell q k y := by
  funext i
  apply Fin.ext
  have hval : ⌊(2 : ℝ) ^ l * x i⌋₊ % 2 ^ l = ⌊(2 : ℝ) ^ l * y i⌋₊ % 2 ^ l := by
    have := congrArg Fin.val (congrFun h i)
    simpa only [dyadicCell] using this
  have hprod : 2 ^ l = 2 ^ k * 2 ^ (l - k) := by
    rw [← Nat.pow_add, Nat.add_sub_of_le hkl]
  rw [hprod] at hval
  have hfx : ⌊(2 : ℝ) ^ l * x i⌋₊ / 2 ^ (l - k) = ⌊(2 : ℝ) ^ k * x i⌋₊ :=
    floor_coarsen hkl (x i)
  have hfy : ⌊(2 : ℝ) ^ l * y i⌋₊ / 2 ^ (l - k) = ⌊(2 : ℝ) ^ k * y i⌋₊ :=
    floor_coarsen hkl (y i)
  have hxm := nat_div_mod_mul ⌊(2 : ℝ) ^ l * x i⌋₊ (2 ^ k) (2 ^ (l - k))
    (Nat.pow_pos (by norm_num : 0 < 2)) (Nat.pow_pos (by norm_num : 0 < 2))
  have hym := nat_div_mod_mul ⌊(2 : ℝ) ^ l * y i⌋₊ (2 ^ k) (2 ^ (l - k))
    (Nat.pow_pos (by norm_num : 0 < 2)) (Nat.pow_pos (by norm_num : 0 < 2))
  rw [hfx] at hxm
  rw [hfy] at hym
  simp only [dyadicCell]
  rw [hxm, hym, hval]

/-- Equality of cells at a finer dyadic level implies equality of the cells at
every coarser level. -/
theorem dyadicCell_nested {q k l : ℕ} (hkl : k ≤ l) {x y : Fin q → ℝ}
    (hx : ∀ i, 0 ≤ x i) (hy : ∀ i, 0 ≤ y i)
    (h : dyadicCell q l x = dyadicCell q l y) :
    dyadicCell q k x = dyadicCell q k y :=
  dyadicCell_nested_global hkl h

/-- Two unit-cube coordinates sharing a level-`k` cell differ by at most the
width `2 ^ (-k)` of that cell. -/
theorem abs_sub_le_of_dyadicCell_eq {q k : ℕ} {x y : Fin q → ℝ}
    (hx : ∀ i, 0 ≤ x i ∧ x i < 1) (hy : ∀ i, 0 ≤ y i ∧ y i < 1)
    (h : dyadicCell q k x = dyadicCell q k y) (i : Fin q) :
    |x i - y i| ≤ ((2 : ℝ) ^ k)⁻¹ := by
  have hp : (0 : ℝ) < (2 : ℝ) ^ k := by positivity
  have he : ⌊(2 : ℝ) ^ k * x i⌋₊ = ⌊(2 : ℝ) ^ k * y i⌋₊ := by
    have hv : (dyadicCell q k x i : ℕ) = (dyadicCell q k y i : ℕ) :=
      congrArg Fin.val (congrFun h i)
    rw [dyadicCell_eq_floor_of_nonneg (fun j => (hx j).1) (fun j => (hx j).2) i,
      dyadicCell_eq_floor_of_nonneg (fun j => (hy j).1) (fun j => (hy j).2) i] at hv
    exact hv
  have hxlo := Nat.floor_le (mul_nonneg hp.le (hx i).1)
  have hxhi := Nat.lt_floor_add_one ((2 : ℝ) ^ k * x i)
  have hylo := Nat.floor_le (mul_nonneg hp.le (hy i).1)
  have hyhi := Nat.lt_floor_add_one ((2 : ℝ) ^ k * y i)
  rw [he] at hxlo hxhi
  apply (mul_le_mul_iff_of_pos_left hp).mp
  rw [mul_inv_cancel₀ hp.ne']
  rw [← abs_of_pos hp, ← abs_mul]
  apply abs_le.mpr
  constructor <;> nlinarith

/-- Two unit-cube coordinates sharing a level-`k` cell have squared difference
at most `4 ^ (-k)`. -/
theorem sq_sub_le_of_dyadicCell_eq {q k : ℕ} {x y : Fin q → ℝ}
    (hx : ∀ i, 0 ≤ x i ∧ x i < 1) (hy : ∀ i, 0 ≤ y i ∧ y i < 1)
    (h : dyadicCell q k x = dyadicCell q k y) (i : Fin q) :
    (x i - y i) ^ 2 ≤ (1 / 4 : ℝ) ^ k := by
  have habs := abs_sub_le_of_dyadicCell_eq hx hy h i
  have hpow : (((2 : ℝ) ^ k)⁻¹) ^ 2 = (1 / 4 : ℝ) ^ k := by
    rw [inv_pow, ← pow_mul, Nat.mul_comm k 2, pow_mul, ← inv_pow]
    norm_num
  rw [← hpow, ← sq_abs]
  exact pow_le_pow_left₀ (abs_nonneg _) habs 2

/-- If two unit-cube points have equal level-`k` cells, the total squared
coordinate difference is at most `q * 4 ^ (-k)`. -/
theorem sum_sq_le_of_dyadicCell_eq {q k : ℕ} {x y : Fin q → ℝ}
    (hx : ∀ i, 0 ≤ x i ∧ x i < 1) (hy : ∀ i, 0 ≤ y i ∧ y i < 1)
    (h : dyadicCell q k x = dyadicCell q k y) :
    ∑ i, (x i - y i) ^ 2 ≤ (q : ℝ) * (1 / 4 : ℝ) ^ k := by
  calc
    ∑ i, (x i - y i) ^ 2 ≤ ∑ _i : Fin q, (1 / 4 : ℝ) ^ k :=
      Finset.sum_le_sum fun i _ => sq_sub_le_of_dyadicCell_eq hx hy h i
    _ = (q : ℝ) * (1 / 4 : ℝ) ^ k := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- On the unit cube the sum of squared coordinate differences is at most the
number of coordinates. -/
theorem sum_sq_le_card {q : ℕ} {x y : Fin q → ℝ}
    (hx : ∀ i, 0 ≤ x i ∧ x i < 1) (hy : ∀ i, 0 ≤ y i ∧ y i < 1) :
    ∑ i, (x i - y i) ^ 2 ≤ (q : ℝ) := by
  have hterm : ∀ i, (x i - y i) ^ 2 ≤ (1 : ℝ) := by
    intro i
    have habs : |x i - y i| ≤ 1 := by
      apply abs_le.mpr
      constructor <;> linarith [(hx i).1, (hx i).2, (hy i).1, (hy i).2]
    have h := pow_le_pow_left₀ (abs_nonneg (x i - y i)) habs 2
    simpa [sq_abs] using h
  calc
    ∑ i, (x i - y i) ^ 2 ≤ ∑ _i : Fin q, (1 : ℝ) :=
      Finset.sum_le_sum fun i _ => hterm i
    _ = (q : ℝ) := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]

/-- The deterministic geometric input of the dyadic matching bound: on the unit
cube, the squared Euclidean distance is bounded by the terminal dyadic cell
diameter plus the geometric sum of dyadic cell mismatches.

The terminal term is `4 q (1 / 4) ^ K`.  At the first mismatching level `k₀`,
the points still share a cell of the preceding level, which bounds the squared
distance by `4 q (1 / 4) ^ k₀`; the mismatch at level `k₀` alone contributes
`8 q (1 / 4) ^ k₀` to the weighted sum. -/
theorem sq_dist_le_dyadic_partitionDistance {q K : ℕ} (hK : 0 < K)
    {x y : Fin q → ℝ} (hx : ∀ i, 0 ≤ x i ∧ x i < 1) (hy : ∀ i, 0 ≤ y i ∧ y i < 1) :
    ∑ i, (x i - y i)^2 ≤
      (4 * q : ℝ) * ((1/4 : ℝ) ^ K) +
        ∑ k ∈ Finset.range K, (8 * q : ℝ) * ((1/4 : ℝ) ^ k) *
          partitionDistance (dyadicCell q k x) (dyadicCell q k y) := by
  classical
  by_cases hall : ∀ k, k < K → dyadicCell q k x = dyadicCell q k y
  · -- All levels below `K` agree, so the terminal cell bounds the distance.
    have hKpred : K - 1 < K := Nat.sub_one_lt (Nat.ne_of_gt hK)
    have hcell : dyadicCell q (K - 1) x = dyadicCell q (K - 1) y := hall (K - 1) hKpred
    have hsum := sum_sq_le_of_dyadicCell_eq hx hy hcell
    have hbase : (q : ℝ) * (1 / 4 : ℝ) ^ (K - 1) = (4 * q : ℝ) * (1 / 4 : ℝ) ^ K := by
      have hKsplit : K = (K - 1) + 1 := by omega
      conv_rhs => rw [hKsplit]
      rw [pow_succ]
      ring
    have hsum_nonneg :
        0 ≤ ∑ k ∈ Finset.range K, (8 * q : ℝ) * ((1/4 : ℝ) ^ k) *
          partitionDistance (dyadicCell q k x) (dyadicCell q k y) :=
      Finset.sum_nonneg fun k _ =>
        mul_nonneg (mul_nonneg (by positivity) (by positivity))
          (partitionDistance_bounds _ _).1
    calc
      ∑ i, (x i - y i) ^ 2 ≤ (q : ℝ) * (1 / 4 : ℝ) ^ (K - 1) := hsum
      _ = (4 * q : ℝ) * (1 / 4 : ℝ) ^ K := hbase
      _ ≤ (4 * q : ℝ) * (1 / 4 : ℝ) ^ K +
          ∑ k ∈ Finset.range K, (8 * q : ℝ) * ((1/4 : ℝ) ^ k) *
            partitionDistance (dyadicCell q k x) (dyadicCell q k y) :=
        le_add_of_nonneg_right hsum_nonneg
  · -- Let `k₀` be the first level with mismatching cells.
    push Not at hall
    let k0 := Nat.find hall
    have hk0spec : k0 < K ∧ dyadicCell q k0 x ≠ dyadicCell q k0 y := Nat.find_spec hall
    have hk0lt : k0 < K := hk0spec.1
    have hk0mis : dyadicCell q k0 x ≠ dyadicCell q k0 y := hk0spec.2
    have hk0min : ∀ k, k < k0 → dyadicCell q k x = dyadicCell q k y := by
      intro k hk
      by_contra hne
      exact Nat.find_min hall hk ⟨lt_trans hk hk0lt, hne⟩
    -- The level-`k₀` term is a full unit of partition distance.
    have hdist_k0 : partitionDistance (dyadicCell q k0 x) (dyadicCell q k0 y) = 1 := by
      rw [partitionDistance]
      simp [hk0mis]
    have hterm_nonneg : ∀ k ∈ Finset.range K,
        0 ≤ (8 * q : ℝ) * ((1/4 : ℝ) ^ k) *
          partitionDistance (dyadicCell q k x) (dyadicCell q k y) := by
      intro k _
      exact mul_nonneg (mul_nonneg (by positivity) (by positivity))
        (partitionDistance_bounds _ _).1
    have hsingle := Finset.single_le_sum hterm_nonneg (Finset.mem_range.mpr hk0lt)
    have hlow : (8 * q : ℝ) * (1 / 4 : ℝ) ^ k0 ≤
        ∑ k ∈ Finset.range K, (8 * q : ℝ) * ((1/4 : ℝ) ^ k) *
          partitionDistance (dyadicCell q k x) (dyadicCell q k y) := by
      simpa [hdist_k0] using hsingle
    -- Bound the squared distance using the last agreeing level before `k₀`.
    have hupper : ∑ i, (x i - y i) ^ 2 ≤ (8 * q : ℝ) * (1 / 4 : ℝ) ^ k0 := by
      by_cases hk0zero : k0 = 0
      · have hle := sum_sq_le_card hx hy
        have hzero : (1 / 4 : ℝ) ^ k0 = 1 := by
          rw [hk0zero]
          norm_num
        have hcq : (q : ℝ) ≤ (8 * q : ℝ) * (1 / 4 : ℝ) ^ k0 := by
          rw [hzero, mul_one]
          nlinarith [show (0 : ℝ) ≤ q by positivity]
        exact hle.trans hcq
      · have hpred : k0 - 1 < k0 := Nat.sub_one_lt hk0zero
        have hcell : dyadicCell q (k0 - 1) x = dyadicCell q (k0 - 1) y := hk0min _ hpred
        have hle := sum_sq_le_of_dyadicCell_eq hx hy hcell
        have hpow : (1 / 4 : ℝ) ^ k0 = (1 / 4 : ℝ) ^ (k0 - 1) * (1 / 4) := by
          conv_lhs => rw [← Nat.sub_one_add_one hk0zero]
          rw [pow_succ]
        have hconvert : (q : ℝ) * (1 / 4 : ℝ) ^ (k0 - 1) ≤
            (8 * q : ℝ) * (1 / 4 : ℝ) ^ k0 := by
          calc
            (q : ℝ) * (1 / 4 : ℝ) ^ (k0 - 1) ≤
                (2 * q : ℝ) * (1 / 4 : ℝ) ^ (k0 - 1) := by
              have hq : (0 : ℝ) ≤ q := by positivity
              have hc : (0 : ℝ) ≤ (1 / 4 : ℝ) ^ (k0 - 1) := by positivity
              nlinarith
            _ = (8 * q : ℝ) * (1 / 4 : ℝ) ^ k0 := by
              rw [hpow]
              ring
        exact hle.trans hconvert
    calc
      ∑ i, (x i - y i) ^ 2 ≤ (8 * q : ℝ) * (1 / 4 : ℝ) ^ k0 := hupper
      _ ≤ (4 * q : ℝ) * ((1/4 : ℝ) ^ K) +
          ∑ k ∈ Finset.range K, (8 * q : ℝ) * ((1/4 : ℝ) ^ k) *
            partitionDistance (dyadicCell q k x) (dyadicCell q k y) := by
        have hbase_nonneg : 0 ≤ (4 * q : ℝ) * ((1/4 : ℝ) ^ K) := by positivity
        linarith

end OTSelector
