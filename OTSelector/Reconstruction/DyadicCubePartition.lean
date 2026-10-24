import OTSelector.Finite.DyadicCube
import OTSelector.Reconstruction.HierarchicalIIDAssignment
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Analysis.Normed.Group.Constructions

/-!
# Reconstruction.DyadicCubePartition

**Conditions:** The selected cube is closed, coordinatewise 0≤x≤1, in a finite dimension q; level k is a natural number.

**Objects:** Closed unit-cube points, floor cells in Fin(2^k+1) and their same-cell sup-distance bound.

**Proof detail:** Retain the endpoint one as its own boundary label; the floor inequalities place equal-cell coordinates in one interval of width 2^(−k), and the coordinate supremum norm gives the full distance bound.

**Sources:** [Thomas W. Judson, Abstract Algebra: Theory and Applications (author online edition)](https://twjudson.github.io/aata-files/aata-html/integers-section-division-algorithm.html), Section 2.2, Theorem 2.2.1 (Division Algorithm); [Terence Tao, Analysis I](https://github.com/teorth/analysis/blob/main/Analysis/Section_7_1.lean), Sections 4.3 (absolute value) and 7.1 (finite series), in particular Proposition 7.1.11.

Source relation (corollary): Only the selected generic source commands are covered. The cited book sections provide the finite assignment, finite-sum or coupling foundations; the exact construction and quantitative statement are local corollaries or Lean adapters, not a claim that the book contains the same named Lean lemma.
-/

/-!
# Actual dyadic partitions of a closed cube

The endpoint 1 is retained as a boundary cell. This avoids modifying arbitrary
population laws with boundary atoms. The number of cells is at most a fixed
factor times the usual dyadic count.
-/

open Set Function MeasureTheory ProbabilityTheory
open scoped BigOperators

noncomputable section
namespace OTSelector.Reconstruction







/-- Floor division by two is the actual coarsening of adjacent levels. -/
theorem dyadicCubeCell_coarsen {q : ℕ} (k : ℕ) (x : DyadicUnitCube q) (i : Fin q) :
    (dyadicCubeCell k x i : ℕ) = (dyadicCubeCell (k + 1) x i : ℕ) / 2 := by
  change ⌊(2 : ℝ) ^ k * (x i : ℝ)⌋₊ = ⌊(2 : ℝ) ^ (k + 1) * (x i : ℝ)⌋₊ / 2
  convert (Nat.mul_cast_floor_div_cancel (R := ℝ) (n := 2) (by decide)
    ((2 : ℝ) ^ k * (x i : ℝ))).symm using 1
  congr 2
  rw [pow_succ]
  ring

/-- Equality of finer cells implies equality at every coarser scale. -/
theorem dyadicCubeCell_nested {q : ℕ} {k l : ℕ} (hkl : k ≤ l)
    (x y : DyadicUnitCube q) (hxy : dyadicCubeCell l x = dyadicCubeCell l y) :
    dyadicCubeCell k x = dyadicCubeCell k y := by
  induction l, hkl using Nat.le_induction with
  | base => exact hxy
  | succ l hkl ih =>
    apply ih
    funext i
    apply Fin.ext
    rw [dyadicCubeCell_coarsen l x i, dyadicCubeCell_coarsen l y i]
    rw [hxy]

/-- All actual dyadic cells are measurable in the original cube. -/
theorem measurable_dyadicCubeCell {q : ℕ} (k : ℕ) :
    Measurable (dyadicCubeCell (q := q) k) := by
  apply measurable_pi_lambda
  intro i
  apply measurable_to_countable'
  intro a
  have hm : Measurable (fun x : DyadicUnitCube q ↦ ⌊(2 : ℝ) ^ k * (x i : ℝ)⌋₊) :=
    ((measurable_subtype_coe.comp (measurable_pi_apply i)).const_mul _).nat_floor
  convert hm (measurableSet_singleton (a : ℕ)) using 1
  ext x
  exact Fin.ext_iff



/-- The original closed-cube diameter in its coordinate norm is at most one. -/
theorem dyadicCube_dist_le_one {q : ℕ} (x y : DyadicUnitCube q) :
    ‖dyadicCubePoint x - dyadicCubePoint y‖ ≤ 1 := by
  apply (pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 1)).mpr
  intro i
  change |(x i : ℝ) - (y i : ℝ)| ≤ 1
  exact abs_le.mpr ⟨by linarith [(x i).property.1, (y i).property.2],
    by linarith [(x i).property.2, (y i).property.1]⟩

/-- The terminal squared diameter of an actual level-k cell. -/
theorem dyadicCube_sqdist_le_of_cell_eq {q : ℕ} (k : ℕ) (x y : DyadicUnitCube q)
    (hxy : dyadicCubeCell k x = dyadicCubeCell k y) :
    ‖dyadicCubePoint x - dyadicCubePoint y‖ ^ 2 ≤ (1 / 4 : ℝ) ^ k := by
  have h := dyadicCube_dist_le_of_cell_eq k x y hxy
  have hpow : (((2 : ℝ) ^ k)⁻¹) ^ 2 = (1 / 4 : ℝ) ^ k := by
    rw [inv_pow, ← pow_mul, Nat.mul_comm k 2, pow_mul]
    norm_num
    simpa only [one_div] using (inv_pow (4 : ℝ) k).symm
  rw [← hpow]
  exact pow_le_pow_left₀ (norm_nonneg _) h 2

/-- The actual squared distance is bounded by the terminal cell diameter and
all scale crossings. This holds pointwise even on boundary atoms. -/
theorem dyadicCube_sqdist_multiscale {q : ℕ} (K : ℕ) (x y : DyadicUnitCube q) :
    ‖dyadicCubePoint x - dyadicCubePoint y‖ ^ 2 ≤ (1 / 4 : ℝ) ^ K +
      ∑ k ∈ Finset.range K, (1 / 4 : ℝ) ^ k *
        partitionDistance (dyadicCubeCell (k + 1) x) (dyadicCubeCell (k + 1) y) := by
  classical
  induction K with
  | zero =>
    have h := dyadicCube_dist_le_one x y
    simpa using pow_le_pow_left₀ (norm_nonneg _) h 2
  | succ K ih =>
    rw [Finset.sum_range_succ]
    by_cases he : dyadicCubeCell (K + 1) x = dyadicCubeCell (K + 1) y
    · apply (dyadicCube_sqdist_le_of_cell_eq (K + 1) x y he).trans
      apply le_add_of_nonneg_right
      apply add_nonneg
      · exact Finset.sum_nonneg (fun k _ ↦
          mul_nonneg (by positivity) (partitionDistance_bounds _ _).1)
      · exact mul_nonneg (by positivity) (partitionDistance_bounds _ _).1
    · have hd : partitionDistance (dyadicCubeCell (K + 1) x) (dyadicCubeCell (K + 1) y) = 1 := by
        simp only [partitionDistance, ite_eq_right he]
      rw [hd, mul_one]
      have hbase : (0 : ℝ) ≤ (1 / 4 : ℝ) ^ (K + 1) := by positivity
      linarith

/-- The number of actual floor cells remains within a fixed dimensional factor
of the usual dyadic count. -/
theorem dyadicCube_cell_card_le (q k : ℕ) :
    Fintype.card (Fin q → Fin (2 ^ k + 1)) ≤ 2 ^ ((k + 1) * q) := by
  simp only [Fintype.card_fun, Fintype.card_fin]
  rw [pow_mul]
  apply Nat.pow_le_pow_left
  rw [pow_succ]
  have hp : 1 ≤ 2 ^ k := Nat.one_le_pow k 2 (by decide)
  omega

end OTSelector.Reconstruction
