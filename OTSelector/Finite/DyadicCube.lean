import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Analysis.Convex.Birkhoff
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.GroupTheory.Perm.ViaEmbedding
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Measure.FiniteMeasureExt
import Mathlib.Probability.Distributions.Beta
import Mathlib.Probability.Kernel.CondDistrib
import Mathlib.Probability.Moments.Variance
import Mathlib.Topology.Algebra.Module.Cardinality
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Reconstruction.DyadicCubePartition.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Reconstruction.DyadicCubePartition`; the selected original proof blocks follow. -/
section

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

/-- The closed unit cube, including every boundary face and possible atom. -/
abbrev DyadicUnitCube (q : ℕ) := Fin q → Set.Icc (0 : ℝ) 1

/-- Original coordinates of a point in the closed cube. -/
def dyadicCubePoint {q : ℕ} (x : DyadicUnitCube q) : Fin q → ℝ := fun i ↦ x i

/-- Actual floor cells, with a separate final boundary cell at coordinate 1. -/
def dyadicCubeCell {q : ℕ} (k : ℕ) (x : DyadicUnitCube q) : Fin q → Fin (2 ^ k + 1) :=
  fun i ↦ ⟨⌊(2 : ℝ) ^ k * (x i : ℝ)⌋₊, by
    apply Nat.lt_succ_of_le
    apply Nat.floor_le_of_le
    norm_cast
    have h := (x i).property.2
    have hp : (0 : ℝ) ≤ 2 ^ k := by positivity
    simpa using mul_le_mul_of_nonneg_left h hp⟩







/-- Coordinate equality at scale k bounds the original sup distance. -/
theorem dyadicCube_dist_le_of_cell_eq {q : ℕ} (k : ℕ) (x y : DyadicUnitCube q)
    (hxy : dyadicCubeCell k x = dyadicCubeCell k y) :
    ‖dyadicCubePoint x - dyadicCubePoint y‖ ≤ ((2 : ℝ) ^ k)⁻¹ := by
  have hp : (0 : ℝ) < 2 ^ k := by positivity
  apply (pi_norm_le_iff_of_nonneg (inv_nonneg.mpr hp.le)).mpr
  intro i
  have he : ⌊(2 : ℝ) ^ k * (x i : ℝ)⌋₊ = ⌊(2 : ℝ) ^ k * (y i : ℝ)⌋₊ :=
    congrArg Fin.val (congrFun hxy i)
  have hx0 : 0 ≤ (2 : ℝ) ^ k * (x i : ℝ) := mul_nonneg hp.le (x i).property.1
  have hy0 : 0 ≤ (2 : ℝ) ^ k * (y i : ℝ) := mul_nonneg hp.le (y i).property.1
  have hxlo := Nat.floor_le hx0
  have hxhi := Nat.lt_floor_add_one ((2 : ℝ) ^ k * (x i : ℝ))
  have hylo := Nat.floor_le hy0
  have hyhi := Nat.lt_floor_add_one ((2 : ℝ) ^ k * (y i : ℝ))
  rw [he] at hxlo hxhi
  change |(x i : ℝ) - (y i : ℝ)| ≤ ((2 : ℝ) ^ k)⁻¹
  apply (mul_le_mul_iff_of_pos_left hp).mp
  rw [mul_inv_cancel₀ hp.ne']
  rw [← abs_of_pos hp, ← abs_mul]
  apply abs_le.mpr
  constructor <;> nlinarith









end OTSelector.Reconstruction

end
end
