import OTSelector.Finite.HierarchicalAssignment

/-!
# Typewise discrepancy of the same hierarchy permutation

A fixed population type is charged for its internal cell crossings and for
actual edges entering or leaving that type. These are count identities for one
full permutation, not a separately balanced sample for each type.
-/

open Function
open scoped BigOperators

noncomputable section
namespace OTSelector.Reconstruction

/-- A type is charged for a cross-type edge when exactly one endpoint belongs. -/
def typeCrossingCharge {T : Type*} (t a b : T) : ℝ :=
  |partitionIndicator a t - partitionIndicator b t|

/-- Internal crossings of a fixed type carry two histogram units. -/
def typeInternalCrossing {T C : Type*} (t : T) (a b : T × C) : ℝ := by
  classical
  exact if a.1 = t ∧ b.1 = t then partitionDistance a.2 b.2 else 0

/-- Summing only the cells of one type splits into its internal discrepancy and
its entering/leaving charge. -/
theorem sum_type_cell_indicator_abs {T C : Type*} [Fintype C]
    (t : T) (x y : T × C) :
    (∑ a, |partitionIndicator x (t, a) - partitionIndicator y (t, a)|) =
      2 * typeInternalCrossing t x y + typeCrossingCharge t x.1 y.1 := by
  classical
  rcases x with ⟨tx, x⟩
  rcases y with ⟨ty, y⟩
  by_cases hx : tx = t <;> by_cases hy : ty = t
  · subst tx
    subst ty
    have h := sum_abs_partition_indicator x y
    simpa [typeInternalCrossing, typeCrossingCharge, partitionIndicator, Prod.mk.injEq] using h
  · subst tx
    simp [typeInternalCrossing, typeCrossingCharge, partitionIndicator, Prod.mk.injEq, hy, abs_ite]
  · subst ty
    simp [typeInternalCrossing, typeCrossingCharge, partitionIndicator, Prod.mk.injEq, hx, abs_ite]
  · simp [typeInternalCrossing, typeCrossingCharge, partitionIndicator, Prod.mk.injEq, hx, hy]

/-- Exact count of entering/leaving edges at a saturated type. -/
theorem sum_typeCrossingCharge_eq {n : ℕ} {T : Type*}
    (x y : Fin n → T) (σ : Assignment n)
    (hcross : ∀ i j, x i = y (σ j) → x i ≠ y (σ i) → x j = y (σ j)) (t : T) :
    (∑ i, typeCrossingCharge t (x i) (y (σ i))) =
      |partitionCount x t - partitionCount y t| :=
  (partitionCount_abs_difference x y σ hcross t).symm

/-- The internal crossing count of a type is bounded by that type's refined
histogram discrepancy, for the same global assignment. -/
theorem typeInternalCrossing_le_histogram
    {n : ℕ} {T C : Type*} [Fintype C]
    (x y : Fin n → T × C) (σ : Assignment n)
    (hcross : ∀ i j, x i = y (σ j) → x i ≠ y (σ i) → x j = y (σ j)) (t : T) :
    2 * (∑ i, typeInternalCrossing t (x i) (y (σ i))) ≤
      ∑ a, |partitionCount x (t, a) - partitionCount y (t, a)| := by
  have he (a : C) := partitionCount_abs_difference x y σ hcross (t, a)
  simp_rw [he]
  rw [Finset.sum_comm, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  rw [sum_type_cell_indicator_abs]
  exact le_add_of_nonneg_right (abs_nonneg _)

end OTSelector.Reconstruction
