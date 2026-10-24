import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-!
## Lemma skeleton

* **Conditions:** A finite real matrix with zero row and column sums; optional centered cost and L1 bounds.
* **Objects:** A signed residual pairing with an edge cost.
* **Proof detail:** Cancel row/column potentials, apply the finite triangle inequality and use the centered uniform bound.

## Mathematical sources

* Gabriel Peyré; Marco Cuturi, *Computational Optimal Transport (2019 author version)*, Section 2.3, pp. 15–16, equations (2.10)–(2.11), fixed-marginal polytope and cost pairing.
  https://optimaltransport.github.io/pdf/ComputationalOT.pdf
* Terence Tao, *Analysis I*, Sections 4.3 (absolute value) and 7.1 (finite series), in particular Proposition 7.1.11.
  https://github.com/teorth/analysis/blob/main/Analysis/Section_7_1.lean

**Relationship to the sources:** The gauge cancellation is linear algebra from fixed marginals. The weighted bounds apply to signed residuals; the book does not state these Lean helper names.
-/

/-! # Finite coupling residuals

The reusable object is a real matrix `W` on arbitrary finite row and column types.
When every row and column sum vanishes, pairing `W` with a cost is unchanged by
adding a row potential and a column potential. Absolute bounds are weighted
finite triangle inequalities; no nonnegativity of `W` is required.

## Mathematical source

Gabriel Peyré and Marco Cuturi, *Computational Optimal Transport* (2019),
§2.3, pp. 15–16, equations (2.10) and (2.11): fixed row/column marginals and
the linear transport-cost pairing. Author PDF:
https://optimaltransport.github.io/pdf/ComputationalOT.pdf .
Annihilation of row/column potentials by a zero-marginal residual is a linear
algebra corollary of those constraints. The absolute bounds are finite triangle
inequality corollaries; see Terence Tao, *Analysis I*, §4.3 (absolute values)
and §7.1 (finite sums). These are derived lemmas, not verbatim numbered statements.

-/

open scoped BigOperators

namespace OTSelector.Finite

variable {I J : Type*} [Fintype I] [Fintype J]

/-- Zero marginal sums annihilate row and column potentials. -/
theorem sum_mul_rowColumn_eq_zero (W : I → J → ℝ)
    (hrow : ∀ i, ∑ j, W i j = 0) (hcol : ∀ j, ∑ i, W i j = 0)
    (row : I → ℝ) (column : J → ℝ) :
    ∑ i, ∑ j, W i j * (row i + column j) = 0 := by
  simp_rw [mul_add, Finset.sum_add_distrib]
  have hr : ∑ i, ∑ j, W i j * row i = 0 := by
    simp_rw [← Finset.sum_mul, hrow, zero_mul, Finset.sum_const_zero]
  have hc : ∑ i, ∑ j, W i j * column j = 0 := by
    rw [Finset.sum_comm]
    simp_rw [← Finset.sum_mul, hcol, zero_mul, Finset.sum_const_zero]
  rw [hr, hc, add_zero]

/-- A zero-marginal residual is invariant under row and column cost additions. -/
theorem sum_mul_add_rowColumn (W cost : I → J → ℝ)
    (hrow : ∀ i, ∑ j, W i j = 0) (hcol : ∀ j, ∑ i, W i j = 0)
    (row : I → ℝ) (column : J → ℝ) :
    ∑ i, ∑ j, W i j * (cost i j + (row i + column j)) =
      ∑ i, ∑ j, W i j * cost i j := by
  have hzero := sum_mul_rowColumn_eq_zero W hrow hcol row column
  simp_rw [mul_add, Finset.sum_add_distrib] at hzero ⊢
  rw [hzero, add_zero]

/-- The absolute residual is bounded by the cost weighted by absolute deviations. -/
theorem abs_sum_mul_le_weighted (W cost : I → J → ℝ) :
    |∑ i, ∑ j, W i j * cost i j| ≤ ∑ i, ∑ j, |W i j| * |cost i j| := by
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  refine Finset.sum_le_sum fun i _ ↦ (Finset.abs_sum_le_sum_abs _ _).trans ?_
  exact Finset.sum_le_sum fun j _ ↦ by rw [abs_mul]

/-- A uniform centered-cost bound controls a zero-marginal residual by its L1 mass. -/
theorem abs_sum_mul_le_of_centered (W cost : I → J → ℝ)
    (hrow : ∀ i, ∑ j, W i j = 0) (hcol : ∀ j, ∑ i, W i j = 0)
    (row : I → ℝ) (column : J → ℝ) {η F : ℝ} (hη0 : 0 ≤ η)
    (hcost : ∀ i j, |cost i j + (row i + column j)| ≤ η)
    (hmass : ∑ i, ∑ j, |W i j| ≤ F) :
    |∑ i, ∑ j, W i j * cost i j| ≤ η * F := by
  rw [← sum_mul_add_rowColumn W cost hrow hcol row column]
  calc
    _ ≤ ∑ i, ∑ j, |W i j| * |cost i j + (row i + column j)| :=
      abs_sum_mul_le_weighted W _
    _ ≤ ∑ i, ∑ j, |W i j| * η := by
      exact Finset.sum_le_sum fun i _ ↦ Finset.sum_le_sum fun j _ ↦
        mul_le_mul_of_nonneg_left (hcost i j) (abs_nonneg _)
    _ = η * (∑ i, ∑ j, |W i j|) := by
      simp only [← Finset.sum_mul, mul_comm η]
    _ ≤ η * F := mul_le_mul_of_nonneg_left hmass hη0

end OTSelector.Finite
