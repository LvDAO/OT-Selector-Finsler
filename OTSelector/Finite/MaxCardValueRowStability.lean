import Mathlib.Analysis.Convex.Function
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import Mathlib.Tactic.Linarith
import OTSelector.Finite.MaxCardValueSigned
import OTSelector.Finite.PartialMatching

/-!
# Finite.MaxCardValueRowStability

**Conditions:** Two finite cost matrices agree off a specified row set S and differ by at most B≥0 on S.

**Objects:** Affected matching edges and the corresponding optimal-value perturbation.

**Proof detail:** Project affected edges injectively to rows to bound their count by |S|; bound their summed errors and apply the common-infimum comparison, specializing S to one row.

**Sources:** [Reinhard Diestel, Graph Theory, 4th electronic edition (2010), corrected reprint 2012](https://diestel-graph-theory.com/Sample.pdf#page=2), Chapter 2 opening matching definition and Section 2.1, first three chapter pages; [Sheldon Axler, Supplement for Measure, Integration & Real Analysis](https://measure.axler.net/SupplementMIRA.pdf#page=18), Section C, Definitions 0.32 and 0.35, pp. 18–19; [Terence Tao, Analysis I](https://github.com/teorth/analysis/blob/main/Analysis/Section_7_1.lean), Sections 4.3 (absolute value) and 7.1 (finite series), in particular Proposition 7.1.11.

Source relation (corollary): The cited sections provide the stated mathematical foundations; the exact finite construction and quantitative bound in this module are local consequences, not a claim that the book states the Lean theorem verbatim.
-/

/-!
# One-row stability of the maximum-cardinality value

If two cost matrices agree off a single row, and their entries in that row differ
by at most `B`, then the minimum costs of maximum-cardinality matchings differ by
at most `B` as well.  A maximum-cardinality matching uses any row at most once,
so only one matched edge can feel the change.

This is the per-point stability needed to transfer the matching pressure across a
coupling that moves a single sample point.
-/

open scoped BigOperators

noncomputable section
namespace OTSelector

namespace PartialMatching

variable {m n : ℕ}

/-- The number of matched edges whose row lies in a finite set is at most the
cardinality of that set. -/
theorem card_filter_rows_le (σ : PartialMatching m n) (S : Finset (Fin m)) :
    (σ.edges.filter (fun p => p.1 ∈ S)).card ≤ S.card := by
  classical
  have hsub : (σ.edges.filter (fun p => p.1 ∈ S)).image Prod.fst ⊆ S := by
    intro i hi
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hi
    rw [Finset.mem_filter] at hp
    exact hp.2
  have hinj : Set.InjOn Prod.fst
      (((σ.edges.filter (fun p : Fin m × Fin n => p.1 ∈ S) : Finset (Fin m × Fin n)) :
        Set (Fin m × Fin n))) := by
    intro a ha b hb h
    rw [Finset.mem_coe, Finset.mem_filter] at ha hb
    exact σ.row_inj a ha.1 b hb.1 h
  calc (σ.edges.filter (fun p => p.1 ∈ S)).card
      = ((σ.edges.filter (fun p => p.1 ∈ S)).image Prod.fst).card := by
        rw [Finset.card_image_of_injOn hinj]
    _ ≤ S.card := Finset.card_le_card hsub

/-- The cost difference of one matching is bounded by `B` times the number of
rows on which the two cost matrices differ. -/
theorem cost_sub_le_of_off_rows (c d : Fin m → Fin n → ℝ) (σ : PartialMatching m n)
    {B : ℝ} (hB0 : 0 ≤ B) (S : Finset (Fin m))
    (hrow : ∀ i ∈ S, ∀ j, |c i j - d i j| ≤ B)
    (hoff : ∀ i, i ∉ S → ∀ j, c i j = d i j) :
    |σ.cost c - σ.cost d| ≤ B * (S.card : ℝ) := by
  classical
  unfold cost
  rw [← Finset.sum_sub_distrib]
  have hsplit := Finset.sum_filter_add_sum_filter_not
    (s := σ.edges) (p := fun p : Fin m × Fin n => p.1 ∈ S)
    (f := fun p : Fin m × Fin n => c p.1 p.2 - d p.1 p.2)
  have hnot : ∑ p ∈ σ.edges.filter (fun p : Fin m × Fin n => ¬ p.1 ∈ S),
      (c p.1 p.2 - d p.1 p.2) = 0 := by
    apply Finset.sum_eq_zero
    intro p hp
    rw [Finset.mem_filter] at hp
    rw [hoff p.1 hp.2 p.2, sub_self]
  have hone : |∑ p ∈ σ.edges.filter (fun p : Fin m × Fin n => p.1 ∈ S),
      (c p.1 p.2 - d p.1 p.2)| ≤ B * (S.card : ℝ) := by
    calc |∑ p ∈ σ.edges.filter (fun p : Fin m × Fin n => p.1 ∈ S),
          (c p.1 p.2 - d p.1 p.2)|
        ≤ ∑ p ∈ σ.edges.filter (fun p : Fin m × Fin n => p.1 ∈ S),
            |c p.1 p.2 - d p.1 p.2| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _p ∈ σ.edges.filter (fun p : Fin m × Fin n => p.1 ∈ S), B := by
          apply Finset.sum_le_sum
          intro p hp
          rw [Finset.mem_filter] at hp
          exact hrow p.1 hp.2 p.2
      _ = B * ((σ.edges.filter (fun p : Fin m × Fin n => p.1 ∈ S)).card : ℝ) := by
          rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
      _ ≤ B * (S.card : ℝ) := by
          apply mul_le_mul_of_nonneg_left _ hB0
          exact_mod_cast σ.card_filter_rows_le S
  rw [← hsplit, hnot, add_zero]
  exact hone

/-- **Multi-row stability.**  If two cost matrices agree outside a finite set of
rows `S` and differ by at most `B` on those rows, then the maximum-cardinality
values differ by at most `B * #S`. -/
theorem abs_maxCardValue_sub_le_of_off_rows (c d : Fin m → Fin n → ℝ) {B : ℝ}
    (hB0 : 0 ≤ B) (S : Finset (Fin m))
    (hrow : ∀ i ∈ S, ∀ j, |c i j - d i j| ≤ B)
    (hoff : ∀ i, i ∉ S → ∀ j, c i j = d i j) :
    |maxCardValue c - maxCardValue d| ≤ B * (S.card : ℝ) := by
  exact abs_maxCardValue_sub_le_of_cost_bound c d
    (fun σ _ ↦ cost_sub_le_of_off_rows c d σ hB0 S hrow hoff)

/-- **One-row stability.**  Changing the entries of a single row by at most `B`
changes the maximum-cardinality value by at most `B`. -/
theorem abs_maxCardValue_sub_le_of_off_row (c d : Fin m → Fin n → ℝ) {B : ℝ}
    (hB0 : 0 ≤ B) (i0 : Fin m)
    (hrow : ∀ j, |c i0 j - d i0 j| ≤ B)
    (hoff : ∀ i, i ≠ i0 → ∀ j, c i j = d i j) :
    |maxCardValue c - maxCardValue d| ≤ B := by
  simpa using abs_maxCardValue_sub_le_of_off_rows c d hB0 {i0}
    (fun i hi j ↦ by simpa only [Finset.mem_singleton.mp hi] using hrow j)
    (fun i hi j ↦ hoff i (by simpa using hi) j)


end PartialMatching

end OTSelector
