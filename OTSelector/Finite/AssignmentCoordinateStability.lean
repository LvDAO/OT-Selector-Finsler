import Mathlib.Analysis.Convex.Birkhoff
import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Data.Finset.Max
import Mathlib.Data.Real.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.MetricSpace.Lipschitz
import OTSelector.Finite.Assignment
import OTSelector.Finite.PerturbedValue

/-!
# Finite.AssignmentCoordinateStability

**Conditions:** Finite square costs; row/column error bounds or a bounded sampled edge kernel are explicit.

**Objects:** Optimal assignment value under replacement of a source and target coordinate.

**Proof detail:** Each permutation uses a given row and column exactly once, so its total error is bounded by the two row/column errors; compare attained minima and specialize a paired coordinate update to the 4B bound.

**Sources:** [Sheldon Axler, Supplement for Measure, Integration & Real Analysis](https://measure.axler.net/SupplementMIRA.pdf#page=18), Section C, Definitions 0.32 and 0.35, pp. 18–19; [Terence Tao, Analysis I](https://github.com/teorth/analysis/blob/main/Analysis/Section_7_1.lean), Sections 4.3 (absolute value) and 7.1 (finite series), in particular Proposition 7.1.11.

Source relation (corollary): The cited sections provide the stated mathematical foundations; the exact finite construction and quantitative bound in this module are local consequences, not a claim that the book states the Lean theorem verbatim.
-/

/-!
# Stability under replacing a source and a target

A replacement changes one row and one column. Every permutation uses each of
these once, so the attained minimum has the same bound, including arbitrary ties.
These deterministic bounds apply directly to paired independent sample coordinates.
-/

open scoped BigOperators

namespace OTSelector

variable {n : ℕ}

/-- A bounded edge cost bounds the attained total cost by the sample size. -/
theorem assignmentValue_abs_le_of_edge_bound
    (cost : Matrix (Fin n) (Fin n) ℝ) (B : ℝ) (h : ∀ i j, |cost i j| ≤ B) :
    |perturbedAssignmentValue cost 0 0| ≤ (n : ℝ) * B := by
  simp only [perturbedAssignmentValue, perturbedEdgeCost_zero, assignmentCost]
  calc
    _ ≤ ∑ i, |cost i (optimalAssignment cost i)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin n, B := Finset.sum_le_sum fun i _ ↦ h i _
    _ = _ := by simp

/-- A bound valid for every competing assignment also bounds the attained minima. -/
theorem assignmentValue_abs_sub_le_of_assignment_bound
    (cost cost' : Matrix (Fin n) (Fin n) ℝ) (D : ℝ)
    (h : ∀ σ : Assignment n, |assignmentCost cost σ - assignmentCost cost' σ| ≤ D) :
    |perturbedAssignmentValue cost 0 0 - perturbedAssignmentValue cost' 0 0| ≤ D := by
  apply abs_sub_le_iff.mpr
  constructor
  · obtain ⟨σ, _, hσ⟩ := perturbedAssignmentValue_attained cost' 0 0
    have hle := perturbedAssignmentValue_le cost 0 0 σ
    simp only [perturbedEdgeCost_zero] at hσ hle
    rw [hσ]
    exact (sub_le_sub_right hle _).trans (le_abs_self _ |>.trans (h σ))
  · obtain ⟨σ, _, hσ⟩ := perturbedAssignmentValue_attained cost 0 0
    have hle := perturbedAssignmentValue_le cost' 0 0 σ
    simp only [perturbedEdgeCost_zero] at hσ hle
    rw [hσ]
    have hb := (abs_le.mp (h σ)).1
    linarith

/-- Separate bounds on a single row and column are added once in every assignment. -/
theorem assignmentValue_abs_sub_le_of_row_column_bound
    (cost cost' : Matrix (Fin n) (Fin n) ℝ) (r s : Fin n) (A B : ℝ)
    (h : ∀ i j, |cost i j - cost' i j| ≤
      (if i = r then A else 0) + (if j = s then B else 0)) :
    |perturbedAssignmentValue cost 0 0 - perturbedAssignmentValue cost' 0 0| ≤ A + B := by
  apply assignmentValue_abs_sub_le_of_assignment_bound
  intro σ
  simp only [assignmentCost, ← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ i, |cost i (σ i) - cost' i (σ i)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, ((if i = r then A else 0) + (if σ i = s then B else 0)) :=
      Finset.sum_le_sum fun i _ ↦ h i (σ i)
    _ = A + B := by
      rw [Finset.sum_add_distrib, Equiv.sum_comp σ (fun j ↦ if j = s then B else 0)]
      simp

/-- Any bounded paired cost gives a uniform coordinate replacement bound for the
actual sample assignment minimum. Both coordinates are replaced together. -/
theorem assignmentValue_pair_update_abs_sub_le {S T : Type*}
    (c : S → T → ℝ) {B : ℝ} (hB : 0 ≤ B) (hc : ∀ x y, |c x y| ≤ B)
    (z : Fin n → S × T) (i : Fin n) (w : S × T) :
    |perturbedAssignmentValue (fun j k ↦ c (Function.update z i w j).1
        (Function.update z i w k).2) 0 0 -
      perturbedAssignmentValue (fun j k ↦ c (z j).1 (z k).2) 0 0| ≤ 4 * B := by
  have h := assignmentValue_abs_sub_le_of_row_column_bound
    (fun j k ↦ c (Function.update z i w j).1 (Function.update z i w k).2)
    (fun j k ↦ c (z j).1 (z k).2) i i (2 * B) (2 * B)
  apply (h ?_).trans_eq (by ring)
  intro j k
  have hab : |c (Function.update z i w j).1 (Function.update z i w k).2 -
      c (z j).1 (z k).2| ≤ 2 * B := by
    apply (abs_sub _ _).trans
    have hnew := hc (Function.update z i w j).1 (Function.update z i w k).2
    have hold := hc (z j).1 (z k).2
    linarith
  by_cases hj : j = i <;> by_cases hk : k = i
  · simp only [ite_eq_left hj, ite_eq_left hk]
    linarith
  · simpa only [ite_eq_left hj, ite_eq_right hk, add_zero] using hab
  · simpa only [ite_eq_right hj, ite_eq_left hk, zero_add] using hab
  · simp [hj, hk]

end OTSelector
