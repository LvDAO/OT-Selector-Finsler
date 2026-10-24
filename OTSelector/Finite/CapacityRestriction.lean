import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.Convex.Birkhoff
import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Real.Basic
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.Tactic.Linarith
import Mathlib.Topology.Instances.Real.Lemmas
import OTSelector.Finite.CapacityAssignment

/-!
# Finite.CapacityRestriction

**Conditions:** Total allocation cost on the full finite source array is injective as a function of the allocation.

**Objects:** Cost injectivity for every retained source subtype.

**Proof detail:** Extend two subtype allocations by the same fixed target outside the subtype; their exterior cost cancels, so equality of subset costs gives full-cost equality and then equality of the original allocations.

**Sources:** [Terence Tao, Analysis I](https://github.com/teorth/analysis/blob/main/Analysis/Section_7_1.lean), Sections 4.3 (absolute value) and 7.1 (finite series), in particular Proposition 7.1.11.

Source relation (corollary): The cited sections provide the stated mathematical foundations; the exact finite construction and quantitative bound in this module are local consequences, not a claim that the book states the Lean theorem verbatim.
-/

/-!
# Cost uniqueness on actual source subsets

Extend two subset allocations by the same target outside the subset. Their total
cost difference is exactly the original subset cost difference. Consequently one
event of distinct full-array allocation costs also covers every retained subset.
-/

open scoped BigOperators

namespace OTSelector

variable {ι α : Type*} [Fintype ι]

/-- Injective full-array allocation costs imply injective costs on every actual
source subset. The subset may be chosen after the original costs are known. -/
theorem injective_capacityAssignmentCost_subtype
    (cost : ι → α → ℝ) (hinj : Function.Injective (capacityAssignmentCost cost))
    (p : ι → Prop) [DecidablePred p] :
    Function.Injective (capacityAssignmentCost (fun (i : {i // p i}) j ↦ cost i j)) := by
  classical
  cases isEmpty_or_nonempty α with
  | inl h =>
    let := h
    exact fun _ _ _ ↦ Subsingleton.elim _ _
  | inr h =>
    let := h
    let j₀ : α := Classical.arbitrary α
    let extend (a : {i // p i} → α) : ι → α :=
      fun i ↦ if hi : p i then a ⟨i, hi⟩ else j₀
    have hsplit (a : {i // p i} → α) :
        capacityAssignmentCost cost (extend a) =
          capacityAssignmentCost (fun (i : {i // p i}) j ↦ cost i j) a +
            ∑ i : {i // ¬ p i}, cost i j₀ := by
      have hsum := Fintype.sum_subtype_add_sum_subtype p (fun i ↦ cost i (extend a i))
      unfold capacityAssignmentCost
      rw [← hsum]
      congr 1
      · apply Finset.sum_congr rfl
        intro i _
        simp only [extend, dite_eq_left i.2]
      · apply Finset.sum_congr rfl
        intro i _
        simp only [extend, dite_eq_right i.2]
    intro a b hab
    have heq : extend a = extend b := hinj (by rw [hsplit a, hsplit b, hab])
    funext i
    have h := congrFun heq i
    simpa only [extend, dite_eq_left i.2] using h

end OTSelector
