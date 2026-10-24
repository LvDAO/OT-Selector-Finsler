import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.BigOperators

/-!
# Finite.PartitionFiberSums

## Lemma skeleton

* **Conditions:** A finite set, a finite block-label type and an additive-valued integrand.

* **Objects:** Exact sums over block fibers, including total cardinalities.

* **Proof detail:** Apply the finite partition-by-fiber sum identity and specialize the summand to one for counts.

## Mathematical sources

- [Terence Tao, Analysis I](https://github.com/teorth/analysis/blob/main/Analysis/Section_7_1.lean): Sections 4.3 (absolute value) and 7.1 (finite series), in particular Proposition 7.1.11.

Source relation (adapter): Finite dependent-subtype encoding of the usual disjoint partition identity.
-/

/-! Actual original block restrictions partition unused costs and counts exactly. -/
open scoped BigOperators Classical
noncomputable section
namespace OTSelector.Reconstruction

/-- A literal original unused index occurs in exactly one block's sum. -/
theorem sum_originalUnusedBlock_restrictions
    {I B A : Type*} [DecidableEq I] [Fintype B] [AddCommMonoid A]
    (U : Finset I) (block : I → B) (f : I → A) :
    (∑ b, ∑ i : U.filter (fun i ↦ block i = b), f i.val) = ∑ i : U, f i.val := by
  classical
  simp_rw [Finset.sum_coe_sort,Finset.sum_filter]
  rw [Finset.sum_comm]
  simp

/-- In particular, the total local unused capacity is its true original cardinality. -/
theorem sum_originalUnusedBlock_cards
    {I B : Type*} [DecidableEq I] [Fintype B] (U : Finset I) (block : I → B) :
    (∑ b, (U.filter (fun i ↦ block i = b)).card) = U.card := by
  simpa using sum_originalUnusedBlock_restrictions U block (fun _ ↦ (1 : ℕ))

end OTSelector.Reconstruction
