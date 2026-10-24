import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.Convex.Birkhoff
import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Real.Basic
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.GroupTheory.Perm.ViaEmbedding
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Logic.Relation
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.Tactic.Linarith
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.MetricSpace.Lipschitz
import OTSelector.Finite.CapacityAssignment

/-!
# Finite.TargetTreeGluing

**Conditions:** A finite source set is split by a decidable predicate; the two allocations meet their respective integer quotas.

**Objects:** The piecewise glued allocation, additive quotas and additive cost.

**Proof detail:** Count target fibers separately on the predicate and its complement, then use the finite-sum subtype partition identity to split the objective.

**Sources:** [Terence Tao, Analysis I](https://github.com/teorth/analysis/blob/main/Analysis/Section_7_1.lean), Sections 4.3 (absolute value) and 7.1 (finite series), in particular Proposition 7.1.11; [Gabriel Peyré; Marco Cuturi, Computational Optimal Transport (2019 author version)](https://optimaltransport.github.io/pdf/ComputationalOT.pdf), Section 2.3, pp. 15–16, equations (2.10)–(2.11), fixed-marginal polytope and cost pairing.

Source relation (corollary): The cited sections provide the stated mathematical foundations; the exact finite construction and quantitative bound in this module are local consequences, not a claim that the book states the Lean theorem verbatim.
-/

/-!
# Gluing a retained cavity allocation to its complementary cell choices

Feasible allocations on complementary source subsets add their target counts exactly.
The gluing identities below retain the actual finite source labels and costs.
-/

open scoped BigOperators

noncomputable section
namespace OTSelector

universe u v
variable {ι : Type u} {α : Type v} [Fintype ι] [DecidableEq α]

/-- Join allocations on complementary subsets without changing any source label. -/
def glueCapacityAssignments (P : ι → Prop) [DecidablePred P]
    (a : {k // P k} → α) (b : {k // ¬ P k} → α) : ι → α :=
  fun k ↦ if hk : P k then a ⟨k, hk⟩ else b ⟨k, hk⟩

omit [Fintype ι] [DecidableEq α] in
@[simp]
theorem glueCapacityAssignments_of_pos (P : ι → Prop) [DecidablePred P]
    (a : {k // P k} → α) (b : {k // ¬ P k} → α) (k : ι) (hk : P k) :
    glueCapacityAssignments P a b k = a ⟨k, hk⟩ := by
  simp [glueCapacityAssignments, hk]

omit [Fintype ι] [DecidableEq α] in
@[simp]
theorem glueCapacityAssignments_of_neg (P : ι → Prop) [DecidablePred P]
    (a : {k // P k} → α) (b : {k // ¬ P k} → α) (k : ι) (hk : ¬ P k) :
    glueCapacityAssignments P a b k = b ⟨k, hk⟩ := by
  simp [glueCapacityAssignments, hk]

/-- Target multiplicities add when allocations on complementary source subsets are joined. -/
theorem capacityFeasible_glue (P : ι → Prop) [DecidablePred P]
    (r s : α → ℕ) (a : {k // P k} → α) (b : {k // ¬ P k} → α)
    (ha : CapacityFeasible r a) (hb : CapacityFeasible s b) :
    CapacityFeasible (fun j ↦ r j + s j) (glueCapacityAssignments P a b) := by
  intro j
  have hcard {κ : Type u} [Fintype κ] (f : κ → α) :
      Fintype.card {k // f k = j} = ∑ k, if f k = j then 1 else 0 := by
    simp [Fintype.card_subtype, Finset.sum_boole]
  rw [hcard, ← Fintype.sum_subtype_add_sum_subtype P
    (fun k ↦ if glueCapacityAssignments P a b k = j then 1 else 0)]
  have hp (k : {k // P k}) : glueCapacityAssignments P a b k = a k :=
    glueCapacityAssignments_of_pos P a b k k.2
  have hn (k : {k // ¬ P k}) : glueCapacityAssignments P a b k = b k :=
    glueCapacityAssignments_of_neg P a b k k.2
  simp only [hp, hn]
  rw [← hcard, ← hcard, ha j, hb j]

omit [DecidableEq α] in
/-- The actual cost of the glued allocation is the sum of its two actual costs. -/
theorem capacityAssignmentCost_glue (P : ι → Prop) [DecidablePred P]
    (cost : ι → α → ℝ) (a : {k // P k} → α) (b : {k // ¬ P k} → α) :
    capacityAssignmentCost cost (glueCapacityAssignments P a b) =
      capacityAssignmentCost (fun (k : {k // P k}) j ↦ cost k j) a +
        capacityAssignmentCost (fun (k : {k // ¬ P k}) j ↦ cost k j) b := by
  unfold capacityAssignmentCost
  rw [← Fintype.sum_subtype_add_sum_subtype P
    (fun k ↦ cost k (glueCapacityAssignments P a b k))]
  have hp (k : {k // P k}) : glueCapacityAssignments P a b k = a k :=
    glueCapacityAssignments_of_pos P a b k k.2
  have hn (k : {k // ¬ P k}) : glueCapacityAssignments P a b k = b k :=
    glueCapacityAssignments_of_neg P a b k k.2
  simp only [hp, hn]

end OTSelector
