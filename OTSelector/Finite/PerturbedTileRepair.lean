import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.Convex.Birkhoff
import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Real.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.Tactic
import Mathlib.Tactic.Linarith
import Mathlib.Topology.Instances.Real.Lemmas
import OTSelector.Finite.BlockMatchingComparison
import OTSelector.Finite.BlockMaxValueComparison
import OTSelector.Finite.MaxCardValueAssignment
import OTSelector.Finite.PartialMatching
import OTSelector.Finite.PerturbedValue

/-!
# Finite.PerturbedTileRepair

**Conditions:** Balanced finite sample clouds have finite tile labels; tilted costs are bounded above by B≥0.

**Objects:** The physical assignment value bounded by rectangular tile optima plus half the total tile-count discrepancy.

**Proof detail:** Commute block restriction with affine tilting, identify square assignment and maximum-cardinality values, then apply the signed block comparison and its exact residual count bound.

**Sources:** [Reinhard Diestel, Graph Theory, 4th electronic edition (2010), corrected reprint 2012](https://diestel-graph-theory.com/Sample.pdf#page=2), Chapter 2 opening matching definition and Section 2.1, first three chapter pages; [Sheldon Axler, Supplement for Measure, Integration & Real Analysis](https://measure.axler.net/SupplementMIRA.pdf#page=18), Section C, Definitions 0.32 and 0.35, pp. 18–19; [Terence Tao, Analysis I](https://github.com/teorth/analysis/blob/main/Analysis/Section_7_1.lean), Sections 4.3 (absolute value) and 7.1 (finite series), in particular Proposition 7.1.11.

Source relation (composition): The cited sections provide the stated mathematical foundations; the exact finite construction and quantitative bound in this module are local consequences, not a claim that the book states the Lean theorem verbatim.
-/

/-!
# Tile repair for the physical assignment value

The physical semidiscrete pressure is the least permutation cost
`perturbedAssignmentValue`.  Partitioning rows and columns by the tile label and
applying the block decomposition of maximum-cardinality matchings gives

`value ≤ ∑_c (block value of tile c) + B · ½ ∑_c |#source(c) − #target(c)|`,

where `B` is a uniform bound on the tilted edge costs.  The block values are
maximum-cardinality values on rectangular submatrices, exactly the objects
produced by the marked-cube tile machinery.
-/

open scoped BigOperators

noncomputable section
namespace OTSelector
namespace PartialMatching

variable {n : ℕ} {β : Type*} [Fintype β] [DecidableEq β]

/-- The tilted block matrix of a tilted ambient matrix is the tilted block
matrix of the two components. -/
theorem blockCost_add_smul
    (blockS blockT : Fin n → β) (d g : Fin n → Fin n → ℝ) (t : ℝ) (c : β) :
    blockCost blockS blockT (fun i j => d i j + t * g i j) c =
      fun i j => blockCost blockS blockT d c i j + t * blockCost blockS blockT g c i j :=
  rfl

/-- **Physical tile repair.**  The least permutation cost is at most the sum of
the tile block values plus the uniform edge bound times the half label-count
discrepancy. -/
theorem perturbedAssignmentValue_le_sum_block_add_discrepancy
    (blockS blockT : Fin n → β) (d g : Fin n → Fin n → ℝ) (t B : ℝ)
    (hB0 : 0 ≤ B) (hB : ∀ i j, d i j + t * g i j ≤ B) :
    perturbedAssignmentValue d g t ≤
      (∑ c : β, maxCardValue (blockCost blockS blockT (perturbedEdgeCost d g t) c)) +
        B * ((1 / 2 : ℝ) * ∑ c : β,
          |(blockSizeS blockS c : ℝ) - (blockSizeT blockT c : ℝ)|) := by
  rw [← maxCardValue_eq_perturbedAssignmentValue]
  exact maxCardValue_le_sum_block_add_half_discrepancy blockS blockT
    (perturbedEdgeCost d g t) hB hB0

end PartialMatching
end OTSelector
