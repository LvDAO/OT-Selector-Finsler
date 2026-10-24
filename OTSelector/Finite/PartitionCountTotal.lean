import LeanPool.Vlasov.OT.Coupling
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.MeasureTheory.Constructions.UnitInterval
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Measure.FiniteMeasureExt
import Mathlib.MeasureTheory.Measure.FiniteMeasurePi
import Mathlib.MeasureTheory.Measure.FiniteMeasureProd
import Mathlib.Probability.Distributions.Beta
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Tactic
import Mathlib.Topology.Algebra.Module.Cardinality
import OTSelector.Finite.HierarchicalAssignment
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Reconstruction.FinslerRelativeLawGlobalResidualSplice.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Reconstruction.FinslerRelativeLawGlobalResidualSplice`; the selected original proof blocks follow. -/
section

/-!
# Reconstruction.FinslerRelativeLawGlobalResidualSplice

**Conditions:** A finite index type and finite target label type, with arbitrary label map.

**Objects:** The total of all real partition counts and the original index cardinality.

**Proof detail:** Exchange the two finite sums; each index contributes exactly one nonzero label indicator, so the total equals the original number of indices.

**Sources:** [Terence Tao, Analysis I](https://github.com/teorth/analysis/blob/main/Analysis/Section_7_1.lean), Sections 4.3 (absolute value) and 7.1 (finite series), in particular Proposition 7.1.11.

Source relation (corollary): Only the selected generic source commands are covered. The cited book sections provide the finite assignment, finite-sum or coupling foundations; the exact construction and quantitative statement are local corollaries or Lean adapters, not a claim that the book contains the same named Lean lemma.
-/

/-! Splice the original true-type hierarchy matching with all retained cell
matchings. Bounded completion sees only original count and legal deficits. -/

open Set Function
open scoped BigOperators Classical
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

/-- A finite original histogram counts every original sample exactly once. -/
theorem sum_partitionCount_eq_card {I T : Type*} [Fintype I] [Fintype T]
    (x : I → T) : (∑ t, partitionCount x t) = Fintype.card I := by
  classical
  unfold partitionCount
  rw [Finset.sum_comm]
  simp [partitionIndicator, eq_comm]





end OTSelector.Reconstruction

end
end
