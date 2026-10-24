import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.Convex.Birkhoff
import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Real.Basic
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.Tactic.Linarith
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.MetricSpace.Lipschitz
import OTSelector.Finite.HierarchicalAssignment

/-!
# Finite.PartitionCount

**Conditions:** A finite index type and decidable equality on its labels.

**Objects:** Indicator-sum partition counts and cardinalities of the corresponding label fibers.

**Proof detail:** Rewrite the indicator sum as the finite sum of ones over the filtered fiber and use the finite-cardinality identity.

**Sources:** [Terence Tao, Analysis I](https://github.com/teorth/analysis/blob/main/Analysis/Section_7_1.lean), Sections 4.3 (absolute value) and 7.1 (finite series), in particular Proposition 7.1.11.

Source relation (adapter): The cited sections provide the stated mathematical foundations; the exact finite construction and quantitative bound in this module are local consequences, not a claim that the book states the Lean theorem verbatim.
-/

/-!
# Real partition counts and finite cardinalities

The indicator-sum partition count agrees with the cardinality of its label fiber.
This shared fact is used by hierarchical finite repair and Poisson cloud estimates.
-/

noncomputable section
namespace OTSelector

open OTSelector.Reconstruction

/-- The real partition count is the cardinality of the corresponding filter. -/
theorem partitionCount_eq_card_filter {I C : Type*} [Fintype I] [DecidableEq C]
    (x : I → C) (a : C) :
    partitionCount x a = ((Finset.univ.filter (fun i => x i = a)).card : ℝ) := by
  classical
  have h : ∀ i, partitionIndicator (x i) a = if x i = a then (1 : ℝ) else 0 := by
    intro i
    unfold partitionIndicator
    split_ifs <;> rfl
  rw [partitionCount]
  rw [Finset.sum_congr rfl (fun i _ => h i)]
  exact Finset.sum_boole (fun i => x i = a) Finset.univ

end OTSelector
