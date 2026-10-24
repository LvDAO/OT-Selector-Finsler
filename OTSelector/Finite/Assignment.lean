import Mathlib.Analysis.Real.Sqrt
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.Topology.Instances.Real.Lemmas
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Basic.Model; OTSelector.Finite.Assignment.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Basic.Model`; the selected original proof blocks follow. -/
section

/-!
# Finite samples for empirical Euclidean optimal transport

This file fixes the coordinate order used throughout the formalization.  A source point is
`(T, U)`, a target point is `(S, V)`, and a plan point is `((T, U), (S, V))`.  Physical Euclidean
points retain the paper's order `(U, T)` and `(2 + V, S)`.
-/

open Set

namespace OTSelector









/-- An assignment is a permutation of the target indices. -/
abbrev Assignment (n : ℕ) := Equiv.Perm (Fin n)



end OTSelector

end

/-! Original source unit: `OTSelector.Finite.Assignment`; the selected original proof blocks follow. -/
section

/-!
# Finite.Assignment

**Conditions:** An arbitrary real cost matrix on Fin n×Fin n, with no uniqueness or nonnegativity assumption.

**Objects:** Total permutation cost, the minimizer predicate, an attained optimizer and its chosen witness.

**Proof detail:** The finite permutation type is nonempty; attain the minimum of its real objective and choose one such witness, preserving all ties in the minimizer predicate.

**Sources:** [Gabriel Peyré; Marco Cuturi, Computational Optimal Transport (2019 author version)](https://optimaltransport.github.io/pdf/ComputationalOT.pdf), Section 2.3, pp. 15–16, equations (2.10)–(2.11), fixed-marginal polytope and cost pairing; [Sheldon Axler, Supplement for Measure, Integration & Real Analysis](https://measure.axler.net/SupplementMIRA.pdf#page=18), Section C, Definitions 0.32 and 0.35, pp. 18–19; [Terence Tao, Analysis I](https://github.com/teorth/analysis/blob/main/Analysis/Section_7_1.lean), Sections 4.3 (absolute value) and 7.1 (finite series), in particular Proposition 7.1.11.

Source relation (adapter): Only the selected generic source commands are covered. The cited book sections provide the finite assignment, finite-sum or coupling foundations; the exact construction and quantitative statement are local corollaries or Lean adapters, not a claim that the book contains the same named Lean lemma.
-/


/-!
# Basic.Model

**Conditions:** The selected alias takes a natural sample size n, including zero.

**Objects:** Assignment n, the type of permutations of Fin n.

**Proof detail:** Name the finite source-to-target bijection type used by the assignment objective; no other Basic.Model object or paper result belongs to this selected scope.

**Sources:** [Gabriel Peyré; Marco Cuturi, Computational Optimal Transport (2019 author version)](https://optimaltransport.github.io/pdf/ComputationalOT.pdf), Section 2.3, pp. 15–16, equations (2.10)–(2.11), fixed-marginal polytope and cost pairing.

Source relation (adapter): Only the selected generic source commands are covered. The cited book sections provide the finite assignment, finite-sum or coupling foundations; the exact construction and quantitative statement are local corollaries or Lean adapters, not a claim that the book contains the same named Lean lemma.
-/

/-!
# Finite assignments and optimal permutations
-/

open scoped BigOperators

namespace OTSelector

variable {n : ℕ}

/-- Total cost of a permutation for an arbitrary edge-cost matrix. -/
def assignmentCost (cost : Fin n → Fin n → ℝ) (σ : Assignment n) : ℝ :=
  ∑ i, cost i (σ i)

/-- A permutation is optimal when its total cost is no larger than every competitor's. -/
def OptimalAssignment (cost : Fin n → Fin n → ℝ) (σ : Assignment n) : Prop :=
  ∀ τ, assignmentCost cost σ ≤ assignmentCost cost τ

theorem exists_optimalAssignment (cost : Fin n → Fin n → ℝ) :
    ∃ σ, OptimalAssignment cost σ := by
  classical
  let _ : Fintype (Assignment n) := Fintype.ofFinite (Assignment n)
  obtain ⟨σ, -, hσ⟩ := Finset.univ.exists_min_image (assignmentCost cost) Finset.univ_nonempty
  exact ⟨σ, fun τ ↦ hσ τ (Finset.mem_univ τ)⟩

/-- A fixed noncomputable minimizing permutation. -/
noncomputable def optimalAssignment (cost : Fin n → Fin n → ℝ) : Assignment n :=
  Classical.choose (exists_optimalAssignment cost)

theorem optimalAssignment_isOptimal (cost : Fin n → Fin n → ℝ) :
    OptimalAssignment cost (optimalAssignment cost) :=
  Classical.choose_spec (exists_optimalAssignment cost)





end OTSelector

end
