import OTSelector.Finite.Assignment
import Mathlib.Data.Finset.Max
import OTSelector.Basic.Model

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











/-- The exact empirical Euclidean optimizer used in `main.tex`. -/
noncomputable def FiniteSample.euclideanOptimizer (sample : FiniteSample n) : Assignment n :=
  optimalAssignment sample.euclideanEdgeCost

theorem FiniteSample.euclideanOptimizer_isOptimal (sample : FiniteSample n) :
    OptimalAssignment sample.euclideanEdgeCost sample.euclideanOptimizer :=
  optimalAssignment_isOptimal sample.euclideanEdgeCost

end OTSelector
