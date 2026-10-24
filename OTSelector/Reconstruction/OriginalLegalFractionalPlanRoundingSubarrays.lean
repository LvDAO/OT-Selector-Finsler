import OTSelector.Finite.LegalFractionalSubarrayRounding
import OTSelector.Finite.LegalFractionalRounding

/-!
# Reconstruction.OriginalLegalFractionalPlanRoundingSubarrays

**Conditions:** Arbitrary finite row/column types have a real nonnegative matrix with unit row and column sums and zero forbidden entries.

**Objects:** Equality of cardinalities and a legal original-type equivalence with cost no greater than the matrix cost.

**Proof detail:** Double-sum the unit marginals to identify cardinalities, enumerate both types by one Fin n, apply square-matrix legal rounding and transfer the resulting permutation back through the two equivalences.

**Sources:** [Gabriel Peyré; Marco Cuturi, Computational Optimal Transport (2019 author version)](https://optimaltransport.github.io/pdf/ComputationalOT.pdf#page=21), Section 2.3, Proposition 2.1 and its proof, pp. 17–18 (PDF pages 21–22); [Terence Tao, Analysis I](https://github.com/teorth/analysis/blob/main/Analysis/Section_7_1.lean), Sections 4.3 (absolute value) and 7.1 (finite series), in particular Proposition 7.1.11.

Source relation (generalization): Only the selected generic source commands are covered. The cited book sections provide the finite assignment, finite-sum or coupling foundations; the exact construction and quantitative statement are local corollaries or Lean adapters, not a claim that the book contains the same named Lean lemma.
-/

/-!
# Legal fractional rounding on unchanged finite source and target labels

The two index types can be the unused source and target subarrays. Unit row and column sums
force their cardinalities to agree, and the selected equivalence acts on those original labels.
No cardinality maximality or already completed legal bijection is supplied.
-/

open scoped BigOperators

namespace OTSelector





/-- A plan on literal finite subsets returns a legal bijection on precisely those subsets. -/
theorem exists_legalSubarrayEquiv_le_matrixCost {I J : Type*}
    (S : Finset I) (T : Finset J) (P : S → T → ℝ) (cost : I → J → ℝ)
    (hP : ∀ i j, 0 ≤ P i j) (hrow : ∀ i, ∑ j, P i j = 1)
    (hcol : ∀ j, ∑ i, P i j = 1) (R : I → J → Prop)
    (hlegal : ∀ (i : S) (j : T), ¬ R (i : I) (j : J) → P i j = 0) :
    ∃ σ : S ≃ T, (∀ i : S, R (i : I) (σ i : J)) ∧
      (∑ i : S, cost i (σ i)) ≤ ∑ i : S, ∑ j : T, P i j * cost i j := by
  exact exists_legalEquiv_le_unitCapacityPlanCost P (fun i j ↦ cost i j) hP hrow hcol
    (fun i j ↦ R i j) hlegal

end OTSelector
