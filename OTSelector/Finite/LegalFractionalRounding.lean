import LeanPool.Vlasov.OT.Coupling
import OTSelector.Finite.Assignment
import OTSelector.Finite.FractionalOptimal
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Reconstruction.OriginalLegalFractionalPlanRounding.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Reconstruction.OriginalLegalFractionalPlanRounding`; the selected original proof blocks follow. -/
section

/-!
# Reconstruction.OriginalLegalFractionalPlanRounding

**Conditions:** An actual finite doubly stochastic matrix has zero entries on all forbidden pairs; signed costs and the empty matrix are allowed.

**Objects:** A Birkhoff decomposition supported on legal permutations and one legal permutation of no greater total cost.

**Proof detail:** A positive decomposition coefficient forces every used entry to be positive and hence legal; some positively weighted permutation costs no more than the convex average, giving cost-preserving legal rounding.

**Sources:** [Gabriel Peyré; Marco Cuturi, Computational Optimal Transport (2019 author version)](https://optimaltransport.github.io/pdf/ComputationalOT.pdf#page=21), Section 2.3, Proposition 2.1 and its proof, pp. 17–18 (PDF pages 21–22); [Gabriel Peyré; Marco Cuturi, Computational Optimal Transport (2019 author version)](https://optimaltransport.github.io/pdf/ComputationalOT.pdf), Section 2.3, pp. 15–16, equations (2.10)–(2.11), fixed-marginal polytope and cost pairing; [Terence Tao, Analysis I](https://github.com/teorth/analysis/blob/main/Analysis/Section_7_1.lean), Sections 4.3 (absolute value) and 7.1 (finite series), in particular Proposition 7.1.11.

Source relation (corollary): Only the selected generic source commands are covered. The cited book sections provide the finite assignment, finite-sum or coupling foundations; the exact construction and quantitative statement are local corollaries or Lean adapters, not a claim that the book contains the same named Lean lemma.
-/

/-!
# Cost-preserving legal rounding of an actual finite fractional plan

A genuine doubly-stochastic matrix has a Birkhoff decomposition supported on permutations
using only its positive entries. Consequently, if every illegal entry vanishes, one of its
legal permutations has no greater total cost for any signed real edge cost. The empty matrix
is covered by the same argument; no positive-cardinality assumption is needed.
-/

open scoped BigOperators

namespace OTSelector

variable {n : ℕ}

/-- Every positive Birkhoff coefficient uses only legal entries of the original matrix. -/
theorem legalFractionalAssignment_decomposition
    (P : Matrix (Fin n) (Fin n) ℝ) (hP : P ∈ doublyStochastic ℝ (Fin n))
    (R : Fin n → Fin n → Prop) (hlegal : ∀ i j, ¬ R i j → P i j = 0) :
    ∃ w : Assignment n → ℝ, (∀ σ, 0 ≤ w σ) ∧ (∑ σ, w σ = 1) ∧
      (∑ σ, w σ • σ.permMatrix ℝ = P) ∧
      ∀ σ, 0 < w σ → ∀ i, R i (σ i) := by
  classical
  obtain ⟨w, hw, hsum, hdecomp⟩ := exists_eq_sum_perm_of_mem_doublyStochastic hP
  refine ⟨w, hw, hsum, hdecomp, ?_⟩
  intro σ hσ i
  have hentry : (∑ τ, w τ * τ.permMatrix ℝ i (σ i)) = P i (σ i) := by
    simpa only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul] using
      congrArg (fun M : Matrix (Fin n) (Fin n) ℝ ↦ M i (σ i)) hdecomp
  have hσentry : w σ ≤ P i (σ i) := by
    calc
      w σ = w σ * σ.permMatrix ℝ i (σ i) := by
        simp [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply]
      _ ≤ ∑ τ, w τ * τ.permMatrix ℝ i (σ i) := by
        apply Finset.single_le_sum (f := fun τ ↦ w τ * τ.permMatrix ℝ i (σ i))
          (fun τ _ ↦ ?_) (Finset.mem_univ σ)
        exact mul_nonneg (hw τ)
          ((permMatrix_mem_doublyStochastic (R := ℝ) (σ := τ)).1 i (σ i))
      _ = P i (σ i) := hentry
  by_contra hi
  rw [hlegal i (σ i) hi] at hσentry
  exact (not_lt_of_ge hσentry) hσ

/-- A legal permutation rounds an actual feasible matrix without increasing any signed cost. -/
theorem exists_legalAssignment_le_fractionalAssignmentCost
    (P cost : Matrix (Fin n) (Fin n) ℝ) (hP : P ∈ doublyStochastic ℝ (Fin n))
    (R : Fin n → Fin n → Prop) (hlegal : ∀ i j, ¬ R i j → P i j = 0) :
    ∃ σ : Assignment n, (∀ i, R i (σ i)) ∧
      assignmentCost cost σ ≤ fractionalAssignmentCost cost P := by
  classical
  obtain ⟨w, hw, hsum, hdecomp, hsupport⟩ :=
    legalFractionalAssignment_decomposition P hP R hlegal
  let S : Finset (Assignment n) := Finset.univ.filter fun σ ↦ 0 < w σ
  have hS : S.Nonempty := by
    obtain ⟨σ, _, hσ⟩ := (Finset.sum_pos_iff_of_nonneg (fun σ _ ↦ hw σ)).mp
      (show 0 < ∑ σ, w σ by rw [hsum]; norm_num)
    exact ⟨σ, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hσ⟩⟩
  obtain ⟨σ, hσ, hmin⟩ := S.exists_min_image (assignmentCost cost) hS
  refine ⟨σ, hsupport σ (Finset.mem_filter.mp hσ).2, ?_⟩
  calc
    assignmentCost cost σ = ∑ τ, w τ * assignmentCost cost σ := by
      rw [← Finset.sum_mul, hsum, one_mul]
    _ ≤ ∑ τ, w τ * assignmentCost cost τ := by
      apply Finset.sum_le_sum
      intro τ _
      by_cases hτ : 0 < w τ
      · exact mul_le_mul_of_nonneg_left
          (hmin τ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hτ⟩)) (hw τ)
      · have hz : w τ = 0 := le_antisymm (not_lt.mp hτ) (hw τ)
        simp [hz]
    _ = fractionalAssignmentCost cost P := by
      rw [← fractionalAssignmentCost_sum_perm, hdecomp]

/-- Entrywise feasibility suffices; no completed integral comparator is assumed. -/
theorem exists_legalAssignment_le_matrixCost
    (P cost : Matrix (Fin n) (Fin n) ℝ)
    (hP : ∀ i j, 0 ≤ P i j) (hrow : ∀ i, ∑ j, P i j = 1)
    (hcol : ∀ j, ∑ i, P i j = 1) (R : Fin n → Fin n → Prop)
    (hlegal : ∀ i j, ¬ R i j → P i j = 0) :
    ∃ σ : Assignment n, (∀ i, R i (σ i)) ∧
      (∑ i, cost i (σ i)) ≤ ∑ i, ∑ j, P i j * cost i j := by
  exact exists_legalAssignment_le_fractionalAssignmentCost P cost
    (mem_doublyStochastic_iff_sum.mpr ⟨hP, hrow, hcol⟩) R hlegal

end OTSelector

end
