import Mathlib.Analysis.Convex.Birkhoff
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Data.Finset.Max
import Mathlib.Data.Real.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.Topology.Instances.Real.Lemmas
import OTSelector.Finite.Assignment
import OTSelector.Finite.FractionalOptimal

/-!
# Finite.FractionalUnique

**Conditions:** The original finite permutation optimum is unique.

**Objects:** The singleton fractional optimal face and its permutation matrix.

**Proof detail:** Decompose any fractional optimum into optimal permutations; uniqueness makes all positive-weight components the same matrix, so their convex sum equals it.

**Sources:** [Gabriel Peyré; Marco Cuturi, Computational Optimal Transport (2019 author version)](https://optimaltransport.github.io/pdf/ComputationalOT.pdf#page=21), Section 2.3, Proposition 2.1 and its proof, pp. 17–18 (PDF pages 21–22); [Terence Tao, Analysis I](https://github.com/teorth/analysis/blob/main/Analysis/Section_7_1.lean), Sections 4.3 (absolute value) and 7.1 (finite series), in particular Proposition 7.1.11.

Source relation (corollary): The cited sections provide the stated mathematical foundations; the exact finite construction and quantitative bound in this module are local consequences, not a claim that the book states the Lean theorem verbatim.
-/

/-!
# A singleton fractional optimal face from a unique optimal permutation

The original Birkhoff decomposition expresses every fractional optimum as a convex combination
of optimal permutations. If the original permutation problem has only one optimizer, the whole
fractional optimal face consists of its permutation matrix. No optimizer selection is assumed.
-/

open scoped BigOperators

namespace OTSelector

variable {n : ℕ}

/-- Every fractional optimum equals the matrix of the unique optimal permutation. -/
theorem optimalFractionalAssignment_eq_permMatrix_of_unique
    (cost P : Matrix (Fin n) (Fin n) ℝ) (σ : Assignment n)
    (hunique : ∀ τ, OptimalAssignment cost τ → τ = σ)
    (hP : OptimalFractionalAssignment cost P) : P = σ.permMatrix ℝ := by
  classical
  obtain ⟨w, hw, hsum, hdecomp, hopt⟩ :=
    optimalFractionalAssignment_decomposition cost P hP
  have hzero (τ : Assignment n) (hτ : τ ≠ σ) : w τ = 0 := by
    apply le_antisymm _ (hw τ)
    exact le_of_not_gt fun hpos ↦ hτ (hunique τ (hopt τ hpos))
  have hsum' : ∑ τ, w τ = w σ := by
    apply Finset.sum_eq_single σ
    · intro τ _ hτ
      exact hzero τ hτ
    · simp
  have hσ : w σ = 1 := hsum'.symm.trans hsum
  calc
    P = ∑ τ, w τ • τ.permMatrix ℝ := hdecomp.symm
    _ = w σ • σ.permMatrix ℝ := by
      apply Finset.sum_eq_single σ
      · intro τ _ hτ
        rw [hzero τ hτ, zero_smul]
      · simp
    _ = σ.permMatrix ℝ := by rw [hσ, one_smul]

/-- Uniqueness of the permutation optimum implies uniqueness of the full fractional optimum. -/
theorem existsUnique_optimalFractionalAssignment_of_existsUnique_optimalAssignment
    (cost : Matrix (Fin n) (Fin n) ℝ) (h : ∃! σ, OptimalAssignment cost σ) :
    ∃! P, OptimalFractionalAssignment cost P := by
  obtain ⟨σ, hσ, huniq⟩ := h
  refine ⟨σ.permMatrix ℝ, ⟨permMatrix_mem_doublyStochastic, ?_⟩, ?_⟩
  · intro Q hQ
    rw [fractionalAssignmentCost_permMatrix]
    exact assignmentCost_le_fractionalAssignmentCost cost Q σ hσ hQ
  · intro P hP
    exact optimalFractionalAssignment_eq_permMatrix_of_unique cost P σ huniq hP

end OTSelector
