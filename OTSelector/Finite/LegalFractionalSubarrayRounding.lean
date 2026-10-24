import OTSelector.Finite.Assignment
import OTSelector.Finite.LegalFractionalRounding
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Reconstruction.OriginalLegalFractionalPlanRoundingSubarrays.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Reconstruction.OriginalLegalFractionalPlanRoundingSubarrays`; the selected original proof blocks follow. -/
section

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

/-- A rectangular unit-capacity plan forces equal cardinalities of its two original sides. -/
theorem card_eq_of_unitCapacityPlan {I J : Type*} [Fintype I] [Fintype J]
    (P : I → J → ℝ) (hrow : ∀ i, ∑ j, P i j = 1)
    (hcol : ∀ j, ∑ i, P i j = 1) : Fintype.card I = Fintype.card J := by
  have htotal : (Fintype.card I : ℝ) = (Fintype.card J : ℝ) := by
    calc
      (Fintype.card I : ℝ) = ∑ i, ∑ j, P i j := by simp_rw [hrow]; simp
      _ = ∑ j, ∑ i, P i j := Finset.sum_comm
      _ = (Fintype.card J : ℝ) := by simp_rw [hcol]; simp
  exact_mod_cast htotal

/-- Rounding preserves the actual source and target labels, even for empty unused subarrays. -/
theorem exists_legalEquiv_le_unitCapacityPlanCost {I J : Type*} [Fintype I] [Fintype J]
    (P cost : I → J → ℝ) (hP : ∀ i j, 0 ≤ P i j)
    (hrow : ∀ i, ∑ j, P i j = 1) (hcol : ∀ j, ∑ i, P i j = 1)
    (R : I → J → Prop) (hlegal : ∀ i j, ¬ R i j → P i j = 0) :
    ∃ σ : I ≃ J, (∀ i, R i (σ i)) ∧
      (∑ i, cost i (σ i)) ≤ ∑ i, ∑ j, P i j * cost i j := by
  classical
  let e : I ≃ J := Fintype.equivOfCardEq (card_eq_of_unitCapacityPlan P hrow hcol)
  let eI : Fin (Fintype.card I) ≃ I := (Fintype.equivFin I).symm
  let eJ : Fin (Fintype.card I) ≃ J := eI.trans e
  let Q : Matrix (Fin (Fintype.card I)) (Fin (Fintype.card I)) ℝ :=
    fun i j ↦ P (eI i) (eJ j)
  let c : Matrix (Fin (Fintype.card I)) (Fin (Fintype.card I)) ℝ :=
    fun i j ↦ cost (eI i) (eJ j)
  have hr (i : Fin (Fintype.card I)) : ∑ j, Q i j = 1 := by
    change (∑ j, P (eI i) (eJ j)) = 1
    rw [eJ.sum_comp]
    exact hrow (eI i)
  have hc (j : Fin (Fintype.card I)) : ∑ i, Q i j = 1 := by
    change (∑ i, P (eI i) (eJ j)) = 1
    exact (eI.sum_comp (fun i ↦ P i (eJ j))).trans (hcol (eJ j))
  obtain ⟨τ, hτ, hcost⟩ := exists_legalAssignment_le_matrixCost Q c
    (fun i j ↦ hP (eI i) (eJ j)) hr hc (fun i j ↦ R (eI i) (eJ j))
    (fun i j ↦ hlegal (eI i) (eJ j))
  let σ : I ≃ J := (eI.symm.trans τ).trans eJ
  have hσ (i : Fin (Fintype.card I)) : σ (eI i) = eJ (τ i) := by simp [σ]
  refine ⟨σ, ?_, ?_⟩
  · intro i
    simpa only [← hσ, eI.apply_symm_apply] using hτ (eI.symm i)
  · have hleft : (∑ i, c i (τ i)) = ∑ i, cost i (σ i) := by
      simpa only [c, ← hσ] using eI.sum_comp (fun i ↦ cost i (σ i))
    have hright : (∑ i, ∑ j, Q i j * c i j) = ∑ i, ∑ j, P i j * cost i j := by
      simp only [Q, c]
      calc
        (∑ i, ∑ j, P (eI i) (eJ j) * cost (eI i) (eJ j)) =
            ∑ i : Fin (Fintype.card I), ∑ j : J, P (eI i) j * cost (eI i) j := by
          apply Finset.sum_congr rfl
          intro i _
          exact eJ.sum_comp (fun j ↦ P (eI i) j * cost (eI i) j)
        _ = ∑ i, ∑ j, P i j * cost i j := eI.sum_comp (fun i ↦ ∑ j, P i j * cost i j)
    rw [← hleft, ← hright]
    exact hcost



end OTSelector

end
