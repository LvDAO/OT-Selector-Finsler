import OTSelector.Reconstruction.TaggedDyadicCompetitorEnergy
import Mathlib.Logic.Equiv.Sum

/-!
# Replace local blocks of one full original assignment

The source fibres identify retained equal-type edges of a full competitor. A
permutation inside each fibre only changes its target partners; all prescribed
fixed fibres, in particular count-completion edges, remain unchanged.
-/

open Set Function MeasureTheory
open scoped BigOperators
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false

variable {T : Type*} {n : ℕ}

/-- Permuting within the source fibres and then applying the original assignment
replaces local blocks while retaining a full global permutation. -/
def replaceAssignmentBlocks (σ : Assignment n) (tag : Fin n → T)
    (θ : ∀ t, Equiv.Perm {i // tag i = t}) : Assignment n :=
  (((Equiv.sigmaFiberEquiv tag).symm.trans (Equiv.sigmaCongrRight θ)).trans
    (Equiv.sigmaFiberEquiv tag)).trans σ

theorem replaceAssignmentBlocks_apply (σ : Assignment n) (tag : Fin n → T)
    (θ : ∀ t, Equiv.Perm {i // tag i = t}) (i : Fin n) :
    replaceAssignmentBlocks σ tag θ i = σ (θ (tag i) ⟨i, rfl⟩).val := rfl

/-- A block with identity replacement retains every original target partner. -/
theorem replaceAssignmentBlocks_eq_of_fixed (σ : Assignment n) (tag : Fin n → T)
    (θ : ∀ t, Equiv.Perm {i // tag i = t}) {t : T}
    (hθ : θ t = Equiv.refl _) (i : Fin n) (hi : tag i = t) :
    replaceAssignmentBlocks σ tag θ i = σ i := by
  subst t
  rw [replaceAssignmentBlocks_apply, hθ]
  rfl

/-- The exact global cost is the sum of costs on the same retained source blocks. -/
theorem assignmentCost_replaceAssignmentBlocks [Fintype T] [DecidableEq T]
    (cost : Fin n → Fin n → ℝ) (σ : Assignment n) (tag : Fin n → T)
    (θ : ∀ t, Equiv.Perm {i // tag i = t}) :
    assignmentCost cost (replaceAssignmentBlocks σ tag θ) =
      ∑ t, ∑ i : {i // tag i = t}, cost i.val (σ (θ t i).val) := by
  unfold assignmentCost
  rw [← Equiv.sum_comp (Equiv.sigmaFiberEquiv tag)]
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro t _
  apply Finset.sum_congr rfl
  intro i _
  rcases i with ⟨i, hi⟩
  subst t
  rfl

/-- Pointwise block upper bounds glue into a bound for the original full pressure. -/
theorem assignmentValue_le_replaced_blocks [Fintype T] [DecidableEq T]
    (cost : Fin n → Fin n → ℝ) (σ : Assignment n) (tag : Fin n → T)
    (θ : ∀ t, Equiv.Perm {i // tag i = t}) (bound : T → ℝ)
    (hbound : ∀ t, (∑ i : {i // tag i = t}, cost i.val (σ (θ t i).val)) ≤ bound t) :
    perturbedAssignmentValue cost 0 0 ≤ ∑ t, bound t := by
  have h := perturbedAssignmentValue_le cost 0 0 (replaceAssignmentBlocks σ tag θ)
  simp only [perturbedEdgeCost_zero] at h
  rw [assignmentCost_replaceAssignmentBlocks] at h
  exact h.trans (Finset.sum_le_sum (fun t _ ↦ hbound t))

end OTSelector.Reconstruction
