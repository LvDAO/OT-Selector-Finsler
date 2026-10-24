import OTSelector.Reconstruction.AssignmentBlockReplacement

/-!
# Exact local pressure replacement inside one full competitor

Each source block uses the original competitor's target indices. Its exact
minimum is inserted into the full permutation; the distinguished remainder
block is kept fixed, so all prescribed repair edges remain literally unchanged.
-/

open Set Function MeasureTheory Matrix
open scoped BigOperators
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false

variable {T : Type*} {n : ℕ} [DecidableEq T]

/-- The actual finite cost on the source indices of one block and precisely the
original target indices assigned to that block. -/
def assignmentBlockCost (cost : Fin n → Fin n → ℝ) (σ : Assignment n)
    (tag : Fin n → T) (t : T) :
    Matrix (Fin (Fintype.card {i // tag i = t})) (Fin (Fintype.card {i // tag i = t})) ℝ :=
  fun i j ↦ cost ((Fintype.equivFin {i // tag i = t}).symm i).val
    (σ ((Fintype.equivFin {i // tag i = t}).symm j).val)

/-- The fixed measurable finite tie rule on a block, expressed in its original
source-index fibre. -/
def optimalAssignmentBlock (cost : Fin n → Fin n → ℝ) (σ : Assignment n)
    (tag : Fin n → T) (t : T) : Equiv.Perm {i // tag i = t} :=
  ((Fintype.equivFin {i // tag i = t}).trans
    (firstOptimalAssignment (assignmentBlockCost cost σ tag t))).trans
      (Fintype.equivFin {i // tag i = t}).symm

/-- The replacement block realizes its literal finite pressure. -/
theorem optimalAssignmentBlock_cost (cost : Fin n → Fin n → ℝ) (σ : Assignment n)
    (tag : Fin n → T) (t : T) :
    (∑ i : {i // tag i = t}, cost i.val (σ (optimalAssignmentBlock cost σ tag t i).val)) =
      perturbedAssignmentValue (assignmentBlockCost cost σ tag t) 0 0 := by
  have hv := perturbedAssignmentValue_eq_of_optimal (assignmentBlockCost cost σ tag t)
    0 0 (firstOptimalAssignment (assignmentBlockCost cost σ tag t)) (by
      simpa only [perturbedEdgeCost_zero] using
        firstOptimalAssignment_isOptimal (assignmentBlockCost cost σ tag t))
  simp only [perturbedEdgeCost_zero] at hv
  rw [hv, ← Equiv.sum_comp (Fintype.equivFin {i // tag i = t}).symm]
  unfold assignmentCost assignmentBlockCost optimalAssignmentBlock
  simp only [Equiv.trans_apply, Equiv.apply_symm_apply]
  rfl

/-- Exact local minimizers are used on every selected block; the distinguished
remainder block is left untouched. -/
def optimizeAssignmentBlocks (cost : Fin n → Fin n → ℝ) (σ : Assignment n)
    (tag : Fin n → Option T) : Assignment n :=
  replaceAssignmentBlocks σ tag (fun t ↦ match t with
    | none => Equiv.refl _
    | some t => optimalAssignmentBlock cost σ tag (some t))

/-- Count-completion and discarded-piece edges encoded by the remainder label
are not modified by insertion of the local minimizers. -/
theorem optimizeAssignmentBlocks_none (cost : Fin n → Fin n → ℝ) (σ : Assignment n)
    (tag : Fin n → Option T) (i : Fin n) (hi : tag i = none) :
    optimizeAssignmentBlocks cost σ tag i = σ i :=
  replaceAssignmentBlocks_eq_of_fixed σ tag _ rfl i hi

/-- The same full competitor has exactly the original remainder cost plus the
sum of true finite pressure values on its retained index blocks. -/
theorem optimizeAssignmentBlocks_cost [Fintype T]
    (cost : Fin n → Fin n → ℝ) (σ : Assignment n) (tag : Fin n → Option T) :
    assignmentCost cost (optimizeAssignmentBlocks cost σ tag) =
      (∑ i : {i // tag i = none}, cost i.val (σ i.val)) +
      ∑ t, perturbedAssignmentValue (assignmentBlockCost cost σ tag (some t)) 0 0 := by
  rw [optimizeAssignmentBlocks, assignmentCost_replaceAssignmentBlocks, Fintype.sum_option]
  congr 1
  apply Finset.sum_congr rfl
  intro t _
  exact optimalAssignmentBlock_cost cost σ tag (some t)

/-- The global original pressure admits the exact retained-block upper bound,
with the original competitor's entire repair cost charged without alteration. -/
theorem assignmentValue_le_blockPressures [Fintype T]
    (cost : Fin n → Fin n → ℝ) (σ : Assignment n) (tag : Fin n → Option T) :
    perturbedAssignmentValue cost 0 0 ≤
      (∑ i : {i // tag i = none}, cost i.val (σ i.val)) +
      ∑ t, perturbedAssignmentValue (assignmentBlockCost cost σ tag (some t)) 0 0 := by
  have h := perturbedAssignmentValue_le cost 0 0 (optimizeAssignmentBlocks cost σ tag)
  simp only [perturbedEdgeCost_zero] at h
  exact h.trans_eq (optimizeAssignmentBlocks_cost cost σ tag)

end OTSelector.Reconstruction
