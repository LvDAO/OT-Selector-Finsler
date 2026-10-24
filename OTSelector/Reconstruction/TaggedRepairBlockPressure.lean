import OTSelector.Reconstruction.AssignmentBlockPressure

/-!
# Local pressure replacement preserves the prescribed subplan repair

Only equal-type edges outside the selected population pieces are optimized.
Every selected-piece edge and every count-completion edge stays fixed. Hence the
proved small-mass energy bound survives insertion of the local pressure optima.
-/

open Set Function MeasureTheory
open scoped BigOperators
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false

variable {T : Type*} [DecidableEq T] {n : ℕ}

/-- Retained equal-type edges outside the selected repair pieces get a local
block label. Every selected or crossing edge belongs to the fixed remainder. -/
def retainedRepairBlockTag (S : Finset T) (x y : Fin n → T) (σ : Assignment n)
    (i : Fin n) : Option T :=
  if x i = y (σ i) ∧ x i ∉ S then some (x i) else none

/-- A retained block has the same original type on both endpoints and excludes
the prescribed repair pieces. -/
theorem retainedRepairBlockTag_eq_some_iff
    (S : Finset T) (x y : Fin n → T) (σ : Assignment n) (i : Fin n) (t : T) :
    retainedRepairBlockTag S x y σ i = some t ↔ x i = t ∧ y (σ i) = t ∧ t ∉ S := by
  unfold retainedRepairBlockTag
  split_ifs with h
  · simp only [Option.some.injEq]
    constructor
    · intro hi
      exact ⟨hi, h.1.symm.trans hi, hi ▸ h.2⟩
    · exact fun hi ↦ hi.1
  · simp only [false_iff, not_and]
    intro hx hy hnot
    exact h ⟨hx.trans hy.symm, hx ▸ hnot⟩

/-- A source edge touching a selected population type is always in the fixed
remainder block of the original full competitor. -/
theorem retainedRepairBlockTag_none_of_selected
    (S : Finset T) (x y : Fin n → T) (σ : Assignment n) (i : Fin n)
    (hi : x i ∈ S ∨ y (σ i) ∈ S) : retainedRepairBlockTag S x y σ i = none := by
  unfold retainedRepairBlockTag
  apply ite_eq_right
  rintro ⟨heq, hn⟩
  exact hn (hi.elim id (fun h ↦ heq ▸ h))

/-- Local exact pressure optimization retains every edge incident to the
selected deterministic population pieces, with its original physical endpoints. -/
theorem optimizeRepairBlocks_eq_of_selected
    (S : Finset T) (x y : Fin n → T) (σ : Assignment n)
    (objective : Fin n → Fin n → ℝ) (i : Fin n) (hi : x i ∈ S ∨ y (σ i) ∈ S) :
    optimizeAssignmentBlocks objective σ (retainedRepairBlockTag S x y σ) i = σ i :=
  optimizeAssignmentBlocks_none objective σ _ i
    (retainedRepairBlockTag_none_of_selected S x y σ i hi)

/-- Any replaced edge has a target taken from the same original retained source
block. This is a statement about the actual old partner indices. -/
theorem optimizeAssignmentBlocks_target_in_same_block
    (cost : Fin n → Fin n → ℝ) (σ : Assignment n) (tag : Fin n → Option T) (i : Fin n) :
    ∃ j : Fin n, tag j = tag i ∧ optimizeAssignmentBlocks cost σ tag i = σ j := by
  let θ : ∀ t, Equiv.Perm {j // tag j = t} := fun t ↦ match t with
    | none => Equiv.refl _
    | some t => optimalAssignmentBlock cost σ tag (some t)
  exact ⟨(θ (tag i) ⟨i, rfl⟩).val, (θ (tag i) ⟨i, rfl⟩).property, rfl⟩

/-- Inserting arbitrary local pressure optima leaves the entire selected-type
energy exactly unchanged, for any other physical cost or probe being measured. -/
theorem attributedTypesEnergy_optimizeRepairBlocks
    {q : ℕ} (S : Finset T) (x y : Fin n → T × DyadicUnitCube q) (σ : Assignment n)
    (objective cost : Fin n → Fin n → ℝ) :
    attributedTypesEnergy S x y cost
      (optimizeAssignmentBlocks objective σ
        (retainedRepairBlockTag S (fun i ↦ (x i).1) (fun i ↦ (y i).1) σ)) =
      attributedTypesEnergy S x y cost σ := by
  let tag := retainedRepairBlockTag S (fun i ↦ (x i).1) (fun i ↦ (y i).1) σ
  unfold attributedTypesEnergy attributedTypeEnergy
  apply Finset.sum_congr rfl
  intro t ht
  apply Finset.sum_congr rfl
  intro i _
  cases hi : tag i with
  | none =>
    rw [show optimizeAssignmentBlocks objective σ tag i = σ i from
      optimizeAssignmentBlocks_none objective σ tag i hi]
  | some k =>
    have hx := (retainedRepairBlockTag_eq_some_iff S (fun i ↦ (x i).1)
      (fun i ↦ (y i).1) σ i k).mp hi
    obtain ⟨j, hj, heq⟩ := optimizeAssignmentBlocks_target_in_same_block objective σ tag i
    have hjk : tag j = some k := hj.trans hi
    have hy := (retainedRepairBlockTag_eq_some_iff S (fun i ↦ (x i).1)
      (fun i ↦ (y i).1) σ j k).mp hjk
    have hkt : k ≠ t := fun h ↦ hx.2.2 (h ▸ ht)
    simp only [tag] at heq
    simp only [heq, typeTouchIndicator, hx.1, hx.2.1, hy.2.1, hkt, or_self,
      ↓reduceIte, zero_mul]

end OTSelector.Reconstruction
