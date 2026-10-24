import OTSelector.Reconstruction.OriginalClasswiseOriginalAtomRepairClockBlockStageLaws

/-! Restricting unchanged unused labels to their actual balanced block preserves each stage law. -/
open Set Function MeasureTheory
open scoped ENNReal BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OTSelector.Reconstruction.OriginalStageClockGrid
variable (G : OriginalStageClockGrid) {μ ν : Measure ℝ}

/-- A source stage inside its own actual block needs no contribution from
another block, and retains the original unused atom indices. -/
theorem originalSourceClockBlock_unused_stageLaw
    {I E : Type*} [Fintype I] [MeasurableSpace E]
    (h₀ : G.clockSlabSurplus μ ν 0 = 0) (hN : G.clockSlabSurplus μ ν G.count = 0)
    (a : I → ℝ) (ha : ∀ i, G.sourceLabel (a i) < G.count)
    (U : Finset I) (b : G.ClockSlabBlock μ ν) (κ : I → Measure E)
    (k : ℕ) (hk : k < b.upper.val-b.lower.val) :
    let S := U.filter (fun i ↦ G.sourceBlockLabel h₀ hN (a i) (ha i) = b)
    originalAtomSmoothingClassLaw (fun i : S ↦ κ i.val)
      (fun i ↦ G.sourceClockInBlock h₀ hN (a i.val) (ha i.val)) k =
      ∑ i : U, if a i.val ∈ G.sourceCell ⟨b.lower.val+k,by have h := b.upper.isLt; omega⟩
        then κ i.val else 0 := by
  let S := U.filter (fun i ↦ G.sourceBlockLabel h₀ hN (a i) (ha i) = b)
  change originalAtomSmoothingClassLaw (fun i : S ↦ κ i.val) _ _ = _
  rw [G.originalSourceClockBlock_stageLaw h₀ hN (fun i : S ↦ a i.val)
    (fun i ↦ ha i.val) b (fun i ↦ (Finset.mem_filter.mp i.property).2) (fun i ↦ κ i.val) k hk]
  rw [Finset.sum_coe_sort S (fun i ↦ if a i ∈ G.sourceCell
    ⟨b.lower.val+k,by have h := b.upper.isLt; omega⟩ then κ i else 0),
    Finset.sum_coe_sort U (fun i ↦ if a i ∈ G.sourceCell
    ⟨b.lower.val+k,by have h := b.upper.isLt; omega⟩ then κ i else 0)]
  change (∑ i ∈ U.filter _, _) = _
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : a i ∈ G.sourceCell ⟨b.lower.val+k,by have h := b.upper.isLt; omega⟩
  · have hl := (G.sourceLabel_eq_iff (a i)
        ⟨b.lower.val+k,by have h := b.upper.isLt; omega⟩).mpr hi
    have hb : G.sourceBlockLabel h₀ hN (a i) (ha i) = b := by
      apply (G.blockForClass_eq_iff h₀ hN ⟨_,ha i⟩ b).mpr
      change b.lower.val ≤ G.sourceLabel (a i) ∧ G.sourceLabel (a i) < b.upper.val
      dsimp only at hl
      omega
    simp only [hi, hb, ite_true]
  · simp only [hi, ite_false, ite_self]

/-- Targets separately keep the original Ioc convention under the same restriction. -/
theorem originalTargetClockBlock_unused_stageLaw
    {I E : Type*} [Fintype I] [MeasurableSpace E]
    (h₀ : G.clockSlabSurplus μ ν 0 = 0) (hN : G.clockSlabSurplus μ ν G.count = 0)
    (a : I → ℝ) (ha : ∀ i, G.targetLabel (a i) < G.count)
    (U : Finset I) (b : G.ClockSlabBlock μ ν) (κ : I → Measure E)
    (k : ℕ) (hk : k < b.upper.val-b.lower.val) :
    let T := U.filter (fun i ↦ G.targetBlockLabel h₀ hN (a i) (ha i) = b)
    originalAtomSmoothingClassLaw (fun i : T ↦ κ i.val)
      (fun i ↦ G.targetClockInBlock h₀ hN (a i.val) (ha i.val)) k =
      ∑ i : U, if a i.val ∈ G.targetCell ⟨b.lower.val+k,by have h := b.upper.isLt; omega⟩
        then κ i.val else 0 := by
  let T := U.filter (fun i ↦ G.targetBlockLabel h₀ hN (a i) (ha i) = b)
  change originalAtomSmoothingClassLaw (fun i : T ↦ κ i.val) _ _ = _
  rw [G.originalTargetClockBlock_stageLaw h₀ hN (fun i : T ↦ a i.val)
    (fun i ↦ ha i.val) b (fun i ↦ (Finset.mem_filter.mp i.property).2) (fun i ↦ κ i.val) k hk]
  rw [Finset.sum_coe_sort T (fun i ↦ if a i ∈ G.targetCell
    ⟨b.lower.val+k,by have h := b.upper.isLt; omega⟩ then κ i else 0),
    Finset.sum_coe_sort U (fun i ↦ if a i ∈ G.targetCell
    ⟨b.lower.val+k,by have h := b.upper.isLt; omega⟩ then κ i else 0)]
  change (∑ i ∈ U.filter _, _) = _
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : a i ∈ G.targetCell ⟨b.lower.val+k,by have h := b.upper.isLt; omega⟩
  · have hl := (G.targetLabel_eq_iff (a i)
        ⟨b.lower.val+k,by have h := b.upper.isLt; omega⟩).mpr hi
    have hb : G.targetBlockLabel h₀ hN (a i) (ha i) = b := by
      apply (G.blockForClass_eq_iff h₀ hN ⟨_,ha i⟩ b).mpr
      change b.lower.val ≤ G.targetLabel (a i) ∧ G.targetLabel (a i) < b.upper.val
      dsimp only at hl
      omega
    simp only [hi, hb, ite_true]
  · simp only [hi, ite_false, ite_self]

end OTSelector.Reconstruction.OriginalStageClockGrid
