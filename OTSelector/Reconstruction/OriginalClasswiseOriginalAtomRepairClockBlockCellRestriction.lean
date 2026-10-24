import OTSelector.Reconstruction.OriginalClasswiseOriginalAtomRepairClockBlockRestriction

/-! Original unused block filtering preserves the literal original fine-class measure. -/
open Set Function MeasureTheory
open scoped BigOperators Classical
noncomputable section
namespace OTSelector.Reconstruction.OriginalStageClockGrid
variable (G : OriginalStageClockGrid) {μ ν : Measure ℝ}

/-- Filtering original unused source indices to this block leaves its actual
fine-cell measure unchanged. -/
theorem originalSourceClockBlock_unused_cellLaw
    {I E : Type*} [Fintype I] [MeasurableSpace E]
    (h₀ : G.clockSlabSurplus μ ν 0 = 0) (hN : G.clockSlabSurplus μ ν G.count = 0)
    (a : I → ℝ) (ha : ∀ i, G.sourceLabel (a i) < G.count)
    (U : Finset I) (b : G.ClockSlabBlock μ ν) (κ : I → Measure E)
    (i : Fin G.count) (hi : b.Contains i) :
    let S := U.filter (fun j ↦ G.sourceBlockLabel h₀ hN (a j) (ha j) = b)
    (∑ j : S, if a j.val ∈ G.sourceCell i then κ j.val else 0) =
      ∑ j : U, if a j.val ∈ G.sourceCell i then κ j.val else 0 := by
  let k := i.val-b.lower.val
  have hk : k < b.upper.val-b.lower.val := by dsimp [k,FiniteSurplusStrictBlock.Contains] at *; omega
  have he : (⟨b.lower.val+k,by have h := b.upper.isLt; omega⟩ : Fin G.count) = i := by
    apply Fin.ext
    dsimp [k,FiniteSurplusStrictBlock.Contains] at *
    omega
  have h := G.originalSourceClockBlock_unused_stageLaw h₀ hN a ha U b κ k hk
  dsimp only at h
  rw [G.originalSourceClockBlock_stageLaw h₀ hN
    (fun j : U.filter (fun j ↦ G.sourceBlockLabel h₀ hN (a j) (ha j) = b) ↦ a j.val) (fun j ↦ ha j.val) b
    (fun j ↦ (Finset.mem_filter.mp j.property).2) _ k hk,he] at h
  exact h

/-- The target statement separately preserves its genuine Ioc fine cells. -/
theorem originalTargetClockBlock_unused_cellLaw
    {I E : Type*} [Fintype I] [MeasurableSpace E]
    (h₀ : G.clockSlabSurplus μ ν 0 = 0) (hN : G.clockSlabSurplus μ ν G.count = 0)
    (a : I → ℝ) (ha : ∀ i, G.targetLabel (a i) < G.count)
    (U : Finset I) (b : G.ClockSlabBlock μ ν) (κ : I → Measure E)
    (i : Fin G.count) (hi : b.Contains i) :
    let T := U.filter (fun j ↦ G.targetBlockLabel h₀ hN (a j) (ha j) = b)
    (∑ j : T, if a j.val ∈ G.targetCell i then κ j.val else 0) =
      ∑ j : U, if a j.val ∈ G.targetCell i then κ j.val else 0 := by
  let k := i.val-b.lower.val
  have hk : k < b.upper.val-b.lower.val := by dsimp [k,FiniteSurplusStrictBlock.Contains] at *; omega
  have he : (⟨b.lower.val+k,by have h := b.upper.isLt; omega⟩ : Fin G.count) = i := by
    apply Fin.ext
    dsimp [k,FiniteSurplusStrictBlock.Contains] at *
    omega
  have h := G.originalTargetClockBlock_unused_stageLaw h₀ hN a ha U b κ k hk
  dsimp only at h
  rw [G.originalTargetClockBlock_stageLaw h₀ hN
    (fun j : U.filter (fun j ↦ G.targetBlockLabel h₀ hN (a j) (ha j) = b) ↦ a j.val) (fun j ↦ ha j.val) b
    (fun j ↦ (Finset.mem_filter.mp j.property).2) _ k hk,he] at h
  exact h

end OTSelector.Reconstruction.OriginalStageClockGrid
