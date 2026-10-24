import OTSelector.Reconstruction.OriginalClasswiseOriginalAtomRepairClockBlockLocalClasses

/-! Local real stages are the original source Ico and target Ioc measure sums. -/
open Set Function MeasureTheory
open scoped ENNReal BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OTSelector.Reconstruction.OriginalStageClockGrid
variable (G : OriginalStageClockGrid) {μ ν : Measure ℝ}

/-- Relabeling a true source block changes only stage numbers, retaining the
literal original Ico atom laws. -/
theorem originalSourceClockBlock_stageLaw
    {I E : Type*} [Fintype I] [MeasurableSpace E]
    (h₀ : G.clockSlabSurplus μ ν 0 = 0) (hN : G.clockSlabSurplus μ ν G.count = 0)
    (a : I → ℝ) (ha : ∀ i, G.sourceLabel (a i) < G.count)
    (b : G.ClockSlabBlock μ ν) (hb : ∀ i, G.sourceBlockLabel h₀ hN (a i) (ha i) = b)
    (κ : I → Measure E) (k : ℕ) (hk : k < b.upper.val-b.lower.val) :
    originalAtomSmoothingClassLaw κ (fun i ↦ G.sourceClockInBlock h₀ hN (a i) (ha i)) k =
      ∑ i, if a i ∈ G.sourceCell ⟨b.lower.val+k,by have h := b.upper.isLt; omega⟩ then κ i else 0 := by
  apply Finset.sum_congr rfl
  intro i _
  simp only [G.sourceClockInBlock_eq_iff_original_cell h₀ hN (a i) (ha i) b (hb i) k hk]

/-- The target keeps its independently defined original Ioc classes. -/
theorem originalTargetClockBlock_stageLaw
    {I E : Type*} [Fintype I] [MeasurableSpace E]
    (h₀ : G.clockSlabSurplus μ ν 0 = 0) (hN : G.clockSlabSurplus μ ν G.count = 0)
    (a : I → ℝ) (ha : ∀ i, G.targetLabel (a i) < G.count)
    (b : G.ClockSlabBlock μ ν) (hb : ∀ i, G.targetBlockLabel h₀ hN (a i) (ha i) = b)
    (κ : I → Measure E) (k : ℕ) (hk : k < b.upper.val-b.lower.val) :
    originalAtomSmoothingClassLaw κ (fun i ↦ G.targetClockInBlock h₀ hN (a i) (ha i)) k =
      ∑ i, if a i ∈ G.targetCell ⟨b.lower.val+k,by have h := b.upper.isLt; omega⟩ then κ i else 0 := by
  apply Finset.sum_congr rfl
  intro i _
  simp only [G.targetClockInBlock_eq_iff_original_cell h₀ hN (a i) (ha i) b (hb i) k hk]

/-- True cell monochromaticity is precisely the no-label alternative needed
by strict RN rounding, even when one or both original arrays are empty. -/
theorem originalClockBlock_local_monochrome
    {I J : Type*}
    (h₀ : G.clockSlabSurplus μ ν 0 = 0) (hN : G.clockSlabSurplus μ ν G.count = 0)
    (a : I → ℝ) (d : J → ℝ)
    (ha : ∀ i, G.sourceLabel (a i) < G.count) (hd : ∀ j, G.targetLabel (d j) < G.count)
    (b : G.ClockSlabBlock μ ν)
    (hs : ∀ i, G.sourceBlockLabel h₀ hN (a i) (ha i) = b)
    (ht : ∀ j, G.targetBlockLabel h₀ hN (d j) (hd j) = b)
    (hmono : ∀ k : Fin G.count,
      (∀ i, a i ∉ G.sourceCell k) ∨ (∀ j, d j ∉ G.targetCell k)) :
    ∀ k, k < b.upper.val-b.lower.val →
      (∀ i, G.sourceClockInBlock h₀ hN (a i) (ha i) ≠ k) ∨
      (∀ j, G.targetClockInBlock h₀ hN (d j) (hd j) ≠ k) := by
  intro k hk
  rcases hmono ⟨b.lower.val+k,by have h := b.upper.isLt; omega⟩ with h | h
  · left
    intro i he
    exact h i ((G.sourceClockInBlock_eq_iff_original_cell h₀ hN (a i) (ha i) b (hs i) k hk).mp he)
  · right
    intro j he
    exact h j ((G.targetClockInBlock_eq_iff_original_cell h₀ hN (d j) (hd j) b (ht j) k hk).mp he)

end OTSelector.Reconstruction.OriginalStageClockGrid
