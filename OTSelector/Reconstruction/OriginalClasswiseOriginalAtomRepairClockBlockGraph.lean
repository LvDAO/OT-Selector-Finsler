import OTSelector.Reconstruction.OriginalClasswiseOriginalAtomRepairClockBlockLocalClasses
import OTSelector.Reconstruction.MarkedStationaryValueLegalTypes

/-! The actual scalar-clock graph and the genuine balanced-block labels agree. -/
open Set Function MeasureTheory
open scoped Classical
noncomputable section
namespace OTSelector.Reconstruction.OriginalStageClockGrid
variable (G : OriginalStageClockGrid) {μ ν : Measure ℝ}

/-- A source's true block label is exactly membership in the original Ico block union. -/
theorem sourceBlockLabel_eq_iff_mem
    (h₀ : G.clockSlabSurplus μ ν 0 = 0) (hN : G.clockSlabSurplus μ ν G.count = 0)
    (a : ℝ) (ha : G.sourceLabel a < G.count) (b : G.ClockSlabBlock μ ν) :
    G.sourceBlockLabel h₀ hN a ha = b ↔ a ∈ G.sourceBlockCell μ ν b := by
  rw [G.mem_sourceBlockCell_iff b ((G.sourceLabel_eq_iff a ⟨_,ha⟩).mp rfl)]
  exact G.blockForClass_eq_iff h₀ hN ⟨_,ha⟩ b

/-- Target membership keeps the separate original Ioc block union. -/
theorem targetBlockLabel_eq_iff_mem
    (h₀ : G.clockSlabSurplus μ ν 0 = 0) (hN : G.clockSlabSurplus μ ν G.count = 0)
    (a : ℝ) (ha : G.targetLabel a < G.count) (b : G.ClockSlabBlock μ ν) :
    G.targetBlockLabel h₀ hN a ha = b ↔ a ∈ G.targetBlockCell μ ν b := by
  rw [G.mem_targetBlockCell_iff b ((G.targetLabel_eq_iff a ⟨_,ha⟩).mp rfl)]
  exact G.blockForClass_eq_iff h₀ hN ⟨_,ha⟩ b

/-- Original strict clock edges move forward through the real blocks, and
every strict forward block pair is an edge of the unchanged original graph. -/
theorem originalClockBlock_graph_forward_complete
    {m n : ℕ}
    (h₀ : G.clockSlabSurplus μ ν 0 = 0) (hN : G.clockSlabSurplus μ ν G.count = 0)
    (a : Fin m → ℝ) (d : Fin n → ℝ)
    (ha : ∀ i, G.sourceLabel (a i) < G.count) (hd : ∀ j, G.targetLabel (d j) < G.count) :
    let order := FiniteSurplusStrictBlock.linearOrder (G.clockSlabSurplus μ ν) G.count
    letI : LE (G.ClockSlabBlock μ ν) := order.toLE
    letI : LT (G.ClockSlabBlock μ ν) := order.toLT
    (∀ i j, (i,j) ∈ scalarClockLegalGraph a d →
      G.sourceBlockLabel h₀ hN (a i) (ha i) ≤ G.targetBlockLabel h₀ hN (d j) (hd j)) ∧
    (∀ i j, G.sourceBlockLabel h₀ hN (a i) (ha i) < G.targetBlockLabel h₀ hN (d j) (hd j) →
      (i,j) ∈ scalarClockLegalGraph a d) := by
  constructor
  · intro i j hij
    change (G.sourceBlockLabel h₀ hN (a i) (ha i)).lower ≤
      (G.targetBlockLabel h₀ hN (d j) (hd j)).lower
    apply G.original_clock_lt_implies_block_forward h₀ hN (ha i) (hd j)
    exact (Finset.mem_filter.mp hij).2
  · intro i j hij
    change (G.sourceBlockLabel h₀ hN (a i) (ha i)).lower <
      (G.targetBlockLabel h₀ hN (d j) (hd j)).lower at hij
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      G.block_strict_forward_implies_original_clock_lt h₀ hN (ha i) (hd j) hij⟩

end OTSelector.Reconstruction.OriginalStageClockGrid
