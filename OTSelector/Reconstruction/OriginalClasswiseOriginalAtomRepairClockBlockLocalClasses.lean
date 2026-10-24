import OTSelector.Reconstruction.OriginalClasswiseOriginalAtomRepairClockBlockLabels
import OTSelector.Probability.AtomicSmoothingClassLaws

/-! Local stage numbers retain the exact original half-open clock classes. -/
open Set Function MeasureTheory
open scoped BigOperators Classical
noncomputable section
namespace OTSelector.Reconstruction.OriginalStageClockGrid
variable (G : OriginalStageClockGrid) {μ ν : Measure ℝ}

theorem blockForClass_eq_iff (h₀ : G.clockSlabSurplus μ ν 0 = 0)
    (hN : G.clockSlabSurplus μ ν G.count = 0) (i : Fin G.count) (b : G.ClockSlabBlock μ ν) :
    G.blockForClass h₀ hN i = b ↔ b.Contains i := by
  constructor
  · intro he
    rw [← he]
    exact G.blockForClass_contains h₀ hN i
  · intro hb
    exact (exists_unique_finiteSurplusStrictBlock _ _ h₀ hN i).unique
      (G.blockForClass_contains h₀ hN i) hb

/-- Stage numbers are measured from this original atom's own real block. -/
def sourceClockInBlock (h₀ : G.clockSlabSurplus μ ν 0 = 0)
    (hN : G.clockSlabSurplus μ ν G.count = 0) (a : ℝ) (ha : G.sourceLabel a < G.count) : ℕ :=
  G.sourceLabel a - (G.sourceBlockLabel h₀ hN a ha).lower.val

def targetClockInBlock (h₀ : G.clockSlabSurplus μ ν 0 = 0)
    (hN : G.clockSlabSurplus μ ν G.count = 0) (a : ℝ) (ha : G.targetLabel a < G.count) : ℕ :=
  G.targetLabel a - (G.targetBlockLabel h₀ hN a ha).lower.val

theorem sourceClockInBlock_lt (h₀ : G.clockSlabSurplus μ ν 0 = 0)
    (hN : G.clockSlabSurplus μ ν G.count = 0) (a : ℝ) (ha : G.sourceLabel a < G.count) :
    G.sourceClockInBlock h₀ hN a ha < (G.sourceBlockLabel h₀ hN a ha).upper.val -
      (G.sourceBlockLabel h₀ hN a ha).lower.val := by
  have h := G.blockForClass_contains h₀ hN (⟨_,ha⟩ : Fin G.count)
  change (G.sourceBlockLabel h₀ hN a ha).lower.val ≤ G.sourceLabel a ∧
    G.sourceLabel a < (G.sourceBlockLabel h₀ hN a ha).upper.val at h
  unfold sourceClockInBlock
  omega

theorem targetClockInBlock_lt (h₀ : G.clockSlabSurplus μ ν 0 = 0)
    (hN : G.clockSlabSurplus μ ν G.count = 0) (a : ℝ) (ha : G.targetLabel a < G.count) :
    G.targetClockInBlock h₀ hN a ha < (G.targetBlockLabel h₀ hN a ha).upper.val -
      (G.targetBlockLabel h₀ hN a ha).lower.val := by
  have h := G.blockForClass_contains h₀ hN (⟨_,ha⟩ : Fin G.count)
  change (G.targetBlockLabel h₀ hN a ha).lower.val ≤ G.targetLabel a ∧
    G.targetLabel a < (G.targetBlockLabel h₀ hN a ha).upper.val at h
  unfold targetClockInBlock
  omega

/-- The local source stage remains the original Ico class, exactly. -/
theorem sourceClockInBlock_eq_iff_original_cell
    (h₀ : G.clockSlabSurplus μ ν 0 = 0) (hN : G.clockSlabSurplus μ ν G.count = 0)
    (a : ℝ) (ha : G.sourceLabel a < G.count) (b : G.ClockSlabBlock μ ν)
    (hab : G.sourceBlockLabel h₀ hN a ha = b) (k : ℕ)
    (hk : k < b.upper.val-b.lower.val) :
    G.sourceClockInBlock h₀ hN a ha = k ↔
      a ∈ G.sourceCell ⟨b.lower.val+k,by have h := b.upper.isLt; omega⟩ := by
  have hc := (G.blockForClass_eq_iff h₀ hN (⟨_,ha⟩ : Fin G.count) b).mp hab
  rw [← G.sourceLabel_eq_iff]
  unfold sourceClockInBlock
  rw [hab]
  change b.lower.val ≤ G.sourceLabel a ∧ G.sourceLabel a < b.upper.val at hc
  dsimp only
  omega

/-- The local target stage separately remains the original Ioc class. -/
theorem targetClockInBlock_eq_iff_original_cell
    (h₀ : G.clockSlabSurplus μ ν 0 = 0) (hN : G.clockSlabSurplus μ ν G.count = 0)
    (a : ℝ) (ha : G.targetLabel a < G.count) (b : G.ClockSlabBlock μ ν)
    (hab : G.targetBlockLabel h₀ hN a ha = b) (k : ℕ)
    (hk : k < b.upper.val-b.lower.val) :
    G.targetClockInBlock h₀ hN a ha = k ↔
      a ∈ G.targetCell ⟨b.lower.val+k,by have h := b.upper.isLt; omega⟩ := by
  have hc := (G.blockForClass_eq_iff h₀ hN (⟨_,ha⟩ : Fin G.count) b).mp hab
  rw [← G.targetLabel_eq_iff]
  unfold targetClockInBlock
  rw [hab]
  change b.lower.val ≤ G.targetLabel a ∧ G.targetLabel a < b.upper.val at hc
  dsimp only
  omega

/-- Local strict stage order in one real block is legal original clock order. -/
theorem original_clock_lt_of_local_block_order
    (h₀ : G.clockSlabSurplus μ ν 0 = 0) (hN : G.clockSlabSurplus μ ν G.count = 0)
    {a b : ℝ} (ha : G.sourceLabel a < G.count) (hb : G.targetLabel b < G.count)
    (hsame : G.sourceBlockLabel h₀ hN a ha = G.targetBlockLabel h₀ hN b hb)
    (hlocal : G.sourceClockInBlock h₀ hN a ha < G.targetClockInBlock h₀ hN b hb) : a < b := by
  apply G.clock_lt_of_labels ha hb
  unfold sourceClockInBlock targetClockInBlock at hlocal
  rw [hsame] at hlocal
  omega

end OTSelector.Reconstruction.OriginalStageClockGrid
