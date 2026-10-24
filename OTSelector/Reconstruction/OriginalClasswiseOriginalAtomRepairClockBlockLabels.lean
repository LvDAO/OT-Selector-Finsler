import OTSelector.Reconstruction.OriginalClasswiseOriginalAtomRepairClockSlabBlocks
import OTSelector.Reconstruction.OriginalStageClockSlabsLabels

/-! Ordered actual balanced-block labels preserve original scalar-clock legality. -/
open Set Function MeasureTheory
noncomputable section
namespace OTSelector.Reconstruction

/-- Two consecutive zero-cut blocks with the same lower cut are identical. -/
theorem FiniteSurplusStrictBlock.lower_injective {H : ℕ → ℝ} {N : ℕ} :
    Injective (FiniteSurplusStrictBlock.lower (H := H) (N := N)) := by
  intro b c hbc
  have hu : b.upper = c.upper := by
    apply le_antisymm
    · by_contra hn
      have hlt : c.upper < b.upper := lt_of_not_ge hn
      exact b.consecutive.2.2.2 c.upper (hbc ▸ c.consecutive.1) hlt c.consecutive.2.2.1
    · by_contra hn
      have hlt : b.upper < c.upper := lt_of_not_ge hn
      exact c.consecutive.2.2.2 b.upper (hbc ▸ b.consecutive.1) hlt b.consecutive.2.2.1
  apply Subtype.ext
  exact Prod.ext hbc hu

/-- The actual clock-block order is its genuine lower-cut order. -/
abbrev FiniteSurplusStrictBlock.linearOrder (H : ℕ → ℝ) (N : ℕ) :
    LinearOrder (FiniteSurplusStrictBlock H N) :=
  LinearOrder.lift' FiniteSurplusStrictBlock.lower FiniteSurplusStrictBlock.lower_injective

/-- Distinct ordered actual blocks have disjoint ordered class intervals. -/
theorem FiniteSurplusStrictBlock.upper_le_lower_of_lower_lt {H : ℕ → ℝ} {N : ℕ}
    (b c : FiniteSurplusStrictBlock H N) (hbc : b.lower < c.lower) : b.upper ≤ c.lower := by
  by_contra hn
  exact b.consecutive.2.2.2 c.lower hbc (lt_of_not_ge hn) c.consecutive.2.1

namespace OriginalStageClockGrid
variable (G : OriginalStageClockGrid) {μ ν : Measure ℝ}

/-- Each actual fine class belongs to its unique balanced clock block. -/
def blockForClass (h₀ : G.clockSlabSurplus μ ν 0 = 0)
    (hN : G.clockSlabSurplus μ ν G.count = 0) (i : Fin G.count) : G.ClockSlabBlock μ ν :=
  Classical.choose (exists_unique_finiteSurplusStrictBlock _ G.count h₀ hN i)

theorem blockForClass_contains (h₀ : G.clockSlabSurplus μ ν 0 = 0)
    (hN : G.clockSlabSurplus μ ν G.count = 0) (i : Fin G.count) :
    (G.blockForClass h₀ hN i).Contains i :=
  (Classical.choose_spec (exists_unique_finiteSurplusStrictBlock _ G.count h₀ hN i)).1

theorem blockForClass_lower_mono (h₀ : G.clockSlabSurplus μ ν 0 = 0)
    (hN : G.clockSlabSurplus μ ν G.count = 0) {i j : Fin G.count} (hij : i ≤ j) :
    (G.blockForClass h₀ hN i).lower ≤ (G.blockForClass h₀ hN j).lower := by
  have hi := G.blockForClass_contains h₀ hN i
  have hj := G.blockForClass_contains h₀ hN j
  by_contra hn
  have hc := FiniteSurplusStrictBlock.upper_le_lower_of_lower_lt
    (G.blockForClass h₀ hN j) (G.blockForClass h₀ hN i) (lt_of_not_ge hn)
  have hcv : (G.blockForClass h₀ hN j).upper.val ≤ (G.blockForClass h₀ hN i).lower.val := hc
  have hijv : i.val ≤ j.val := hij
  dsimp only [FiniteSurplusStrictBlock.Contains] at hi hj
  omega

/-- Actual source and target clocks get their own half-open fine-class label
before being assigned the unique real balanced block. -/
def sourceBlockLabel (h₀ : G.clockSlabSurplus μ ν 0 = 0)
    (hN : G.clockSlabSurplus μ ν G.count = 0) (a : ℝ) (ha : G.sourceLabel a < G.count) :
    G.ClockSlabBlock μ ν := G.blockForClass h₀ hN ⟨_,ha⟩

def targetBlockLabel (h₀ : G.clockSlabSurplus μ ν 0 = 0)
    (hN : G.clockSlabSurplus μ ν G.count = 0) (a : ℝ) (ha : G.targetLabel a < G.count) :
    G.ClockSlabBlock μ ν := G.blockForClass h₀ hN ⟨_,ha⟩

theorem original_clock_lt_implies_block_forward
    (h₀ : G.clockSlabSurplus μ ν 0 = 0) (hN : G.clockSlabSurplus μ ν G.count = 0)
    {a b : ℝ} (ha : G.sourceLabel a < G.count) (hb : G.targetLabel b < G.count) (hab : a < b) :
    (G.sourceBlockLabel h₀ hN a ha).lower ≤ (G.targetBlockLabel h₀ hN b hb).lower := by
  have hsa := (G.sourceLabel_eq_iff a ⟨_,ha⟩).mp rfl
  have htb := (G.targetLabel_eq_iff b ⟨_,hb⟩).mp rfl
  apply G.blockForClass_lower_mono h₀ hN
  change G.sourceLabel a ≤ G.targetLabel b
  by_contra hn
  have hij : G.targetLabel b + 1 ≤ G.sourceLabel a := by omega
  have hc := G.strictMono.monotone hij
  exact (not_lt_of_ge (htb.2.trans (hc.trans hsa.1))) hab

/-- Every strict forward pair of actual block labels is a legal original
clock pair. This supplies cross-block completeness for the real graph. -/
theorem block_strict_forward_implies_original_clock_lt
    (h₀ : G.clockSlabSurplus μ ν 0 = 0) (hN : G.clockSlabSurplus μ ν G.count = 0)
    {a b : ℝ} (ha : G.sourceLabel a < G.count) (hb : G.targetLabel b < G.count)
    (hblock : (G.sourceBlockLabel h₀ hN a ha).lower < (G.targetBlockLabel h₀ hN b hb).lower) : a < b := by
  have hc := FiniteSurplusStrictBlock.upper_le_lower_of_lower_lt _ _ hblock
  have hsa := G.blockForClass_contains h₀ hN (⟨_,ha⟩ : Fin G.count)
  have htb := G.blockForClass_contains h₀ hN (⟨_,hb⟩ : Fin G.count)
  have hcv : (G.blockForClass h₀ hN (⟨_,ha⟩ : Fin G.count)).upper.val ≤
      (G.blockForClass h₀ hN (⟨_,hb⟩ : Fin G.count)).lower.val := hc
  have hij : G.sourceLabel a < G.targetLabel b := hsa.2.trans_le (hcv.trans htb.1)
  exact G.clock_lt_of_labels ha hb hij

end OriginalStageClockGrid
end OTSelector.Reconstruction
