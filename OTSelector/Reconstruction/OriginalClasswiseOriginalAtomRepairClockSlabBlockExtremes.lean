import OTSelector.Reconstruction.OriginalClasswiseOriginalAtomRepairClockSlabBlocks

/-! Genuine extreme classes of every positive actual half-open clock block. -/
open Set Function MeasureTheory
open scoped ENNReal BigOperators
noncomputable section
namespace OTSelector.Reconstruction.OriginalStageClockGrid
variable (G : OriginalStageClockGrid) {μ ν : Measure ℝ}

/-- The first original grid class of this actual balanced block. -/
def firstBlockClass (b : G.ClockSlabBlock μ ν) : Fin G.count :=
  ⟨b.lower.val, lt_of_lt_of_le b.consecutive.1 (Nat.le_of_lt_succ b.upper.isLt)⟩

/-- The last original grid class of this actual balanced block. -/
def lastBlockClass (b : G.ClockSlabBlock μ ν) : Fin G.count :=
  ⟨b.upper.val-1, by have h := b.consecutive.1; have h' := b.upper.isLt; omega⟩

/-- A positive monochrome balanced block has at least two actual original
classes. Singleton zero blocks are discarded without a positivity premise. -/
theorem positiveSlabBlock_has_two_classes [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hmono : ∀ i, μ (G.sourceCell i) = 0 ∨ ν (G.targetCell i) = 0)
    (b : G.ClockSlabBlock μ ν) (hb : b ∈ G.positiveSlabBlocks μ ν) :
    b.lower.val+1 < b.upper.val := by
  classical
  by_contra hn
  have he : b.upper.val = b.lower.val+1 := by have h := b.consecutive.1; omega
  have hclasses : b.classes = {G.firstBlockClass b} := by
    ext i
    simp only [FiniteSurplusStrictBlock.classes, Finset.mem_filter, Finset.mem_univ,
      true_and, Finset.mem_singleton, FiniteSurplusStrictBlock.Contains]
    constructor
    · intro hi
      apply Fin.ext
      change i.val = b.lower.val
      omega
    · intro hi
      subst i
      change b.lower.val ≤ b.lower.val ∧ b.lower.val < b.upper.val
      omega
  have hm := G.positiveSlabBlock_mass b hb
  rw [(G.block_mass_eq_class_sum b).1, (G.block_mass_eq_class_sum b).2, hclasses,
    Finset.sum_singleton] at hm
  simp only [Finset.sum_singleton] at hm
  rcases hmono (G.firstBlockClass b) with hz | hz
  · have hr : μ.real (G.sourceCell (G.firstBlockClass b)) = 0 := by simp [measureReal_def, hz]
    exact hm.1.ne' hr
  · have hr : ν.real (G.targetCell (G.firstBlockClass b)) = 0 := by simp [measureReal_def, hz]
    exact hm.1.ne' (hm.2.trans hr)

/-- The actual first source class and last target class of every positive
block have positive original law mass. These are real blockwise reserve
deletion classes, without a global support-connectedness assumption. -/
theorem positiveSlabBlock_extreme_class_masses [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hmono : ∀ i, μ (G.sourceCell i) = 0 ∨ ν (G.targetCell i) = 0)
    (hH : ∀ k ≤ G.count, 0 ≤ G.clockSlabSurplus μ ν k)
    (b : G.ClockSlabBlock μ ν) (hb : b ∈ G.positiveSlabBlocks μ ν) :
    0 < μ.real (G.sourceCell (G.firstBlockClass b)) ∧
      0 < ν.real (G.targetCell (G.lastBlockClass b)) := by
  have htwo := G.positiveSlabBlock_has_two_classes hmono b hb
  let a := fun i ↦ μ.real (G.sourceCell i)
  let c := fun i ↦ ν.real (G.targetCell i)
  have hl := b.consecutive.2.1
  have hr := b.consecutive.2.2.1
  let kl : Fin (G.count+1) := ⟨b.lower.val+1, by have h := b.upper.isLt; omega⟩
  let kr : Fin (G.count+1) := ⟨b.upper.val-1, by have h := b.upper.isLt; omega⟩
  have hpl := b.proper_prefix_pos hH (k := kl)
    (by change b.lower.val < b.lower.val+1; omega) (by exact htwo)
  have hpr := b.proper_prefix_pos hH (k := kr)
    (by change b.lower.val < b.upper.val-1; omega)
    (by change b.upper.val-1 < b.upper.val; omega)
  have has := finiteClockPrefix_succ_sub a (G.firstBlockClass b)
  have hcs := finiteClockPrefix_succ_sub c (G.firstBlockClass b)
  have hat := finiteClockPrefix_succ_sub a (G.lastBlockClass b)
  have hct := finiteClockPrefix_succ_sub c (G.lastBlockClass b)
  have hlast : (G.lastBlockClass b).val+1 = b.upper.val := by
    have h := b.consecutive.1
    change b.upper.val-1+1 = b.upper.val
    omega
  rw [hlast] at hat hct
  simp only [firstBlockClass] at has hcs
  simp only [lastBlockClass] at hat hct
  have heql : G.clockSlabSurplus μ ν (b.lower.val+1) -
      G.clockSlabSurplus μ ν b.lower.val = a (G.firstBlockClass b)-c (G.firstBlockClass b) := by
    calc
      _ = (finiteClockPrefix a (b.lower.val+1)-finiteClockPrefix a b.lower.val) -
          (finiteClockPrefix c (b.lower.val+1)-finiteClockPrefix c b.lower.val) := by
        dsimp only [clockSlabSurplus, finiteClassSurplus, a, c]
        ring
      _ = _ := by rw [has, hcs]; rfl
  have heqr : G.clockSlabSurplus μ ν b.upper.val -
      G.clockSlabSurplus μ ν (b.upper.val-1) = a (G.lastBlockClass b)-c (G.lastBlockClass b) := by
    calc
      _ = (finiteClockPrefix a b.upper.val-finiteClockPrefix a (b.upper.val-1)) -
          (finiteClockPrefix c b.upper.val-finiteClockPrefix c (b.upper.val-1)) := by
        dsimp only [clockSlabSurplus, finiteClassSurplus, a, c]
        ring
      _ = _ := by rw [hat, hct]; rfl
  have hcn : 0 ≤ c (G.firstBlockClass b) := measureReal_nonneg
  have han : 0 ≤ a (G.lastBlockClass b) := measureReal_nonneg
  rw [hl, sub_zero] at heql
  rw [hr, zero_sub] at heqr
  change 0 < G.clockSlabSurplus μ ν (b.lower.val+1) at hpl
  change 0 < G.clockSlabSurplus μ ν (b.upper.val-1) at hpr
  rw [heql] at hpl
  have hneg : a (G.lastBlockClass b)-c (G.lastBlockClass b) < 0 := by
    rw [← heqr]
    exact neg_neg_of_pos hpr
  exact ⟨by change 0 < a (G.firstBlockClass b); linarith only [hpl,hcn],
    by change 0 < c (G.lastBlockClass b); linarith only [hneg,han]⟩

end OTSelector.Reconstruction.OriginalStageClockGrid
