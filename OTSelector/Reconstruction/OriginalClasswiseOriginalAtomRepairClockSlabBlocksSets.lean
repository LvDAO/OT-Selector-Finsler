import OTSelector.Reconstruction.OriginalClasswiseOriginalAtomRepairClockSlabBlocksFlow

/-! Actual source and target block unions, including true zero-mass blocks. -/

open Set Function MeasureTheory
open scoped BigOperators ENNReal
noncomputable section
namespace OTSelector.Reconstruction

private theorem block_union_mem_iff {N : ℕ} {H : ℕ → ℝ}
    (cell : Fin N → Set ℝ) (hd : Pairwise (Disjoint on cell))
    (b : FiniteSurplusStrictBlock H N) {i : Fin N} {x : ℝ} (hx : x ∈ cell i) :
    (x ∈ ⋃ j ∈ b.classes, cell j) ↔ b.Contains i := by
  classical
  constructor
  · intro hb
    obtain ⟨j, hj⟩ := mem_iUnion.mp hb
    obtain ⟨hj, hxj⟩ := mem_iUnion.mp hj
    have hij : i = j := by
      by_contra h
      exact disjoint_left.mp (hd h) hx hxj
    subst j
    exact (Finset.mem_filter.mp hj).2
  · intro hi
    exact mem_iUnion.mpr ⟨i, mem_iUnion.mpr
      ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩, hx⟩⟩

private theorem block_unions_disjoint {N : ℕ} {H : ℕ → ℝ}
    (h₀ : H 0 = 0) (hN : H N = 0) (cell : Fin N → Set ℝ)
    (hd : Pairwise (Disjoint on cell)) :
    Pairwise (fun b c : FiniteSurplusStrictBlock H N ↦
      Disjoint (⋃ i ∈ b.classes, cell i) (⋃ i ∈ c.classes, cell i)) := by
  intro b c hbc
  apply disjoint_left.mpr
  intro x hb hc
  obtain ⟨i, hi⟩ := mem_iUnion.mp hb
  obtain ⟨_, hxi⟩ := mem_iUnion.mp hi
  have hbi := (block_union_mem_iff cell hd b hxi).mp hb
  have hci := (block_union_mem_iff cell hd c hxi).mp hc
  exact hbc ((exists_unique_finiteSurplusStrictBlock H N h₀ hN i).unique hbi hci)

namespace OriginalStageClockGrid
variable (G : OriginalStageClockGrid) {μ ν : Measure ℝ}

/-- Source blocks remain unions of the actual original Ico cells. -/
def sourceBlockCell (μ ν : Measure ℝ) (b : G.ClockSlabBlock μ ν) : Set ℝ :=
  ⋃ i ∈ b.classes, G.sourceCell i

/-- Target blocks separately remain unions of the actual original Ioc cells. -/
def targetBlockCell (μ ν : Measure ℝ) (b : G.ClockSlabBlock μ ν) : Set ℝ :=
  ⋃ i ∈ b.classes, G.targetCell i

theorem blockCells_measurable (b : G.ClockSlabBlock μ ν) :
    MeasurableSet (G.sourceBlockCell μ ν b) ∧ MeasurableSet (G.targetBlockCell μ ν b) :=
  ⟨MeasurableSet.iUnion fun _ ↦ MeasurableSet.iUnion fun _ ↦ measurableSet_Ico,
    MeasurableSet.iUnion fun _ ↦ MeasurableSet.iUnion fun _ ↦ measurableSet_Ioc⟩

theorem mem_sourceBlockCell_iff (b : G.ClockSlabBlock μ ν) {i : Fin G.count} {x : ℝ}
    (hx : x ∈ G.sourceCell i) : x ∈ G.sourceBlockCell μ ν b ↔ b.Contains i :=
  block_union_mem_iff G.sourceCell G.source_disjoint b hx

theorem mem_targetBlockCell_iff (b : G.ClockSlabBlock μ ν) {i : Fin G.count} {x : ℝ}
    (hx : x ∈ G.targetCell i) : x ∈ G.targetBlockCell μ ν b ↔ b.Contains i :=
  block_union_mem_iff G.targetCell G.target_disjoint b hx

/-- Each color retains its actual disjoint block partition. -/
theorem blockCells_disjoint (h₀ : G.clockSlabSurplus μ ν 0 = 0)
    (hN : G.clockSlabSurplus μ ν G.count = 0) :
    Pairwise (fun b c : G.ClockSlabBlock μ ν ↦ Disjoint (G.sourceBlockCell μ ν b) (G.sourceBlockCell μ ν c)) ∧
      Pairwise (fun b c : G.ClockSlabBlock μ ν ↦ Disjoint (G.targetBlockCell μ ν b) (G.targetBlockCell μ ν c)) :=
  ⟨block_unions_disjoint h₀ hN G.sourceCell G.source_disjoint,
    block_unions_disjoint h₀ hN G.targetCell G.target_disjoint⟩

/-- Original source and target AE coverage passes to their distinct actual block unions. -/
theorem blockCells_ae_cover (h₀ : G.clockSlabSurplus μ ν 0 = 0)
    (hN : G.clockSlabSurplus μ ν G.count = 0)
    (hs : ∀ᵐ x ∂μ, x ∈ ⋃ i, G.sourceCell i) (ht : ∀ᵐ y ∂ν, y ∈ ⋃ j, G.targetCell j) :
    (∀ᵐ x ∂μ, x ∈ ⋃ b : G.ClockSlabBlock μ ν, G.sourceBlockCell μ ν b) ∧
      (∀ᵐ y ∂ν, y ∈ ⋃ b : G.ClockSlabBlock μ ν, G.targetBlockCell μ ν b) := by
  constructor
  · filter_upwards [hs] with x hx
    obtain ⟨i, hi⟩ := mem_iUnion.mp hx
    obtain ⟨b, hb, _⟩ := exists_unique_finiteSurplusStrictBlock _ G.count h₀ hN i
    exact mem_iUnion.mpr ⟨b, (G.mem_sourceBlockCell_iff b hi).mpr hb⟩
  · filter_upwards [ht] with x hx
    obtain ⟨i, hi⟩ := mem_iUnion.mp hx
    obtain ⟨b, hb, _⟩ := exists_unique_finiteSurplusStrictBlock _ G.count h₀ hN i
    exact mem_iUnion.mpr ⟨b, (G.mem_targetBlockCell_iff b hi).mpr hb⟩

/-- Block masses are sums of unchanged source and target slab masses. -/
theorem block_mass_eq_class_sum [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (b : G.ClockSlabBlock μ ν) :
    μ.real (G.sourceBlockCell μ ν b) = ∑ i ∈ b.classes, μ.real (G.sourceCell i) ∧
      ν.real (G.targetBlockCell μ ν b) = ∑ i ∈ b.classes, ν.real (G.targetCell i) := by
  constructor
  · exact measureReal_biUnion_finset (fun _ _ _ _ h ↦ G.source_disjoint h)
      (fun _ _ ↦ measurableSet_Ico) (fun _ _ ↦ measure_ne_top μ _)
  · exact measureReal_biUnion_finset (fun _ _ _ _ h ↦ G.target_disjoint h)
      (fun _ _ ↦ measurableSet_Ioc) (fun _ _ ↦ measure_ne_top ν _)

/-- Every actual block is balanced, including blocks of zero mass. -/
theorem block_mass_balance [IsFiniteMeasure μ] [IsFiniteMeasure ν] (b : G.ClockSlabBlock μ ν) :
    μ.real (G.sourceBlockCell μ ν b) = ν.real (G.targetBlockCell μ ν b) := by
  rw [(G.block_mass_eq_class_sum b).1, (G.block_mass_eq_class_sum b).2]
  exact b.mass_balance (fun i ↦ μ.real (G.sourceCell i)) (fun i ↦ ν.real (G.targetCell i))

/-- Only blocks whose actual original source mass is positive are retained. -/
def positiveSlabBlocks (μ ν : Measure ℝ) : Finset (G.ClockSlabBlock μ ν) := by
  classical
  exact Finset.univ.filter (fun b ↦ 0 < μ.real (G.sourceBlockCell μ ν b))

theorem positiveSlabBlock_mass [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (b : G.ClockSlabBlock μ ν) (hb : b ∈ G.positiveSlabBlocks μ ν) :
    0 < μ.real (G.sourceBlockCell μ ν b) ∧
      μ.real (G.sourceBlockCell μ ν b) = ν.real (G.targetBlockCell μ ν b) := by
  classical
  exact ⟨(Finset.mem_filter.mp hb).2, G.block_mass_balance b⟩

/-- A discarded zero block has genuinely zero original restricted laws of both colors. -/
theorem zeroSlabBlock_restrict [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (b : G.ClockSlabBlock μ ν) (hb : b ∉ G.positiveSlabBlocks μ ν) :
    μ.restrict (G.sourceBlockCell μ ν b) = 0 ∧ ν.restrict (G.targetBlockCell μ ν b) = 0 := by
  classical
  have hn : ¬ 0 < μ.real (G.sourceBlockCell μ ν b) := by
    simpa only [positiveSlabBlocks, Finset.mem_filter, Finset.mem_univ, true_and] using hb
  have hz : μ.real (G.sourceBlockCell μ ν b) = 0 := le_antisymm (le_of_not_gt hn) measureReal_nonneg
  exact ⟨Measure.restrict_eq_zero.mpr ((measureReal_eq_zero_iff (measure_ne_top μ _)).mp hz),
    Measure.restrict_eq_zero.mpr ((measureReal_eq_zero_iff (measure_ne_top ν _)).mp
      ((G.block_mass_balance b).symm.trans hz))⟩

end OriginalStageClockGrid
end OTSelector.Reconstruction
