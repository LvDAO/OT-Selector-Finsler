import OTSelector.Reconstruction.OriginalLegalScreeningComparatorClockBlockEndpointsFlow

/-! Actual strict/closed tight-cut prefixes are unions of complete original clock blocks. -/
open Set Function MeasureTheory
open scoped BigOperators ENNReal
noncomputable section
namespace OTSelector.Reconstruction.OriginalStageClockGrid
variable (G : OriginalStageClockGrid) {μ ν : Measure ℝ}

/-- A tight cut never lies inside a constructed block. Hence a class is before that
cut exactly when its whole block ends at or before it. -/
theorem block_contains_lt_tight_cut_iff
    (b : G.ClockSlabBlock μ ν) {k : Fin (G.count+1)}
    (hk : G.clockSlabSurplus μ ν k.val = 0) {i : Fin G.count} (hi : b.Contains i) :
    i.val < k.val ↔ b.upper.val ≤ k.val := by
  constructor
  · intro hik
    by_contra hn
    have hku : k < b.upper := by exact lt_of_not_ge hn
    have hlk : b.lower < k := hi.1.trans_lt hik
    exact b.consecutive.2.2.2 k hlk hku hk
  · intro huk
    exact hi.2.trans_le huk

/-- A strict source prefix on the true grid is precisely the complete preceding
source blocks. The source atom at a cut is excluded on both sides. -/
theorem source_tight_prefix_eq_block_union
    (h₀ : G.clockSlabSurplus μ ν 0 = 0) (hN : G.clockSlabSurplus μ ν G.count = 0)
    {k : Fin (G.count+1)} (hk : G.clockSlabSurplus μ ν k.val = 0) :
    (⋃ i, G.sourceCell i) ∩ Iio (G.cut k.val) =
      ⋃ b : G.ClockSlabBlock μ ν, ⋃ (_ : b.upper.val ≤ k.val), G.sourceBlockCell μ ν b := by
  classical
  ext x
  constructor
  · rintro ⟨hx,hcut⟩
    obtain ⟨i,hi⟩ := mem_iUnion.mp hx
    obtain ⟨b,hbi,_⟩ := exists_unique_finiteSurplusStrictBlock _ G.count h₀ hN i
    exact mem_iUnion.mpr ⟨b,mem_iUnion.mpr
      ⟨(G.block_contains_lt_tight_cut_iff b hk hbi).1 ((G.sourceCell_lt_cut_iff hi k.val).1 hcut),
        (G.mem_sourceBlockCell_iff b hi).2 hbi⟩⟩
  · intro hx
    obtain ⟨b,hb⟩ := mem_iUnion.mp hx
    obtain ⟨hbk,hxb⟩ := mem_iUnion.mp hb
    obtain ⟨i,hi⟩ := mem_iUnion.mp hxb
    obtain ⟨hib,hxi⟩ := mem_iUnion.mp hi
    have hbi := (Finset.mem_filter.mp hib).2
    exact ⟨mem_iUnion.mpr ⟨i,hxi⟩,
      (G.sourceCell_lt_cut_iff hxi k.val).2 ((G.block_contains_lt_tight_cut_iff b hk hbi).2 hbk)⟩

/-- The target convention is separately closed at the same tight cut. -/
theorem target_tight_prefix_eq_block_union
    (h₀ : G.clockSlabSurplus μ ν 0 = 0) (hN : G.clockSlabSurplus μ ν G.count = 0)
    {k : Fin (G.count+1)} (hk : G.clockSlabSurplus μ ν k.val = 0) :
    (⋃ j, G.targetCell j) ∩ Iic (G.cut k.val) =
      ⋃ b : G.ClockSlabBlock μ ν, ⋃ (_ : b.upper.val ≤ k.val), G.targetBlockCell μ ν b := by
  classical
  ext y
  constructor
  · rintro ⟨hy,hcut⟩
    obtain ⟨j,hj⟩ := mem_iUnion.mp hy
    obtain ⟨b,hbj,_⟩ := exists_unique_finiteSurplusStrictBlock _ G.count h₀ hN j
    exact mem_iUnion.mpr ⟨b,mem_iUnion.mpr
      ⟨(G.block_contains_lt_tight_cut_iff b hk hbj).1 ((G.targetCell_le_cut_iff hj k.val).1 hcut),
        (G.mem_targetBlockCell_iff b hj).2 hbj⟩⟩
  · intro hy
    obtain ⟨b,hb⟩ := mem_iUnion.mp hy
    obtain ⟨hbk,hyb⟩ := mem_iUnion.mp hb
    obtain ⟨j,hj⟩ := mem_iUnion.mp hyb
    obtain ⟨hjb,hyj⟩ := mem_iUnion.mp hj
    have hbj := (Finset.mem_filter.mp hjb).2
    exact ⟨mem_iUnion.mpr ⟨j,hyj⟩,
      (G.targetCell_le_cut_iff hyj k.val).2 ((G.block_contains_lt_tight_cut_iff b hk hbj).2 hbk)⟩

/-- Actual per-block real mass balance implies actual tight-cut prefix balance,
with the true source and target endpoint conventions and no strict Hall premise. -/
theorem tight_prefix_masses_eq_of_block_balance
    (h₀ : G.clockSlabSurplus μ ν 0 = 0) (hN : G.clockSlabSurplus μ ν G.count = 0)
    (ρs ρt : Measure ℝ) [IsFiniteMeasure ρs] [IsFiniteMeasure ρt]
    (hs : ∀ᵐ x ∂ρs, x ∈ ⋃ i, G.sourceCell i)
    (ht : ∀ᵐ y ∂ρt, y ∈ ⋃ j, G.targetCell j)
    (hbal : ∀ b : G.ClockSlabBlock μ ν,
      ρs.real (G.sourceBlockCell μ ν b) = ρt.real (G.targetBlockCell μ ν b))
    {k : Fin (G.count+1)} (hk : G.clockSlabSurplus μ ν k.val = 0) :
    ρs.real (Iio (G.cut k.val)) = ρt.real (Iic (G.cut k.val)) := by
  classical
  let blocks : Finset (G.ClockSlabBlock μ ν) := Finset.univ.filter (fun b ↦ b.upper.val ≤ k.val)
  have heS : ρs.real (Iio (G.cut k.val)) =
      ρs.real (⋃ b ∈ blocks, G.sourceBlockCell μ ν b) := by
    apply congrArg ENNReal.toReal
    apply measure_congr
    filter_upwards [hs] with x hx
    rw [show (⋃ b ∈ blocks, G.sourceBlockCell μ ν b) =
      (⋃ i, G.sourceCell i) ∩ Iio (G.cut k.val) by
        rw [G.source_tight_prefix_eq_block_union h₀ hN hk]
        simp only [blocks,Finset.mem_filter,Finset.mem_univ,true_and]]
    exact propext ⟨fun h ↦ ⟨hx,h⟩,And.right⟩
  have heT : ρt.real (Iic (G.cut k.val)) =
      ρt.real (⋃ b ∈ blocks, G.targetBlockCell μ ν b) := by
    apply congrArg ENNReal.toReal
    apply measure_congr
    filter_upwards [ht] with y hy
    rw [show (⋃ b ∈ blocks, G.targetBlockCell μ ν b) =
      (⋃ j, G.targetCell j) ∩ Iic (G.cut k.val) by
        rw [G.target_tight_prefix_eq_block_union h₀ hN hk]
        simp only [blocks,Finset.mem_filter,Finset.mem_univ,true_and]]
    exact propext ⟨fun h ↦ ⟨hy,h⟩,And.right⟩
  rw [heS,heT,
    measureReal_biUnion_finset (fun _ _ _ _ h ↦ (G.blockCells_disjoint h₀ hN).1 h)
      (fun b _ ↦ (G.blockCells_measurable b).1) (fun _ _ ↦ measure_ne_top ρs _),
    measureReal_biUnion_finset (fun _ _ _ _ h ↦ (G.blockCells_disjoint h₀ hN).2 h)
      (fun b _ ↦ (G.blockCells_measurable b).2) (fun _ _ ↦ measure_ne_top ρt _)]
  exact Finset.sum_congr rfl (fun b _ ↦ hbal b)

end OTSelector.Reconstruction.OriginalStageClockGrid
