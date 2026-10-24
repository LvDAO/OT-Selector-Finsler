import OTSelector.Reconstruction.OriginalLegalScreeningComparatorClockBlockFloorsCounts

/-! The real half-open grid prefix masses and the unchanged kept-prefix conventions. -/
open Set Function MeasureTheory Module Manifold
open scoped ENNReal BigOperators Classical ContDiff
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OTSelector.Reconstruction
open OTSelector.Probability
namespace OriginalStageClockGrid
variable (G : OriginalStageClockGrid) {μ ν : Measure ℝ}

/-- Literal finite source and target clock prefixes equal their distinct half-open intervals. -/
theorem clockSlabPrefix_eq_grid_masses [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {k : ℕ} (hk : k ≤ G.count) :
    finiteClockPrefix (fun i ↦ μ.real (G.sourceCell i)) k = μ.real (Ico (G.cut 0) (G.cut k)) ∧
    finiteClockPrefix (fun i ↦ ν.real (G.targetCell i)) k = ν.real (Ioc (G.cut 0) (G.cut k)) := by
  let P : Finset (Fin G.count) := Finset.univ.filter (fun i ↦ i.val < k)
  have heS : (⋃ i ∈ P, G.sourceCell i) = Ico (G.cut 0) (G.cut k) := by
    ext x
    constructor
    · intro hx
      obtain ⟨i,hi,hx⟩ := mem_iUnion₂.mp hx
      exact ⟨(G.strictMono.monotone (Nat.zero_le _)).trans hx.1,
        (G.sourceCell_lt_cut_iff hx k).2 (Finset.mem_filter.mp hi).2⟩
    · intro hx
      have hgrid : x ∈ ⋃ i, G.sourceCell i := by
        rw [G.source_union]
        exact ⟨hx.1,hx.2.trans_le (G.strictMono.monotone hk)⟩
      obtain ⟨i,hi⟩ := mem_iUnion.mp hgrid
      exact mem_iUnion₂.mpr ⟨i,Finset.mem_filter.mpr
        ⟨Finset.mem_univ _,(G.sourceCell_lt_cut_iff hi k).1 hx.2⟩,hi⟩
  have heT : (⋃ i ∈ P, G.targetCell i) = Ioc (G.cut 0) (G.cut k) := by
    ext x
    constructor
    · intro hx
      obtain ⟨i,hi,hx⟩ := mem_iUnion₂.mp hx
      exact ⟨(G.strictMono.monotone (Nat.zero_le _)).trans_lt hx.1,
        (G.targetCell_le_cut_iff hx k).2 (Finset.mem_filter.mp hi).2⟩
    · intro hx
      have hgrid : x ∈ ⋃ i, G.targetCell i := by
        rw [G.target_union]
        exact ⟨hx.1,hx.2.trans (G.strictMono.monotone hk)⟩
      obtain ⟨i,hi⟩ := mem_iUnion.mp hgrid
      exact mem_iUnion₂.mpr ⟨i,Finset.mem_filter.mpr
        ⟨Finset.mem_univ _,(G.targetCell_le_cut_iff hi k).1 hx.2⟩,hi⟩
  constructor
  · rw [finiteClockPrefix_eq_filter _ hk]
    exact (measureReal_biUnion_finset (fun _ _ _ _ hn ↦ G.source_disjoint hn)
      (fun _ _ ↦ measurableSet_Ico) (fun _ _ ↦ measure_ne_top μ _)).symm.trans
        (congrArg μ.real heS)
  · rw [finiteClockPrefix_eq_filter _ hk]
    exact (measureReal_biUnion_finset (fun _ _ _ _ hn ↦ G.target_disjoint hn)
      (fun _ _ ↦ measurableSet_Ioc) (fun _ _ ↦ measure_ne_top ν _)).symm.trans
        (congrArg ν.real heT)

/-- The true grid surplus uses exactly the raw-source Ico and raw-target Ioc prefix means. -/
theorem clockSlabSurplus_eq_grid_prefix [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {k : ℕ} (hk : k ≤ G.count) :
    G.clockSlabSurplus μ ν k = μ.real (Ico (G.cut 0) (G.cut k)) - ν.real (Ioc (G.cut 0) (G.cut k)) := by
  obtain ⟨hs,ht⟩ := G.clockSlabPrefix_eq_grid_masses (μ := μ) (ν := ν) hk
  exact congrArg₂ (· - ·) hs ht

/-- Every observed grid-prefix source mark belongs to an actual constructed block. -/
theorem source_grid_prefix_subset_blocks
    (h₀ : G.clockSlabSurplus μ ν 0 = 0) (hN : G.clockSlabSurplus μ ν G.count = 0)
    {k : ℕ} (hk : k ≤ G.count) :
    Ico (G.cut 0) (G.cut k) ⊆ ⋃ block : G.ClockSlabBlock μ ν, G.sourceBlockCell μ ν block := by
  intro x hx
  have hgrid : x ∈ ⋃ i, G.sourceCell i := by
    rw [G.source_union]
    exact ⟨hx.1,hx.2.trans_le (G.strictMono.monotone hk)⟩
  obtain ⟨i,hi⟩ := mem_iUnion.mp hgrid
  obtain ⟨block,hblock,_⟩ := exists_unique_finiteSurplusStrictBlock _ G.count h₀ hN i
  exact mem_iUnion.mpr ⟨block,(G.mem_sourceBlockCell_iff block hi).2 hblock⟩
end OriginalStageClockGrid

/-- The actual kept union lies in its real grid cells. Hence its strict-source and
closed-target prefixes equal the two raw-grid prefix sets, without raw-support assumptions. -/
theorem originalOrientedClockBlockKeptData_prefix_counts
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
    {F : Geometry.ContinuousFinslerNorm E M} {u : M → ℝ}
    (S : Geometry.ContinuousFinslerNorm.CalibratedLevelSeedPatch F u) (w : S.covector.ker)
    (G : OriginalStageClockGrid) (μ ν : Measure ℝ)
    (b : OrthonormalBasis (Fin (finrank ℝ S.covector.ker)) ℝ
      (EuclideanSpace ℝ (Fin (finrank ℝ S.covector.ker)))) (R ell : ℝ)
    (scene : LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))
    (source target : MarkedCloudSpace (finrank ℝ S.covector.ker) ℝ)
    (Cs Ct : G.ClockSlabBlock μ ν → Set ℝ) (c : ℝ) :
    let A := originalOrientedClockBlockKeptData S w G μ ν b R ell scene source target Cs Ct
    originalStageRemainingReserveClassCount source A.sourceKept (Iio c) =
      originalStageRemainingReserveClassCount source A.sourceKept (Ico (G.cut 0) c) ∧
    originalStageRemainingReserveClassCount target A.targetKept (Iic c) =
      originalStageRemainingReserveClassCount target A.targetKept (Ioc (G.cut 0) c) := by
  classical
  let A := originalOrientedClockBlockKeptData S w G μ ν b R ell scene source target Cs Ct
  constructor
  · unfold originalStageRemainingReserveClassCount
    congr 1
    ext i
    simp only [Finset.mem_filter,mem_Iio,mem_Ico]
    constructor
    · rintro ⟨hi,hx⟩
      have hu := originalReserveBlocksKeptFin_mark_mem_union
        (originalCenteredPhysicalCubeRegion b (2*R)) 0 1 (G.sourceBlockCell μ ν) (G.targetBlockCell μ ν) Cs
        ((scene,target),source.1,fun i ↦ (source.2 i).2) i hi
      simp only [OriginalStageClockGrid.sourceBlockCell,mem_iUnion] at hu
      obtain ⟨block,j,_,hj⟩ := hu
      have hlo := (G.strictMono.monotone (Nat.zero_le _)).trans hj.1
      exact ⟨hi,hlo,hx⟩
    · rintro ⟨hi,_,hx⟩
      exact ⟨hi,hx⟩
  · unfold originalStageRemainingReserveClassCount
    congr 1
    ext i
    simp only [Finset.mem_filter,mem_Iic,mem_Ioc]
    constructor
    · rintro ⟨hi,hx⟩
      have hu := originalReserveBlocksKeptFin_mark_mem_union
        (originalCenteredPhysicalCubeRegion b (2*R)) 1 0 (G.targetBlockCell μ ν) (G.sourceBlockCell μ ν) Ct
        ((scene,source),target.1,fun i ↦ (target.2 i).2) i hi
      simp only [OriginalStageClockGrid.targetBlockCell,mem_iUnion] at hu
      obtain ⟨block,j,_,hj⟩ := hu
      have hlo := (G.strictMono.monotone (Nat.zero_le _)).trans_lt hj.1
      exact ⟨hi,hlo,hx⟩
    · rintro ⟨hi,_,hx⟩
      exact ⟨hi,hx⟩

end OTSelector.Reconstruction
