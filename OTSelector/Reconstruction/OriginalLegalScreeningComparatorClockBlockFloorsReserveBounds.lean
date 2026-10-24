import OTSelector.Reconstruction.OriginalLegalScreeningComparatorClockBlockFloorsPrefixMasses
import OTSelector.Reconstruction.OriginalLegalScreeningComparatorClockBlockFloorsClassCounts

/-! Actual raw-prefix fluctuations and actual block deletions control the unchanged kept data. -/
open Set Function MeasureTheory Module Manifold
open scoped ENNReal BigOperators Classical ContDiff
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
namespace OTSelector.Reconstruction
open OTSelector.Geometry ContinuousFinslerNorm OTSelector.Probability
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {S : CalibratedLevelSeedPatch F u} {w : S.covector.ker} {μ ν : Measure ℝ}

/-- The genuine kept union loses at most the actual excess deletions. Two true raw
prefix deviations then give a three-error lower bound for kept signed prefixes, and
adjacent prefixes give the same bound for each actual surviving clock class. -/
theorem originalOrientedClockBlockKeptData_reserve_bounds
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] (G : OriginalStageClockGrid)
    (h₀ : G.clockSlabSurplus μ ν 0 = 0) (hN : G.clockSlabSurplus μ ν G.count = 0)
    (b : OrthonormalBasis (Fin (finrank ℝ S.covector.ker)) ℝ
      (EuclideanSpace ℝ (Fin (finrank ℝ S.covector.ker)))) (R ell θ e : ℝ)
    (scene : LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))
    (source target : MarkedCloudSpace (finrank ℝ S.covector.ker) ℝ)
    (Cs Ct : G.ClockSlabBlock μ ν → Set ℝ) :
    let A := originalOrientedClockBlockKeptData S w G μ ν b R ell scene source target Cs Ct
    (∀ k : Fin (G.count+1),
      |(originalReserveBlockCount source.1 (fun i ↦ (source.2 i).2) (Ico (G.cut 0) (G.cut k.val)) : ℝ) -
        θ*A.cubeVolume*μ.real (Ico (G.cut 0) (G.cut k.val))| ≤ e*A.cubeVolume) →
    (∀ k : Fin (G.count+1),
      |(originalReserveBlockCount target.1 (fun i ↦ (target.2 i).2) (Ioc (G.cut 0) (G.cut k.val)) : ℝ) -
        θ*A.cubeVolume*ν.real (Ioc (G.cut 0) (G.cut k.val))| ≤ e*A.cubeVolume) →
    (((∑ block : G.ClockSlabBlock μ ν,
      (originalReserveBlockExcess (originalCenteredPhysicalCubeRegion b (2*R)) 0 1
        (G.sourceBlockCell μ ν block) (G.targetBlockCell μ ν block)
          ((scene,target),source.1,fun i ↦ (source.2 i).2) +
      originalReserveBlockExcess (originalCenteredPhysicalCubeRegion b (2*R)) 1 0
        (G.targetBlockCell μ ν block) (G.sourceBlockCell μ ν block)
          ((scene,source),target.1,fun i ↦ (target.2 i).2))) : ℕ) : ℝ) ≤ e*A.cubeVolume →
    (∀ k : Fin (G.count+1),
      θ*A.cubeVolume*G.clockSlabSurplus μ ν k.val-3*e*A.cubeVolume ≤ A.reservePrefix (G.cut k.val)) ∧
    ∀ i : Fin G.count,
      θ*A.cubeVolume*μ.real (G.sourceCell i)-3*e*A.cubeVolume ≤
        (originalStageRemainingReserveClassCount source A.sourceKept (G.sourceCell i) : ℝ) ∧
      θ*A.cubeVolume*ν.real (G.targetCell i)-3*e*A.cubeVolume ≤
        (originalStageRemainingReserveClassCount target A.targetKept (G.targetCell i) : ℝ) := by
  classical
  dsimp only
  let A := originalOrientedClockBlockKeptData S w G μ ν b R ell scene source target Cs Ct
  intro hs ht hdel
  let exS := fun block : G.ClockSlabBlock μ ν ↦
    originalReserveBlockExcess (originalCenteredPhysicalCubeRegion b (2*R)) 0 1
      (G.sourceBlockCell μ ν block) (G.targetBlockCell μ ν block)
        ((scene,target),source.1,fun i ↦ (source.2 i).2)
  let exT := fun block : G.ClockSlabBlock μ ν ↦
    originalReserveBlockExcess (originalCenteredPhysicalCubeRegion b (2*R)) 1 0
      (G.targetBlockCell μ ν block) (G.sourceBlockCell μ ν block)
        ((scene,source),target.1,fun i ↦ (target.2 i).2)
  have hdS : ((∑ block, exS block : ℕ) : ℝ) ≤ e*A.cubeVolume := by
    have hh : (∑ block, exS block) ≤ ∑ block, (exS block+exT block) :=
      Finset.sum_le_sum (fun block _ ↦ Nat.le_add_right _ _)
    exact (Nat.cast_le (α := ℝ).mpr hh).trans hdel
  have hdT : ((∑ block, exT block : ℕ) : ℝ) ≤ e*A.cubeVolume := by
    have hh : (∑ block, exT block) ≤ ∑ block, (exS block+exT block) :=
      Finset.sum_le_sum (fun block _ ↦ Nat.le_add_left _ _)
    exact (Nat.cast_le (α := ℝ).mpr hh).trans hdel
  have hsLoss (U : Set ℝ) (hU : U ⊆ ⋃ block : G.ClockSlabBlock μ ν, G.sourceBlockCell μ ν block) :
      (originalReserveBlockCount source.1 (fun i ↦ (source.2 i).2) U : ℝ) ≤
        (originalStageRemainingReserveClassCount source A.sourceKept U : ℝ)+e*A.cubeVolume := by
    have hh := originalReserveBlocksKeptFin_raw_class_count_le (originalCenteredPhysicalCubeRegion b (2*R))
      0 1 (G.sourceBlockCell μ ν) (G.targetBlockCell μ ν) Cs scene source target U hU
    have hr : (originalReserveBlockCount source.1 (fun i ↦ (source.2 i).2) U : ℝ) ≤
        (originalStageRemainingReserveClassCount source A.sourceKept U : ℝ)+((∑ block, exS block : ℕ) : ℝ) := by
      exact_mod_cast hh
    exact hr.trans (add_le_add le_rfl hdS)
  have htLoss (U : Set ℝ) (hU : U ⊆ ⋃ block : G.ClockSlabBlock μ ν, G.targetBlockCell μ ν block) :
      (originalReserveBlockCount target.1 (fun i ↦ (target.2 i).2) U : ℝ) ≤
        (originalStageRemainingReserveClassCount target A.targetKept U : ℝ)+e*A.cubeVolume := by
    have hh := originalReserveBlocksKeptFin_raw_class_count_le (originalCenteredPhysicalCubeRegion b (2*R))
      1 0 (G.targetBlockCell μ ν) (G.sourceBlockCell μ ν) Ct scene target source U hU
    have hr : (originalReserveBlockCount target.1 (fun i ↦ (target.2 i).2) U : ℝ) ≤
        (originalStageRemainingReserveClassCount target A.targetKept U : ℝ)+((∑ block, exT block : ℕ) : ℝ) := by
      exact_mod_cast hh
    exact hr.trans (add_le_add le_rfl hdT)
  constructor
  · intro k
    have hsk := hsLoss (Ico (G.cut 0) (G.cut k.val))
      (G.source_grid_prefix_subset_blocks h₀ hN (Nat.le_of_lt_succ k.isLt))
    have htk : (originalStageRemainingReserveClassCount target A.targetKept (Ioc (G.cut 0) (G.cut k.val)) : ℝ) ≤
        (originalReserveBlockCount target.1 (fun i ↦ (target.2 i).2) (Ioc (G.cut 0) (G.cut k.val)) : ℝ) := by
      exact_mod_cast originalRemainingReserveClassCount_le_raw target A.targetKept (Ioc (G.cut 0) (G.cut k.val))
    have hp := originalOrientedClockBlockKeptData_prefix_counts S w G μ ν b R ell scene source target Cs Ct (G.cut k.val)
    change _ ≤ (originalStageRemainingReserveClassCount source A.sourceKept (Iio (G.cut k.val)) : ℝ)-
      (originalStageRemainingReserveClassCount target A.targetKept (Iic (G.cut k.val)) : ℝ)
    rw [hp.1,hp.2,G.clockSlabSurplus_eq_grid_prefix (Nat.le_of_lt_succ k.isLt)]
    have hlo := (abs_le.mp (hs k)).1
    have hup := (abs_le.mp (ht k)).2
    nlinarith only [hsk,htk,hlo,hup]
  · intro i
    let kl : Fin (G.count+1) := ⟨i.val,by omega⟩
    let kr : Fin (G.count+1) := ⟨i.val+1,by omega⟩
    have hS : G.sourceCell i ⊆ ⋃ block : G.ClockSlabBlock μ ν, G.sourceBlockCell μ ν block := by
      intro x hx
      obtain ⟨block,hblock,_⟩ := exists_unique_finiteSurplusStrictBlock _ G.count h₀ hN i
      exact mem_iUnion.mpr ⟨block,(G.mem_sourceBlockCell_iff block hx).2 hblock⟩
    have hT : G.targetCell i ⊆ ⋃ block : G.ClockSlabBlock μ ν, G.targetBlockCell μ ν block := by
      intro x hx
      obtain ⟨block,hblock,_⟩ := exists_unique_finiteSurplusStrictBlock _ G.count h₀ hN i
      exact mem_iUnion.mpr ⟨block,(G.mem_targetBlockCell_iff block hx).2 hblock⟩
    have hsource := originalReserveBlockCount_grid_increment_lower source.1 (fun j ↦ (source.2 j).2) μ
      (G.strictMono.monotone (Nat.zero_le i.val)) (G.strictMono.monotone (Nat.le_succ i.val)) (hs kl) (hs kr)
    have htarget := originalReserveBlockCount_target_grid_increment_lower target.1 (fun j ↦ (target.2 j).2) ν
      (G.strictMono.monotone (Nat.zero_le i.val)) (G.strictMono.monotone (Nat.le_succ i.val)) (ht kl) (ht kr)
    change θ*A.cubeVolume*μ.real (G.sourceCell i)-2*e*A.cubeVolume ≤
      (originalReserveBlockCount source.1 (fun j ↦ (source.2 j).2) (G.sourceCell i) : ℝ) at hsource
    change θ*A.cubeVolume*ν.real (G.targetCell i)-2*e*A.cubeVolume ≤
      (originalReserveBlockCount target.1 (fun j ↦ (target.2 j).2) (G.targetCell i) : ℝ) at htarget
    have hsl := hsLoss (G.sourceCell i) hS
    have htl := htLoss (G.targetCell i) hT
    exact ⟨by linarith only [hsource,hsl],by linarith only [htarget,htl]⟩

end OTSelector.Reconstruction
