import OTSelector.Reconstruction.OriginalLegalScreeningExpectedCostWorkingDominance
import OTSelector.Reconstruction.OriginalLegalScreeningComparatorActualSignedMaximumObjects

/-! The genuine original-block signed comparator reads into the same complete expected-cost budget. -/
open Set Function MeasureTheory Module Manifold TopologicalSpace
open scoped BigOperators ENNReal Classical ContDiff
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability OTSelector.Geometry ContinuousFinslerNorm
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 300000

/-- The actual fixed block-width/floor coefficient of each original fine stage. -/
def originalScreeningBlockStageWeight {μ ν : Measure ℝ} (G : OriginalStageClockGrid)
    (h₀ : G.clockSlabSurplus μ ν 0 = 0) (hN : G.clockSlabSurplus μ ν G.count = 0)
    (floor C : ℝ) (i : Fin G.count) : ℝ :=
  3*C*((((G.blockForClass h₀ hN i).upper.val-(G.blockForClass h₀ hN i).lower.val : ℕ) : ℝ))*floor⁻¹

/-- Genuine positive scalar floors give nonnegative stage weights. -/
theorem originalScreeningBlockStageWeight_nonneg {μ ν : Measure ℝ} (G : OriginalStageClockGrid)
    (h₀ : G.clockSlabSurplus μ ν 0 = 0) (hN : G.clockSlabSurplus μ ν G.count = 0)
    {floor C : ℝ} (hfloor : 0 ≤ floor) (hC : 0 ≤ C) (i : Fin G.count) :
    0 ≤ originalScreeningBlockStageWeight G h₀ hN floor C i := by
  unfold originalScreeningBlockStageWeight
  positivity

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {S : CalibratedLevelSeedPatch F u} {w : S.covector.ker} {μ ν : Measure ℝ}

omit [BorelSpace E] in
/-- Genuine local block stages sum to the same original weighted finite family. -/
theorem originalScreeningBlockStageBudget_eq_weighted
    {kin : ℝ → ℝ → (Fin (finrank ℝ S.covector.ker) → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (Q : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν kin g)
    (G : OriginalStageClockGrid) (h₀ : G.clockSlabSurplus μ ν 0 = 0) (hN : G.clockSlabSurplus μ ν G.count = 0)
    (b : OrthonormalBasis (Fin (finrank ℝ S.covector.ker)) ℝ
      (EuclideanSpace ℝ (Fin (finrank ℝ S.covector.ker))))
    (K : Fin G.count → Compacts (Fin (finrank ℝ S.covector.ker) → ℝ)) (R ell floor C : ℝ)
    (hj : ∀ i : Fin G.count, ∀ k, MemLp (fun scene ↦ originalSeedPathClockSetCurrent S w
      (originalEuclideanMollifier _) (Ioc (G.cut i.val) (G.cut (i.val+1))) scene k) 2 (Q.law : Measure _))
    (scene : LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker)) :
    (∑ block, C*originalClockBlockStageRepairBudget Q G b K R ell floor hj block scene) =
      ∑ i, originalScreeningBlockStageWeight G h₀ hN floor C i*
        originalOrientedStageCurrentInputNeumannBudget S w Q b (K i) R ell
          (G.cut i.val) (G.cut (i.val+1)) (hj i) scene := by
  let B := fun i : Fin G.count ↦ originalOrientedStageCurrentInputNeumannBudget S w Q b
    (K i) R ell (G.cut i.val) (G.cut (i.val+1)) (hj i) scene
  have hh := G.sum_originalBlock_stages h₀ hN
    (fun block ↦ 3*C*((block.upper.val-block.lower.val : ℕ) : ℝ))
    (fun i ↦ floor⁻¹*B i)
  calc
    _ = ∑ block : G.ClockSlabBlock μ ν,
        (3*C*((block.upper.val-block.lower.val : ℕ) : ℝ))*
          ∑ k : Fin (block.upper.val-block.lower.val),
            floor⁻¹*B ⟨block.lower.val+k.val,by have h := block.upper.isLt; have hh := k.isLt; omega⟩ := by
      apply Finset.sum_congr rfl
      intro block _
      unfold originalClockBlockStageRepairBudget
      ring
    _ = _ := hh.trans (by
      apply Finset.sum_congr rfl
      intro i _
      dsimp only [originalScreeningBlockStageWeight,B]
      ring)

/-- The actual original clock-grid specialization of the complete budget.
Its two reserve families retain their separate own/opposite block conventions. -/
def originalScreeningClockGridCompleteCostBudget {J : Type*} [Fintype J]
    {kin : ℝ → ℝ → (Fin (finrank ℝ S.covector.ker) → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (Q : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν kin g)
    (G : OriginalStageClockGrid) (h₀ : G.clockSlabSurplus μ ν 0 = 0) (hN : G.clockSlabSurplus μ ν G.count = 0)
    (b : OrthonormalBasis (Fin (finrank ℝ S.covector.ker)) ℝ
      (EuclideanSpace ℝ (Fin (finrank ℝ S.covector.ker))))
    (K : Fin G.count → Compacts (Fin (finrank ℝ S.covector.ker) → ℝ))
    (R ell rawRate floor C L tilt r : ℝ) (cuts ε : J → ℝ)
    (hj : ∀ i : Fin G.count, ∀ k, MemLp (fun scene ↦ originalSeedPathClockSetCurrent S w
      (originalEuclideanMollifier _) (Ioc (G.cut i.val) (G.cut (i.val+1))) scene k) 2 (Q.law : Measure _))
    (p : LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker) ×
      TwoMarkedCloudSpace (finrank ℝ S.covector.ker) ℝ ℝ) : ℝ :=
  let Hs := G.sourceReserveFineBlockPartition h₀ hN
  let Ht := G.targetReserveFineBlockPartition h₀ hN
  originalScreeningCompleteCostBudget S w Q b K R ell
    (fun i ↦ G.cut i.val) (fun i ↦ G.cut (i.val+1))
    (originalScreeningBlockStageWeight G h₀ hN floor C) hj rawRate G r cuts ε C L
    (Sum.elim (fun i ↦ Hs.blockCell (Hs.blockFor i)) (fun i ↦ Ht.blockCell (Ht.blockFor i)))
    (Sum.elim (fun i ↦ Hs.oppositeCell (Hs.blockFor i)) (fun i ↦ Ht.oppositeCell (Ht.blockFor i)))
    (Sum.elim (fun i ↦ Hs.deletionCell (Hs.blockFor i)) (fun _ ↦ ∅))
    (Sum.elim (fun _ ↦ ∅) (fun i ↦ Ht.deletionCell (Ht.blockFor i)))
    (Sum.elim Hs.fineCell (fun _ ↦ ∅)) (Sum.elim (fun _ ↦ ∅) Ht.fineCell) tilt p

omit [BorelSpace E] in
/-- The actual comparator budget differs from the complete cost budget only
by its already paid genuine joint exceptional-count correction. -/
theorem originalScreeningClockGridCompleteCostBudget_eq_signed_add_exception {J : Type*} [Fintype J]
    {kin : ℝ → ℝ → (Fin (finrank ℝ S.covector.ker) → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (Q : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν kin g)
    (G : OriginalStageClockGrid) (h₀ : G.clockSlabSurplus μ ν 0 = 0) (hN : G.clockSlabSurplus μ ν G.count = 0)
    (b : OrthonormalBasis (Fin (finrank ℝ S.covector.ker)) ℝ
      (EuclideanSpace ℝ (Fin (finrank ℝ S.covector.ker))))
    (K : Fin G.count → Compacts (Fin (finrank ℝ S.covector.ker) → ℝ))
    (R ell rawRate floor C L tilt r : ℝ) (cuts ε : J → ℝ)
    (hj : ∀ i : Fin G.count, ∀ k, MemLp (fun scene ↦ originalSeedPathClockSetCurrent S w
      (originalEuclideanMollifier _) (Ioc (G.cut i.val) (G.cut (i.val+1))) scene k) 2 (Q.law : Measure _))
    (p : LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker) ×
      TwoMarkedCloudSpace (finrank ℝ S.covector.ker) ℝ ℝ) :
    originalScreeningClockGridCompleteCostBudget Q G h₀ hN b K R ell rawRate floor C L tilt r cuts ε hj p =
      originalActualClockBlockSignedMaximumBudget Q G h₀ hN b K R ell floor C L tilt hj p +
      (4*C*(finrank ℝ S.covector.ker : ℝ)*R^2+2*L)*
        (originalScreeningAllFailure S w μ ν (Q.law : Measure _) b rawRate R G r cuts ε).indicator
          (originalScreeningFullExperimentCount (originalCenteredPhysicalCubeRegion b (2*R))) p := by
  have hs := originalScreeningBlockStageBudget_eq_weighted Q G h₀ hN b K R ell floor C hj p.1
  simp only [originalScreeningClockGridCompleteCostBudget,originalScreeningCompleteCostBudget,
    originalScreeningLowerOrderCostBudget,originalActualClockBlockSignedMaximumBudget,
    originalScreeningPartitionReserveEndpointEnergy] at ⊢
  simp only [hs,OriginalOrientedStageResidualDensityData.sourcePortMeasure,
    OriginalOrientedStageResidualDensityData.targetPortMeasure,originalUnusedBlockReserveData,
    measureReal_def,Measure.fst_univ,Measure.snd_univ]
  ring

end OTSelector.Reconstruction
