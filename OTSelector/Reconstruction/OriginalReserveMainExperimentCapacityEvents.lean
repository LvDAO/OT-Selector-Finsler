import OTSelector.Reconstruction.OriginalMarkSelectedPopulationCouplingBlockExcessBudgetFailure
import OTSelector.Reconstruction.OriginalClasswiseOriginalAtomRepairClockSlabBlockExtremes

/-! Literal blockwise reserve deletion capacities on the unchanged original main experiment. -/
open Set Function MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators Classical
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000

/-- The actual sorted-index deletion requests exceed an original block's
available extreme-class reserve count. All real blocks, including zero blocks,
remain in this event. -/
def originalMainReserveClockSlabCapacityFailure {q : ℕ} (α β : Measure ℝ)
    (b : OrthonormalBasis (Fin q) ℝ (EuclideanSpace ℝ (Fin q)))
    (R : ℝ) (G : OriginalStageClockGrid) :
    Set (LegalMarkedOptimalInputScene q × TwoMarkedCloudSpace q ℝ ℝ) :=
  {p | ∃ block : G.ClockSlabBlock α β,
    originalReserveBlockCount p.2.1.1 (fun i ↦ (p.2.1.2 i).2)
      (G.sourceCell (G.firstBlockClass block)) <
      originalReserveBlockExcess (originalCenteredPhysicalCubeRegion b (2 * R)) 0 1
        (G.sourceBlockCell α β block) (G.targetBlockCell α β block)
        (originalReserveExcessInputAux (originalSourceReserveExperimentSplice p)) ∨
    originalReserveBlockCount p.2.2.1 (fun i ↦ (p.2.2.2 i).2)
      (G.targetCell (G.lastBlockClass block)) <
      originalReserveBlockExcess (originalCenteredPhysicalCubeRegion b (2 * R)) 1 0
        (G.targetBlockCell α β block) (G.sourceBlockCell α β block)
        (originalReserveExcessInputAux (originalTargetReserveExperimentSplice p))}

/-- The real summed block discrepancy is larger than a positive block's
actual reserve quarter-mean margin. -/
def originalMainReservePositiveBlockDiscrepancyFailure {q : ℕ} (α β : Measure ℝ)
    (b : OrthonormalBasis (Fin q) ℝ (EuclideanSpace ℝ (Fin q)))
    (θ R : ℝ) (G : OriginalStageClockGrid) :
    Set (LegalMarkedOptimalInputScene q × TwoMarkedCloudSpace q ℝ ℝ) :=
  {p | ∃ block : G.ClockSlabBlock α β, block ∈ G.positiveSlabBlocks α β ∧
    (θ * min (α.real (G.sourceCell (G.firstBlockClass block)))
      (β.real (G.targetCell (G.lastBlockClass block))) / 4) *
        volume.real (originalCenteredPhysicalCubeRegion b (2 * R)) <
          originalFullClockSlabDiscrepancy (α := α) (β := β) G
            (originalCenteredPhysicalCubeRegion b (2 * R)) p}

/-- The actual capacity-failure event is Borel in the original scene and
literal two-color reserve sampler. -/
theorem measurableSet_originalMainReserveClockSlabCapacityFailure {q : ℕ} (α β : Measure ℝ)
    (b : OrthonormalBasis (Fin q) ℝ (EuclideanSpace ℝ (Fin q))) (R : ℝ)
    (G : OriginalStageClockGrid) :
    MeasurableSet (originalMainReserveClockSlabCapacityFailure α β b R G) := by
  have haux : Measurable (originalReserveExcessInputAux (q := q)) := by
    unfold originalReserveExcessInputAux
    fun_prop
  have h (block : G.ClockSlabBlock α β) : MeasurableSet
      {p : LegalMarkedOptimalInputScene q × TwoMarkedCloudSpace q ℝ ℝ |
        originalReserveBlockCount p.2.1.1 (fun i ↦ (p.2.1.2 i).2)
          (G.sourceCell (G.firstBlockClass block)) <
          originalReserveBlockExcess (originalCenteredPhysicalCubeRegion b (2 * R)) 0 1
            (G.sourceBlockCell α β block) (G.targetBlockCell α β block)
            (originalReserveExcessInputAux (originalSourceReserveExperimentSplice p)) ∨
        originalReserveBlockCount p.2.2.1 (fun i ↦ (p.2.2.2 i).2)
          (G.targetCell (G.lastBlockClass block)) <
          originalReserveBlockExcess (originalCenteredPhysicalCubeRegion b (2 * R)) 1 0
            (G.targetBlockCell α β block) (G.sourceBlockCell α β block)
            (originalReserveExcessInputAux (originalTargetReserveExperimentSplice p))} := by
    apply MeasurableSet.union
    · exact measurableSet_lt
        (measurable_originalReserveBlockCount (by fun_prop) (by fun_prop) measurableSet_Ico)
        ((measurable_originalReserveBlockExcess (measurableSet_originalOrientedTraffic_cube b R)
          0 1 (G.blockCells_measurable block).1 (G.blockCells_measurable block).2).comp
          (haux.comp (by unfold originalSourceReserveExperimentSplice; fun_prop)))
    · exact measurableSet_lt
        (measurable_originalReserveBlockCount (by fun_prop) (by fun_prop) measurableSet_Ioc)
        ((measurable_originalReserveBlockExcess (measurableSet_originalOrientedTraffic_cube b R)
          1 0 (G.blockCells_measurable block).2 (G.blockCells_measurable block).1).comp
          (haux.comp (by unfold originalTargetReserveExperimentSplice; fun_prop)))
  simpa only [originalMainReserveClockSlabCapacityFailure, Set.ofPred_exists] using
    MeasurableSet.iUnion h

/-- Real original extreme counts and the actual summed full-block discrepancy
internally imply both Nat deletion capacities and protected leftover counts.
No successful deletion, completed matching or floor conclusion is assumed. -/
theorem originalMainReserveClockBlock_capacity_and_slack_of_goodCounts
    {q : ℕ} (α β : Measure ℝ)
    (b : OrthonormalBasis (Fin q) ℝ (EuclideanSpace ℝ (Fin q)))
    {θ R : ℝ} (hθ : 0 ≤ θ) (G : OriginalStageClockGrid)
    (block : G.ClockSlabBlock α β)
    (p : LegalMarkedOptimalInputScene q × TwoMarkedCloudSpace q ℝ ℝ)
    (hs : θ * volume.real (originalCenteredPhysicalCubeRegion b (2 * R)) *
      α.real (G.sourceCell (G.firstBlockClass block)) / 2 ≤
        (originalReserveBlockCount p.2.1.1 (fun i ↦ (p.2.1.2 i).2)
          (G.sourceCell (G.firstBlockClass block)) : ℝ))
    (ht : θ * volume.real (originalCenteredPhysicalCubeRegion b (2 * R)) *
      β.real (G.targetCell (G.lastBlockClass block)) / 2 ≤
        (originalReserveBlockCount p.2.2.1 (fun i ↦ (p.2.2.2 i).2)
          (G.targetCell (G.lastBlockClass block)) : ℝ))
    (hd : originalFullClockSlabDiscrepancy (α := α) (β := β) G
      (originalCenteredPhysicalCubeRegion b (2 * R)) p ≤
        (θ * min (α.real (G.sourceCell (G.firstBlockClass block)))
          (β.real (G.targetCell (G.lastBlockClass block))) / 4) *
            volume.real (originalCenteredPhysicalCubeRegion b (2 * R))) :
    let ds := originalReserveBlockExcess (originalCenteredPhysicalCubeRegion b (2 * R)) 0 1
      (G.sourceBlockCell α β block) (G.targetBlockCell α β block)
      (originalReserveExcessInputAux (originalSourceReserveExperimentSplice p))
    let dt := originalReserveBlockExcess (originalCenteredPhysicalCubeRegion b (2 * R)) 1 0
      (G.targetBlockCell α β block) (G.sourceBlockCell α β block)
      (originalReserveExcessInputAux (originalTargetReserveExperimentSplice p))
    let ns := originalReserveBlockCount p.2.1.1 (fun i ↦ (p.2.1.2 i).2)
      (G.sourceCell (G.firstBlockClass block))
    let nt := originalReserveBlockCount p.2.2.1 (fun i ↦ (p.2.2.2 i).2)
      (G.targetCell (G.lastBlockClass block))
    let m := (θ * min (α.real (G.sourceCell (G.firstBlockClass block)))
      (β.real (G.targetCell (G.lastBlockClass block))) / 4) *
        volume.real (originalCenteredPhysicalCubeRegion b (2 * R))
    ds ≤ ns ∧ dt ≤ nt ∧ m ≤ ((ns-ds : ℕ) : ℝ) ∧ m ≤ ((nt-dt : ℕ) : ℝ) := by
  dsimp only
  let V := volume.real (originalCenteredPhysicalCubeRegion b (2 * R))
  let a := α.real (G.sourceCell (G.firstBlockClass block))
  let c := β.real (G.targetCell (G.lastBlockClass block))
  let m := (θ * min a c / 4) * V
  have hV : 0 ≤ V := measureReal_nonneg
  have hm : 0 ≤ m := mul_nonneg (div_nonneg
    (mul_nonneg hθ (le_min measureReal_nonneg measureReal_nonneg)) (by norm_num)) hV
  have has := mul_le_mul_of_nonneg_left (min_le_left a c) (mul_nonneg hθ hV)
  have hat := mul_le_mul_of_nonneg_left (min_le_right a c) (mul_nonneg hθ hV)
  have hms : 2*m ≤ θ*V*a/2 := by dsimp only [m]; nlinarith only [has]
  have hmt : 2*m ≤ θ*V*c/2 := by dsimp only [m]; nlinarith only [hat]
  have hle := originalReserveBlockExcess_le_fullClockSlabDiscrepancy G
    (originalCenteredPhysicalCubeRegion b (2 * R)) p block
  have hds := hle.1.trans hd
  have hdt := hle.2.trans hd
  change θ*V*a/2 ≤ _ at hs
  change θ*V*c/2 ≤ _ at ht
  change _ ≤ m at hds hdt
  have hcs : originalReserveBlockExcess (originalCenteredPhysicalCubeRegion b (2 * R)) 0 1
      (G.sourceBlockCell α β block) (G.targetBlockCell α β block)
      (originalReserveExcessInputAux (originalSourceReserveExperimentSplice p)) ≤
      originalReserveBlockCount p.2.1.1 (fun i ↦ (p.2.1.2 i).2)
        (G.sourceCell (G.firstBlockClass block)) := by
    apply (Nat.cast_le (α := ℝ)).mp
    linarith only [hds, hs, hms, hm]
  have hct : originalReserveBlockExcess (originalCenteredPhysicalCubeRegion b (2 * R)) 1 0
      (G.targetBlockCell α β block) (G.sourceBlockCell α β block)
      (originalReserveExcessInputAux (originalTargetReserveExperimentSplice p)) ≤
      originalReserveBlockCount p.2.2.1 (fun i ↦ (p.2.2.2 i).2)
        (G.targetCell (G.lastBlockClass block)) := by
    apply (Nat.cast_le (α := ℝ)).mp
    linarith only [hdt, ht, hmt, hm]
  refine ⟨hcs, hct, ?_, ?_⟩
  · rw [Nat.cast_sub hcs]
    change m ≤ _
    linarith only [hds, hs, hms]
  · rw [Nat.cast_sub hct]
    change m ≤ _
    linarith only [hdt, ht, hmt]

end OTSelector.Reconstruction
