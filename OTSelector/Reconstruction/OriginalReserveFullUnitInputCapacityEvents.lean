import OTSelector.Reconstruction.OriginalReserveFullUnitInputBlockCapacity
import OTSelector.Reconstruction.OriginalReserveFullUnitInputZeroBlocks

/-! The actual block deletion-capacity event follows from real counts on the same full experiment. -/
open Set Function MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators Classical
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

/-- A positive-block original extreme class falls below its true half-mean. -/
def originalReservePositiveBlockExtremeFailure {q : ℕ} (α β : Measure ℝ)
    (b : OrthonormalBasis (Fin q) ℝ (EuclideanSpace ℝ (Fin q))) (θ R : ℝ)
    (G : OriginalStageClockGrid) : Set (OriginalReserveUnitExperimentSpace q × TwoMarkedCloudSpace q ℝ ℝ) :=
  {p | ∃ block : G.ClockSlabBlock α β, block ∈ G.positiveSlabBlocks α β ∧
    ((originalReserveBlockCount p.1.2.2.1.1 (fun i ↦ (p.1.2.2.1.2 i).2)
        (G.sourceCell (G.firstBlockClass block)) : ℝ) <
      θ * volume.real (originalCenteredPhysicalCubeRegion b (2 * R)) *
        α.real (G.sourceCell (G.firstBlockClass block)) / 2 ∨
    (originalReserveBlockCount p.1.2.2.2.1 (fun i ↦ (p.1.2.2.2.2 i).2)
        (G.targetCell (G.lastBlockClass block)) : ℝ) <
      θ * volume.real (originalCenteredPhysicalCubeRegion b (2 * R)) *
        β.real (G.targetCell (G.lastBlockClass block)) / 2)}

/-- The same original unit-block imbalance exceeds its actual quarter-mean reserve slack. -/
def originalReservePositiveBlockDeviationFailure {q : ℕ} (α β : Measure ℝ)
    (b : OrthonormalBasis (Fin q) ℝ (EuclideanSpace ℝ (Fin q)))
    (θ : ℝ) (hθ : 0 < θ) (hθ1 : θ < 1) (R : ℝ) (G : OriginalStageClockGrid) :
    Set (OriginalReserveUnitExperimentSpace q × TwoMarkedCloudSpace q ℝ ℝ) :=
  {p | ∃ block : G.ClockSlabBlock α β, block ∈ G.positiveSlabBlocks α β ∧
    (θ * min (α.real (G.sourceCell (G.firstBlockClass block)))
      (β.real (G.targetCell (G.lastBlockClass block))) / 4) *
        volume.real (originalCenteredPhysicalCubeRegion b (2 * R)) <
      |(originalMainPhysicalBlockCount (originalCenteredPhysicalCubeRegion b (2 * R))
          (G.sourceBlockCell α β block) 0 (originalReserveUnitInputReadout q θ hθ hθ1 p.1) : ℝ) -
        (originalMainPhysicalBlockCount (originalCenteredPhysicalCubeRegion b (2 * R))
          (G.targetBlockCell α β block) 1 (originalReserveUnitInputReadout q θ hθ hθ1 p.1) : ℝ)|}

/-- This event is the literal failure of either original blockwise deletion
capacity, including every zero block. It reads actual original Nat counts. -/
def originalReserveClockSlabCapacityFailure {q : ℕ} (α β : Measure ℝ)
    (b : OrthonormalBasis (Fin q) ℝ (EuclideanSpace ℝ (Fin q)))
    (θ : ℝ) (hθ1 : θ < 1) (R : ℝ) (G : OriginalStageClockGrid) :
    Set (OriginalReserveUnitExperimentSpace q × TwoMarkedCloudSpace q ℝ ℝ) :=
  {p | ∃ block : G.ClockSlabBlock α β,
    originalReserveBlockCount p.1.2.2.1.1 (fun i ↦ (p.1.2.2.1.2 i).2)
        (G.sourceCell (G.firstBlockClass block)) <
      originalReserveBlockExcess (originalCenteredPhysicalCubeRegion b (2 * R)) 0 1
        (G.sourceBlockCell α β block) (G.targetBlockCell α β block)
        (originalReserveExcessInputAux (originalReserveUnitSourceSamplerView q θ hθ1 p)) ∨
    originalReserveBlockCount p.1.2.2.2.1 (fun i ↦ (p.1.2.2.2.2 i).2)
        (G.targetCell (G.lastBlockClass block)) <
      originalReserveBlockExcess (originalCenteredPhysicalCubeRegion b (2 * R)) 1 0
        (G.targetBlockCell α β block) (G.sourceBlockCell α β block)
        (originalReserveExcessInputAux (originalReserveUnitTargetSamplerView q θ hθ1 p))}

/-- The true capacity failure event is measurable before conditioning on any selected positions. -/
theorem measurableSet_originalReserveClockSlabCapacityFailure {q : ℕ} (α β : Measure ℝ)
    (b : OrthonormalBasis (Fin q) ℝ (EuclideanSpace ℝ (Fin q)))
    (θ : ℝ) (hθ1 : θ < 1) (R : ℝ) (G : OriginalStageClockGrid) :
    MeasurableSet (originalReserveClockSlabCapacityFailure α β b θ hθ1 R G) := by
  have haux : Measurable (originalReserveExcessInputAux (q := q)) := by
    unfold originalReserveExcessInputAux
    fun_prop
  have h (block : G.ClockSlabBlock α β) : MeasurableSet
      {p : OriginalReserveUnitExperimentSpace q × TwoMarkedCloudSpace q ℝ ℝ |
        originalReserveBlockCount p.1.2.2.1.1 (fun i ↦ (p.1.2.2.1.2 i).2)
          (G.sourceCell (G.firstBlockClass block)) <
        originalReserveBlockExcess (originalCenteredPhysicalCubeRegion b (2 * R)) 0 1
          (G.sourceBlockCell α β block) (G.targetBlockCell α β block)
          (originalReserveExcessInputAux (originalReserveUnitSourceSamplerView q θ hθ1 p)) ∨
        originalReserveBlockCount p.1.2.2.2.1 (fun i ↦ (p.1.2.2.2.2 i).2)
          (G.targetCell (G.lastBlockClass block)) <
        originalReserveBlockExcess (originalCenteredPhysicalCubeRegion b (2 * R)) 1 0
          (G.targetBlockCell α β block) (G.sourceBlockCell α β block)
          (originalReserveExcessInputAux (originalReserveUnitTargetSamplerView q θ hθ1 p))} := by
    apply MeasurableSet.union
    · exact measurableSet_lt
        (measurable_originalReserveBlockCount (by fun_prop) (by fun_prop) measurableSet_Ico)
        ((measurable_originalReserveBlockExcess (measurableSet_originalOrientedTraffic_cube b R)
          0 1 (G.blockCells_measurable block).1 (G.blockCells_measurable block).2).comp
          (haux.comp (measurable_originalReserveUnitSourceSamplerView q θ hθ1)))
    · exact measurableSet_lt
        (measurable_originalReserveBlockCount (by fun_prop) (by fun_prop) measurableSet_Ioc)
        ((measurable_originalReserveBlockExcess (measurableSet_originalOrientedTraffic_cube b R)
          1 0 (G.blockCells_measurable block).2 (G.blockCells_measurable block).1).comp
          (haux.comp (measurable_originalReserveUnitTargetSamplerView q θ hθ1)))
  simpa only [originalReserveClockSlabCapacityFailure, Set.ofPred_exists] using MeasurableSet.iUnion h

namespace OriginalReserveFullUnitInputExperiment
variable {q : ℕ} {α β : Measure ℝ} [IsProbabilityMeasure α] [IsProbabilityMeasure β]
  {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
  {Main Reserve : LegalWeightedStationaryPoissonMatching q α β kin g}
  {b : OrthonormalBasis (Fin q) ℝ (EuclideanSpace ℝ (Fin q))}
  {θ R : ℝ} {hθ : 0 < θ} {hθ1 : θ < 1}
  (X : OriginalReserveFullUnitInputExperiment Main Reserve b θ hθ hθ1 R)

/-- True count identities, zero-block laws and real positive-block count good
events internally imply all requested original deletion capacities. -/
theorem ae_capacityFailure_subset (hq : 0 < q) (G : OriginalStageClockGrid) :
    ∀ᵐ p ∂(X.fullLaw : Measure (OriginalReserveUnitExperimentSpace q × TwoMarkedCloudSpace q ℝ ℝ)),
      p ∈ originalReserveClockSlabCapacityFailure α β b θ hθ1 R G →
      p ∈ originalReservePositiveBlockExtremeFailure α β b θ R G ∪
        originalReservePositiveBlockDeviationFailure α β b θ hθ hθ1 R G := by
  have hgood := ae_all_iff.mpr (fun block : G.ClockSlabBlock α β ↦
    X.ae_blockCapacity_of_goodCounts G block)
  have hzero : ∀ᵐ p ∂(X.fullLaw : Measure (OriginalReserveUnitExperimentSpace q × TwoMarkedCloudSpace q ℝ ℝ)),
      ∀ block : G.ClockSlabBlock α β, block ∉ G.positiveSlabBlocks α β →
        originalReserveBlockExcess (originalCenteredPhysicalCubeRegion b (2 * R)) 0 1
          (G.sourceBlockCell α β block) (G.targetBlockCell α β block)
          (originalReserveExcessInputAux (originalReserveUnitSourceSamplerView q θ hθ1 p)) = 0 ∧
        originalReserveBlockExcess (originalCenteredPhysicalCubeRegion b (2 * R)) 1 0
          (G.targetBlockCell α β block) (G.sourceBlockCell α β block)
          (originalReserveExcessInputAux (originalReserveUnitTargetSamplerView q θ hθ1 p)) = 0 := by
    apply ae_all_iff.mpr
    intro block
    by_cases hb : block ∈ G.positiveSlabBlocks α β
    · exact Filter.Eventually.of_forall (fun _ hn ↦ False.elim (hn hb))
    · filter_upwards [X.ae_zeroClockSlabBlock_excess hq G block hb] with p hp
      exact fun _ ↦ hp
  filter_upwards [hgood, hzero] with p hg hz
  rintro ⟨block, hfail⟩
  by_cases hb : block ∈ G.positiveSlabBlocks α β
  · by_contra hn
    have hs : θ * volume.real (originalCenteredPhysicalCubeRegion b (2 * R)) *
        α.real (G.sourceCell (G.firstBlockClass block)) / 2 ≤
        (originalReserveBlockCount p.1.2.2.1.1 (fun i ↦ (p.1.2.2.1.2 i).2)
          (G.sourceCell (G.firstBlockClass block)) : ℝ) := by
      by_contra hc
      exact hn (Or.inl ⟨block, hb, Or.inl (lt_of_not_ge hc)⟩)
    have ht : θ * volume.real (originalCenteredPhysicalCubeRegion b (2 * R)) *
        β.real (G.targetCell (G.lastBlockClass block)) / 2 ≤
        (originalReserveBlockCount p.1.2.2.2.1 (fun i ↦ (p.1.2.2.2.2 i).2)
          (G.targetCell (G.lastBlockClass block)) : ℝ) := by
      by_contra hc
      exact hn (Or.inl ⟨block, hb, Or.inr (lt_of_not_ge hc)⟩)
    have hd : |(originalMainPhysicalBlockCount (originalCenteredPhysicalCubeRegion b (2 * R))
          (G.sourceBlockCell α β block) 0 (originalReserveUnitInputReadout q θ hθ hθ1 p.1) : ℝ) -
        (originalMainPhysicalBlockCount (originalCenteredPhysicalCubeRegion b (2 * R))
          (G.targetBlockCell α β block) 1 (originalReserveUnitInputReadout q θ hθ hθ1 p.1) : ℝ)| ≤
      (θ * min (α.real (G.sourceCell (G.firstBlockClass block)))
        (β.real (G.targetCell (G.lastBlockClass block))) / 4) *
        volume.real (originalCenteredPhysicalCubeRegion b (2 * R)) := by
      by_contra hc
      exact hn (Or.inr ⟨block, hb, lt_of_not_ge hc⟩)
    have hc := hg block hs ht hd
    rcases hfail with hsbad | htbad
    · exact (Nat.not_lt_of_ge hc.1) hsbad
    · exact (Nat.not_lt_of_ge hc.2.1) htbad
  · have hz' := hz block hb
    rcases hfail with hsbad | htbad
    · rw [hz'.1] at hsbad
      exact False.elim (Nat.not_lt_zero _ hsbad)
    · rw [hz'.2] at htbad
      exact False.elim (Nat.not_lt_zero _ htbad)

end OriginalReserveFullUnitInputExperiment
end OTSelector.Reconstruction
