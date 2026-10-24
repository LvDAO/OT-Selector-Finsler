import OTSelector.Reconstruction.OriginalReserveMainExperimentCapacityEvents
import OTSelector.Reconstruction.OriginalReserveMainExperimentZeroBlocks
import OTSelector.Reconstruction.OriginalReserveRawPositiveBlockCapacity

/-! Real count fluctuations control literal deletion capacity on the unchanged original experiment. -/
open Set Function MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators Classical
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000
variable {q : ℕ} {α β : Measure ℝ} [IsProbabilityMeasure α] [IsProbabilityMeasure β]
  {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}

/-- The actual capacity failure is contained almost surely in real
positive-block count failures and the actual summed discrepancy event. The
zero law blocks have zero actual requests, proved internally on the same law. -/
theorem LegalWeightedStationaryPoissonMatching.ae_originalMainReserve_capacityFailure_subset
    (Q : LegalWeightedStationaryPoissonMatching q α β kin g)
    (b : OrthonormalBasis (Fin q) ℝ (EuclideanSpace ℝ (Fin q)))
    {θ R : ℝ} (hθ : 0 ≤ θ) (G : OriginalStageClockGrid) :
    ∀ᵐ p ∂originalMainReserveExperimentLaw Q
      (Real.toNNReal θ * (volume (originalCenteredPhysicalCubeRegion b (2 * R))).toNNReal),
      p ∈ originalMainReserveClockSlabCapacityFailure α β b R G →
      p ∈ {p | p.2 ∈ originalRawReservePositiveBlockExtremeFailure α β b θ R G} ∪
        originalMainReservePositiveBlockDiscrepancyFailure α β b θ R G := by
  have hzero : ∀ᵐ p ∂originalMainReserveExperimentLaw Q
      (Real.toNNReal θ * (volume (originalCenteredPhysicalCubeRegion b (2 * R))).toNNReal),
      ∀ block : G.ClockSlabBlock α β, block ∉ G.positiveSlabBlocks α β →
        originalReserveBlockExcess (originalCenteredPhysicalCubeRegion b (2 * R)) 0 1
          (G.sourceBlockCell α β block) (G.targetBlockCell α β block)
          (originalReserveExcessInputAux (originalSourceReserveExperimentSplice p)) = 0 ∧
        originalReserveBlockExcess (originalCenteredPhysicalCubeRegion b (2 * R)) 1 0
          (G.targetBlockCell α β block) (G.sourceBlockCell α β block)
          (originalReserveExcessInputAux (originalTargetReserveExperimentSplice p)) = 0 := by
    apply ae_all_iff.mpr
    intro block
    by_cases hb : block ∈ G.positiveSlabBlocks α β
    · exact Filter.Eventually.of_forall (fun _ hn ↦ False.elim (hn hb))
    · filter_upwards [Q.ae_originalReserveZeroClockBlock_excess
        (Real.toNNReal θ * (volume (originalCenteredPhysicalCubeRegion b (2 * R))).toNNReal)
        b R G block hb] with p hp
      exact fun _ ↦ hp
  filter_upwards [hzero] with p hz
  rintro ⟨block, hfail⟩
  by_cases hb : block ∈ G.positiveSlabBlocks α β
  · by_contra hn
    have hs : θ * volume.real (originalCenteredPhysicalCubeRegion b (2 * R)) *
        α.real (G.sourceCell (G.firstBlockClass block)) / 2 ≤
        (originalReserveBlockCount p.2.1.1 (fun i ↦ (p.2.1.2 i).2)
          (G.sourceCell (G.firstBlockClass block)) : ℝ) := by
      by_contra hc
      exact hn (Or.inl ⟨block, hb, Or.inl (lt_of_not_ge hc)⟩)
    have ht : θ * volume.real (originalCenteredPhysicalCubeRegion b (2 * R)) *
        β.real (G.targetCell (G.lastBlockClass block)) / 2 ≤
        (originalReserveBlockCount p.2.2.1 (fun i ↦ (p.2.2.2 i).2)
          (G.targetCell (G.lastBlockClass block)) : ℝ) := by
      by_contra hc
      exact hn (Or.inl ⟨block, hb, Or.inr (lt_of_not_ge hc)⟩)
    have hd : originalFullClockSlabDiscrepancy (α := α) (β := β) G
        (originalCenteredPhysicalCubeRegion b (2 * R)) p ≤
        (θ * min (α.real (G.sourceCell (G.firstBlockClass block)))
          (β.real (G.targetCell (G.lastBlockClass block))) / 4) *
            volume.real (originalCenteredPhysicalCubeRegion b (2 * R)) := by
      by_contra hc
      exact hn (Or.inr ⟨block, hb, lt_of_not_ge hc⟩)
    have hc := originalMainReserveClockBlock_capacity_and_slack_of_goodCounts
      α β b hθ G block p hs ht hd
    rcases hfail with hsbad | htbad
    · exact (Nat.not_lt_of_ge hc.1) hsbad
    · exact (Nat.not_lt_of_ge hc.2.1) htbad
  · have hz' := hz block hb
    rcases hfail with hsbad | htbad
    · rw [hz'.1] at hsbad
      exact False.elim (Nat.not_lt_zero _ hsbad)
    · rw [hz'.2] at htbad
      exact False.elim (Nat.not_lt_zero _ htbad)

end OTSelector.Reconstruction
