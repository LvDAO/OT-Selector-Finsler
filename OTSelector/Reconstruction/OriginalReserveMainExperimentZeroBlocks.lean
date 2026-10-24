import OTSelector.Reconstruction.OriginalMarkSelectedPopulationCouplingBlockExcessBudgetFailure

/-! Null law blocks request no deletions on the unchanged original main-plus-reserve experiment. -/
open Set Function MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators Classical
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
variable {q : ℕ} {α β : Measure ℝ} [IsProbabilityMeasure α] [IsProbabilityMeasure β]
  {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}

/-- Genuine zero law mass makes the nonnegative full discrepancy and both
actual original Nat-index deletion requests zero almost surely. -/
theorem LegalWeightedStationaryPoissonMatching.ae_originalReserveBlockExcess_zero_of_null
    (Q : LegalWeightedStationaryPoissonMatching q α β kin g) (rate : ℝ≥0)
    {K : Set (Fin q → ℝ)} (hK : IsCompact K) {S T : Set ℝ}
    (hS : MeasurableSet S) (hT : MeasurableSet T) (hα : α S = 0) (hβ : β T = 0) :
    ∀ᵐ p ∂originalMainReserveExperimentLaw Q rate,
      originalReserveBlockExcess K 0 1 S T
        (originalReserveExcessInputAux (originalSourceReserveExperimentSplice p)) = 0 ∧
      originalReserveBlockExcess K 1 0 T S
        (originalReserveExcessInputAux (originalTargetReserveExperimentSplice p)) = 0 := by
  have hb := Q.originalFullBlockDiscrepancy_integrable_and_integral_le rate hK hS hT
    (hα.trans hβ.symm)
  have hz : ∫ p, originalFullBlockDiscrepancy K S T p
      ∂originalMainReserveExperimentLaw Q rate = 0 := by
    apply le_antisymm
    · simpa only [measureReal_def, hα, ENNReal.toReal_zero, mul_zero,
        Real.sqrt_zero, zero_add] using hb.2
    · exact integral_nonneg fun _ ↦ abs_nonneg _
  have hnonneg : 0 ≤ᵐ[originalMainReserveExperimentLaw Q rate]
      (originalFullBlockDiscrepancy K S T) := ae_of_all _ (fun _ ↦ abs_nonneg _)
  have haz : originalFullBlockDiscrepancy K S T =ᵐ[originalMainReserveExperimentLaw Q rate] 0 :=
    (integral_eq_zero_iff_of_nonneg_ae hnonneg hb.1).mp hz
  filter_upwards [haz] with p hp
  have hs := originalReserveBlockExcess_sum_eq_fullDiscrepancy K S T p
  change originalFullBlockDiscrepancy K S T p = 0 at hp
  rw [hp] at hs
  have hsn : 0 ≤ (originalReserveBlockExcess K 0 1 S T
    (originalReserveExcessInputAux (originalSourceReserveExperimentSplice p)) : ℝ) :=
      Nat.cast_nonneg _
  have htn : 0 ≤ (originalReserveBlockExcess K 1 0 T S
    (originalReserveExcessInputAux (originalTargetReserveExperimentSplice p)) : ℝ) :=
      Nat.cast_nonneg _
  have hs0 : (originalReserveBlockExcess K 0 1 S T
      (originalReserveExcessInputAux (originalSourceReserveExperimentSplice p)) : ℝ) = 0 := by
    linarith only [hs, hsn, htn]
  have ht0 : (originalReserveBlockExcess K 1 0 T S
      (originalReserveExcessInputAux (originalTargetReserveExperimentSplice p)) : ℝ) = 0 := by
    linarith only [hs, hsn, htn]
  exact ⟨by exact_mod_cast hs0, by exact_mod_cast ht0⟩

/-- Discarded actual zero Hall blocks require no positive extreme class or
new bad event. All reserve intensities, including zero, are covered. -/
theorem LegalWeightedStationaryPoissonMatching.ae_originalReserveZeroClockBlock_excess
    (Q : LegalWeightedStationaryPoissonMatching q α β kin g) (rate : ℝ≥0)
    (b : OrthonormalBasis (Fin q) ℝ (EuclideanSpace ℝ (Fin q))) (R : ℝ)
    (G : OriginalStageClockGrid) (block : G.ClockSlabBlock α β)
    (hb : block ∉ G.positiveSlabBlocks α β) :
    ∀ᵐ p ∂originalMainReserveExperimentLaw Q rate,
      originalReserveBlockExcess (originalCenteredPhysicalCubeRegion b (2 * R)) 0 1
        (G.sourceBlockCell α β block) (G.targetBlockCell α β block)
        (originalReserveExcessInputAux (originalSourceReserveExperimentSplice p)) = 0 ∧
      originalReserveBlockExcess (originalCenteredPhysicalCubeRegion b (2 * R)) 1 0
        (G.targetBlockCell α β block) (G.sourceBlockCell α β block)
        (originalReserveExcessInputAux (originalTargetReserveExperimentSplice p)) = 0 :=
  Q.ae_originalReserveBlockExcess_zero_of_null rate
    (isCompact_originalStagePhysicalCube b (2 * R))
    (G.blockCells_measurable block).1 (G.blockCells_measurable block).2
    (Measure.restrict_eq_zero.mp (G.zeroSlabBlock_restrict block hb).1)
    (Measure.restrict_eq_zero.mp (G.zeroSlabBlock_restrict block hb).2)

end OTSelector.Reconstruction
