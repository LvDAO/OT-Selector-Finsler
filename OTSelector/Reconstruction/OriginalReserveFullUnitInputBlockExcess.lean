import OTSelector.Reconstruction.OriginalReserveFullUnitInputBlockCounts
import OTSelector.Reconstruction.OriginalReserveUnitInputClockBlockCounts
import OTSelector.Reconstruction.OriginalReserveFullUnitInputBlockSelection
import OTSelector.Reconstruction.OriginalMarkSelectedPopulationCouplingBlockExcessBudget

/-! Actual same-join block excess is read from the original unit-intensity input counts. -/
open Set Function MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators Classical
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
namespace OriginalReserveFullUnitInputExperiment
variable {q : ℕ} {α β : Measure ℝ} [IsProbabilityMeasure α] [IsProbabilityMeasure β]
  {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
  {Main Reserve : LegalWeightedStationaryPoissonMatching q α β kin g}
  {b : OrthonormalBasis (Fin q) ℝ (EuclideanSpace ℝ (Fin q))}
  {θ R : ℝ} {hθ : 0 < θ} {hθ1 : θ < 1}
  (X : OriginalReserveFullUnitInputExperiment Main Reserve b θ hθ hθ1 R)

/-- The actual main-plus-reserve block discrepancy equals the actual unit-input
block discrepancy on the same full joining. Full arrays only identify observations. -/
theorem ae_fullBlockDiscrepancy_eq_unit {S T : Set ℝ} (hS : MeasurableSet S) (hT : MeasurableSet T) :
    ∀ᵐ p ∂(X.fullLaw : Measure (OriginalReserveUnitExperimentSpace q × TwoMarkedCloudSpace q ℝ ℝ)),
      originalFullBlockDiscrepancy (originalCenteredPhysicalCubeRegion b (2 * R)) S T
        (originalReserveMainSamplerReadout q θ hθ1 p.1) =
      |(originalMainPhysicalBlockCount (originalCenteredPhysicalCubeRegion b (2 * R)) S 0
          (originalReserveUnitInputReadout q θ hθ hθ1 p.1) : ℝ) -
        (originalMainPhysicalBlockCount (originalCenteredPhysicalCubeRegion b (2 * R)) T 1
          (originalReserveUnitInputReadout q θ hθ hθ1 p.1) : ℝ)| := by
  filter_upwards [X.ae_clockBlock_counts hS, X.ae_clockBlock_counts hT] with p hs ht
  have hs' := (hs 0).2
  have ht' := (ht 1).2
  simp only [↓reduceIte] at hs'
  simp only [one_ne_zero, ↓reduceIte] at ht'
  rw [hs', ht', Nat.cast_add, Nat.cast_add]
  simp only [originalFullBlockDiscrepancy, originalReserveObservedBlockCount_eq_natCount]
  rfl

/-- Actual blockwise deletion requests exactly the same unit-input discrepancy;
no successful deletion, capacity or preexisting balance is assumed. -/
theorem ae_blockRequestedExcess_eq_unit {S T : Set ℝ} (hS : MeasurableSet S) (hT : MeasurableSet T) :
    ∀ᵐ p ∂(X.fullLaw : Measure (OriginalReserveUnitExperimentSpace q × TwoMarkedCloudSpace q ℝ ℝ)),
      (originalReserveBlockExcess (originalCenteredPhysicalCubeRegion b (2 * R)) 0 1 S T
        (originalReserveExcessInputAux (originalReserveUnitSourceSamplerView q θ hθ1 p)) : ℝ) +
      (originalReserveBlockExcess (originalCenteredPhysicalCubeRegion b (2 * R)) 1 0 T S
        (originalReserveExcessInputAux (originalReserveUnitTargetSamplerView q θ hθ1 p)) : ℝ) =
      |(originalMainPhysicalBlockCount (originalCenteredPhysicalCubeRegion b (2 * R)) S 0
          (originalReserveUnitInputReadout q θ hθ hθ1 p.1) : ℝ) -
        (originalMainPhysicalBlockCount (originalCenteredPhysicalCubeRegion b (2 * R)) T 1
          (originalReserveUnitInputReadout q θ hθ hθ1 p.1) : ℝ)| := by
  filter_upwards [X.ae_fullBlockDiscrepancy_eq_unit hS hT] with p hp
  exact (originalReserveBlockExcess_sum_eq_fullDiscrepancy
    (originalCenteredPhysicalCubeRegion b (2 * R)) S T
    (originalReserveMainSamplerReadout q θ hθ1 p.1)).trans hp

/-- The true actual main-plus-reserve discrepancy has the sharp unit-intensity
square-root budget, including empty blocks and all surrounding correlations. -/
theorem fullBlockDiscrepancy_integrable_and_integral_le (hq : 0 < q)
    {S T : Set ℝ} (hS : MeasurableSet S) (hT : MeasurableSet T) (hbal : α S = β T) :
    Integrable (fun p : OriginalReserveUnitExperimentSpace q × TwoMarkedCloudSpace q ℝ ℝ ↦
      originalFullBlockDiscrepancy (originalCenteredPhysicalCubeRegion b (2 * R)) S T
        (originalReserveMainSamplerReadout q θ hθ1 p.1)) (X.fullLaw : Measure _) ∧
    (∫ p : OriginalReserveUnitExperimentSpace q × TwoMarkedCloudSpace q ℝ ℝ,
      originalFullBlockDiscrepancy (originalCenteredPhysicalCubeRegion b (2 * R)) S T
        (originalReserveMainSamplerReadout q θ hθ1 p.1) ∂(X.fullLaw : Measure _)) ≤
      Real.sqrt (2 * volume.real (originalCenteredPhysicalCubeRegion b (2 * R)) * α.real S) := by
  have h := X.unitBlock_discrepancy hq (isCompact_originalStagePhysicalCube b (2 * R)) hS hT hbal
  have heq :
      (fun p : OriginalReserveUnitExperimentSpace q × TwoMarkedCloudSpace q ℝ ℝ ↦
        originalFullBlockDiscrepancy (originalCenteredPhysicalCubeRegion b (2 * R)) S T
          (originalReserveMainSamplerReadout q θ hθ1 p.1)) =ᵐ[(X.fullLaw : Measure _)]
      (fun p ↦ |(originalMainPhysicalBlockCount (originalCenteredPhysicalCubeRegion b (2 * R)) S 0
          (originalReserveUnitInputReadout q θ hθ hθ1 p.1) : ℝ) -
        (originalMainPhysicalBlockCount (originalCenteredPhysicalCubeRegion b (2 * R)) T 1
          (originalReserveUnitInputReadout q θ hθ hθ1 p.1) : ℝ)|) :=
    X.ae_fullBlockDiscrepancy_eq_unit hS hT
  exact ⟨h.1.congr heq.symm, (integral_congr_ae heq).trans_le h.2⟩

end OriginalReserveFullUnitInputExperiment
end OTSelector.Reconstruction
