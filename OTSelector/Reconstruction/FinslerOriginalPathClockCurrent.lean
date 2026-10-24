import OTSelector.Reconstruction.FinslerOriginalPathMeasurability
import OTSelector.Reconstruction.MarkedStationaryValueLegalOriginalPathWindowReadout

/-!
# Actual path-position localized clock current

This is the literal complete original path current observed in a physical unit window.
Its mean equals the already centered original clock occupation mean for every genuine law,
including each genuine invariant-conditioned law used downstream.
-/

open Set Function Filter MeasureTheory Matrix Module Manifold
open scoped ENNReal NNReal ContDiff Matrix.Norms.Operator

noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Geometry ContinuousFinslerNorm OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
set_option linter.unusedSectionVars false

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}

/-- The actual same-scene path current in the physical unit cube at original clock c. -/
def originalSeedPathClockCurrent (S : CalibratedLevelSeedPatch F u) (w : S.covector.ker)
    (c : ℝ) : LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker) →
      Fin (finrank ℝ S.covector.ker) → ℝ :=
  legalMarkedPathWindowReadout (finrank ℝ S.covector.ker) (originalSeedPathOffset S w c)
    (legalMarkedUnitWindowWeight (finrank ℝ S.covector.ker)) (originalSeedClockOccupation S w c)

/-- The observation is at the actual path position, and its weight is the unchanged original
clock occupation velocity on that same edge. -/
theorem originalSeedPathClockCurrent_eq_pathLocalizedKernel
    (S : CalibratedLevelSeedPatch F u) (w : S.covector.ker) (c : ℝ)
    (s : LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker)) :
    originalSeedPathClockCurrent S w c s =
      ∫ p, (palmUnitCube (Fin (finrank ℝ S.covector.ker))).indicator
        (fun _ ↦ originalSeedClockOccupation S w c p.2)
        (originalSeedCompletePath S w p.1 p.2 c) ∂physicalScenePairKernel s.1 := by
  apply integral_congr_ae
  filter_upwards [] with p
  rw [originalSeedCompletePath_eq_anchor_add_offset]
  change (palmUnitCube (Fin (finrank ℝ S.covector.ker))).indicator (fun _ ↦ (1 : ℝ))
      (p.1 + originalSeedPathOffset S w c p.2) • originalSeedClockOccupation S w c p.2 = _
  by_cases hp : p.1 + originalSeedPathOffset S w c p.2 ∈
      palmUnitCube (Fin (finrank ℝ S.covector.ker)) <;> simp [hp]

namespace OriginalSeedConditionalMoments
variable {S : CalibratedLevelSeedPatch F u} {w : S.covector.ker} {μ ν : Measure ℝ}
  (D : OriginalSeedConditionalMoments S w μ ν)

/-- Actual path-window clock current is integrable and has exactly the same true Palm mean
as the original source-window clock occupation. -/
theorem original_pathClockCurrent_integrable_and_integral
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {gap diameter : ℝ} (hgap : 0 < gap)
    (hbounds : ConditionalClockSupportBounds μ ν gap diameter) {g : ℝ → ℝ → ℝ}
    (Q : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν
      (D.originalFocalKinetic gap) g) (c : ℝ) :
    Integrable (originalSeedPathClockCurrent S w c)
        (Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))) ∧
      (∫ s, originalSeedPathClockCurrent S w c s
        ∂(Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker)))) =
        ∫ m, originalSeedClockOccupation S w c m
          ∂legalMarkedJointPalm (finrank ℝ S.covector.ker) Q.law := by
  obtain ⟨hi, he⟩ := Q.pathWindowReadout_integrable_and_integral
    (originalSeedPathOffset S w c) (measurable_originalSeedPathOffset S hF hw c)
    (integrable_legalMarkedUnitWindowWeight _) (D.integrable_original_clockOccupation
      hF hw hgap hbounds Q c)
  refine ⟨hi, ?_⟩
  change (∫ s, legalMarkedPathWindowReadout (finrank ℝ S.covector.ker)
    (originalSeedPathOffset S w c) (legalMarkedUnitWindowWeight (finrank ℝ S.covector.ker))
    (originalSeedClockOccupation S w c) s ∂(Q.law : Measure _)) = _
  simpa only [integral_legalMarkedUnitWindowWeight, one_smul] using he

/-- Every actual original weighted minimizer has zero mean literal path-position clock
current. This follows from its actual minimality; no centering assumption is supplied. -/
theorem integral_original_pathClockCurrent_eq_zero_of_minimal_value
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {gap diameter : ℝ} (hgap : 0 < gap)
    (hbounds : ConditionalClockSupportBounds μ ν gap diameter) {g : ℝ → ℝ → ℝ}
    (Q : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν
      (D.originalFocalKinetic gap) g) (t : ℝ)
    (hmin : ∀ R : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν
      (D.originalFocalKinetic gap) g, Q.value t ≤ R.value t) (c : ℝ) :
    (∫ s, originalSeedPathClockCurrent S w c s
      ∂(Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker)))) = 0 := by
  rw [(D.original_pathClockCurrent_integrable_and_integral hF hw hgap hbounds Q c).2]
  exact D.integral_original_clockOccupation_eq_zero_of_minimal_value hF hw hgap hbounds Q t hmin c

end OriginalSeedConditionalMoments
end OTSelector.Reconstruction
