import OTSelector.MeasureTheory.ContinuousTestCentering
import OTSelector.Reconstruction.MarkedStationaryValueLegalStationaryClockShiftCentering
import Mathlib.MeasureTheory.SpecificCodomains.Pi

/-! Actual Finsler minimizing laws have exact centered Borel-clock momenta. -/
open Set Function MeasureTheory Manifold Matrix Module
open scoped ContDiff
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability OTSelector.Geometry ContinuousFinslerNorm
set_option backward.isDefEq.respectTransparency false
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}

namespace OriginalSeedConditionalMoments
variable {S : CalibratedLevelSeedPatch F u} {w : S.covector.ker} {μ ν : Measure ℝ}
  (D : OriginalSeedConditionalMoments S w μ ν)

/-- Every component of the actual original momentum has zero integral over
any Borel source-clock or target-clock event of a minimizing original law.
The event may be a closed or strict prefix; no atomlessness is needed. -/
theorem setIntegral_original_momentum_clock_eq_zero_of_minimal_value
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {gap diameter : ℝ} (hgap : 0 < gap)
    (hbounds : ConditionalClockSupportBounds μ ν gap diameter)
    {g : ℝ → ℝ → ℝ}
    (Q : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν
      (D.originalFocalKinetic gap) g) (t : ℝ)
    (hmin : ∀ R : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν
      (D.originalFocalKinetic gap) g, Q.value t ≤ R.value t)
    (i : Fin (finrank ℝ S.covector.ker)) (B : Set ℝ) (hB : MeasurableSet B) :
    (∫ m in {m | m.1.1 ∈ B}, originalSeedPairMomentum S w m i
      ∂legalMarkedJointPalm (finrank ℝ S.covector.ker) Q.law) = 0 ∧
    (∫ m in {m | m.1.2 ∈ B}, originalSeedPairMomentum S w m i
      ∂legalMarkedJointPalm (finrank ℝ S.covector.ker) Q.law) = 0 := by
  have hi := (D.integrable_original_pair_momentum_of_weighted_stationary
    hF hw hgap hbounds Q).1.eval i
  constructor
  · exact setIntegral_preimage_eq_zero_of_continuous_tests
      (legalMarkedJointPalm (finrank ℝ S.covector.ker) Q.law)
      (fun m ↦ originalSeedPairMomentum S w m i) hi
      (fun m ↦ m.1.1) measurable_fst.fst
      (fun f ↦ (D.integral_momentum_clock_pairings_eq_zero_of_minimal_value
        hF hw hgap hbounds Q t hmin f i).1) B hB
  · exact setIntegral_preimage_eq_zero_of_continuous_tests
      (legalMarkedJointPalm (finrank ℝ S.covector.ker) Q.law)
      (fun m ↦ originalSeedPairMomentum S w m i) hi
      (fun m ↦ m.1.2) measurable_fst.snd
      (fun f ↦ (D.integral_momentum_clock_pairings_eq_zero_of_minimal_value
        hF hw hgap hbounds Q t hmin f i).2) B hB

end OriginalSeedConditionalMoments
end OTSelector.Reconstruction
