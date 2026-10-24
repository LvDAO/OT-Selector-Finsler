import OTSelector.Reconstruction.MarkedStationaryValueLegalGenuineWeakDomination
import OTSelector.Reconstruction.MarkedStationaryValueLegalOriginalInputSimplicity
import OTSelector.Reconstruction.MarkedStationaryValueLegalTruePalmIdentification
import OTSelector.Reconstruction.MarkedStationaryValueLegalOriginalMeanMarginalFullness
import OTSelector.Reconstruction.MarkedStationaryValueLegalTruePalmClockGap
import OTSelector.Reconstruction.MarkedStationaryValueLegalCanonicalInputCompactness
import OTSelector.Reconstruction.MarkedStationaryValueLegalCanonicalInputWeakReadout
import OTSelector.Reconstruction.MarkedStationaryValueLegalStationaryInputLawEquality

/-!
# Genuine matching closure for the same original scene and true Palm

The actual weak scene and its actual full-displacement probability Palm retain
whole matching marginals. Original Poisson simplicity and integer edge closure
recover a full original one-to-one matching, with its original energy and clocks.
-/
open Set Function MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace
open scoped ENNReal NNReal CompactlySupported Classical
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2600000
local instance markedStationaryValueLegalGenuineTruePalmClosureInputPolish (q : ℕ) : PolishSpace
    (LocalFiniteMeasure (LegalColoredInputPoint q)) := LocalFiniteMeasure.instPolishSpace
local instance markedStationaryValueLegalGenuineTruePalmClosurePlanPolish (q : ℕ) : PolishSpace
    (LocalFiniteMeasure (LegalMarkedPhysicalEdge q)) := LocalFiniteMeasure.instPolishSpace

/-- Actual same-sequence scene and probability-Palm limits produce a genuine
full matching. Whole marginals, simple inputs, all-support forwardness and
finite actual energy are established for this same scene, not postulated. -/
theorem exists_genuineStationary_of_scene_and_truePalm_weak
    {q : ℕ} (hq : 0 < q) {α β : Measure ℝ}
    [IsProbabilityMeasure α] [IsProbabilityMeasure β]
    {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (M : ℕ → LegalWeightedStationaryPoissonMatching q α β kin g)
    (Q : ProbabilityMeasure (LegalMarkedOptimalInputScene q))
    (hweak : Tendsto (fun n ↦ (M n).law) atTop (𝓝 Q))
    (η : ProbabilityMeasure (PhysicalPairPalmMark (Fin q)))
    (hPalm : Tendsto (fun n ↦ (M n).truePalmProbability) atTop (𝓝 η))
    (hsource : (η : Measure (PhysicalPairPalmMark (Fin q))).map (fun m ↦ m.1.1) = α)
    (htarget : (η : Measure (PhysicalPairPalmMark (Fin q))).map (fun m ↦ m.1.2) = β)
    {δ : ℝ} (hδ : 0 < δ)
    (hgap : ∀ᵐ m ∂(η : Measure (PhysicalPairPalmMark (Fin q))), δ ≤ m.1.2 - m.1.1)
    (hkin : Integrable (fun m ↦ kin m.1.1 m.1.2 m.2)
      (η : Measure (PhysicalPairPalmMark (Fin q))))
    (hg : Integrable (fun m ↦ g m.1.1 m.1.2)
      (η : Measure (PhysicalPairPalmMark (Fin q)))) :
    ∃ R : LegalWeightedStationaryPoissonMatching q α β kin g,
      R.law = Q ∧ legalMarkedJointPalm q R.law = (η : Measure (PhysicalPairPalmMark (Fin q))) := by
  have hstat := measurePreserving_reroot_of_genuineStationary_tendsto M hweak
  have hlap := input_laplace_of_genuineStationary_tendsto M hweak
  have hpalm := legalMarkedJointPalm_eq_of_genuineStationary_weak_of_truePalm_weak
    M Q hweak hstat η hPalm
  have hprob : IsProbabilityMeasure (legalMarkedJointPalm q Q) := by
    rw [hpalm]
    infer_instance
  have hinput := originalInputLaw_eq_of_compact_laplace_eq Q (M 0).law (by
    intro S hS F hF hzero
    rw [hlap S hS F hF hzero, (M 0).input_laplace S hS F hF hzero])
  have hmarg := ae_original_marginals_eq_input_of_truePalm_clock_marginals
    (M 0) Q hinput hstat hprob (by rw [hpalm]; exact hsource)
    (by rw [hpalm]; exact htarget)
    (ae_marginals_le_input_of_genuineStationary_tendsto M Q hweak)
  have hcount := ae_counting_of_genuineStationary_tendsto M hweak
  have hsimple := ae_originalInput_simple_of_laplace_of_counting hq Q hlap
    (hcount.mono (fun _ hs ↦ hs.2))
  have hfull : ∀ᵐ s ∂(Q : Measure (LegalMarkedOptimalInputScene q)),
      IsFullOriginalInputMatching q s := by
    filter_upwards [hcount, hsimple, hmarg] with s hc hs hm
    exact isFullOriginalInputMatching_of_counting_simple_marginals q s hc.1 hs hm
  have hforward := ae_support_clockGap_of_stationary_truePalm_gap Q hstat hprob
    (by rw [hpalm]; exact hgap)
  let R : LegalWeightedStationaryPoissonMatching q α β kin g := {
    law := Q
    stationary := hstat
    full_matching := hfull
    forward := hforward.mono (fun _ hs e he ↦ by linarith [hs e he])
    input_laplace := hlap
    palm_probability := hprob
    source_clock := by rw [hpalm]; exact hsource
    target_clock := by rw [hpalm]; exact htarget
    kinetic_integrable := by rw [hpalm]; exact hkin
    probe_integrable := by rw [hpalm]; exact hg }
  exact ⟨R, rfl, hpalm⟩

end OTSelector.Reconstruction
