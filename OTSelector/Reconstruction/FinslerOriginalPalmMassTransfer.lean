import OTSelector.Reconstruction.FinslerOriginalSceneCloudCountTransfer
import OTSelector.Reconstruction.MarkedStationaryValueLegalStationaryPoissonCandidate

/-!
# What the Palm construction transfers: probability, not scene edge mass

This module audits the Palm construction against the missing
PalmSceneCloudMassTransfer hypothesis of
FinslerOriginalSceneCloudCountTransfer.lean.

## Findings

The actual source-anchored Palm is

  legalMarkedJointPalm q Q = cubePalm (Fin q) (physicalScenePairCampbell (legalMarkedInputPairLaw q Q)),

a measure on the Palm marks PhysicalPairPalmMark (Fin q) = (clock pair,
displacement).  The Palm construction transfers:

1. **PROBABILITY** (not mass): palm_probability gives
   IsProbabilityMeasure (legalMarkedJointPalm q M.law), hence its total mass is
   one (**palm_totalMass_one**);
2. **the endpoint clock laws**: the Palm pushes forward to the prescribed
   source/target laws alpha, beta (**palm_source_clock_map**,
   **palm_target_clock_map**).

It does NOT transfer the scene edge measure's total mass: the scene edge measure
(s.1.1) lives on LegalMarkedPhysicalEdge q, a different space from the Palm
marks, and the Palm fields contain no normalization or Campbell identity linking
its total mass to the cloud plan mass.  The missing property is exactly a
MASS-TRANSPORT (Campbell/refined-Palm) identity for the scene edge measure: a
theorem of the form (s.1.1).univ = integral of the expected edge count against
the Palm, together with the identification of that expectation with the realized
plan mass.  The Palm modules provide probability transport only.

## Conditional chain

**scene_totalMass_eq_legalMaximumCard_of_palm_mass_transfer** wires the (still
hypothetical) mass-transport identity into the scene count chain: if
(s.1.1).univ = (legalMarkedOptimalPlan ...).univ, then the scene shell
cardinality sum equals the legal maximum cardinality of the realized legal
graph - the number of matched pairs.

## Palm count equality

The Palm marks carry no count coordinates at all (they are clock pairs and
displacements), so mSourceCount = mTargetCount on the rooted event is not
definitional there; it would require a separate statement in the cloud
construction.
-/

open Set Function MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace
open OTSelector.Probability OTSelector.PointProcess
open scoped ENNReal NNReal BigOperators

noncomputable section
namespace OTSelector.Reconstruction

set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

/-- **The Palm is a probability: its total mass is one.** -/
theorem palm_totalMass_one {q : ℕ} {α β : Measure ℝ}
    {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (M : LegalWeightedStationaryPoissonMatching q α β kin g) :
    (legalMarkedJointPalm q M.law) Set.univ = 1 := by
  haveI := M.palm_probability
  simp

/-- **The Palm transports the source clock law.** -/
theorem palm_source_clock_map {q : ℕ} {α β : Measure ℝ}
    {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (M : LegalWeightedStationaryPoissonMatching q α β kin g) :
    (legalMarkedJointPalm q M.law).map (fun m => m.1.1) = α :=
  M.source_clock

/-- **The Palm transports the target clock law.** -/
theorem palm_target_clock_map {q : ℕ} {α β : Measure ℝ}
    {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (M : LegalWeightedStationaryPoissonMatching q α β kin g) :
    (legalMarkedJointPalm q M.law).map (fun m => m.1.2) = β :=
  M.target_clock

/-- **The Palm transports probability to the source clock:** the pushed-forward
source clock law has total mass one (probability transport, not mass transport
of the scene edge measure). -/
theorem palm_source_clock_totalMass_one {q : ℕ} {α β : Measure ℝ}
    {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (M : LegalWeightedStationaryPoissonMatching q α β kin g) :
    α Set.univ = 1 := by
  haveI := M.palm_probability
  rw [← palm_source_clock_map M, Measure.map_apply measurable_fst.fst
    MeasurableSet.univ]
  simp

/-- **Conditional count chain via a Palm mass-transport identity.**  If the
scene edge total mass equals the realized cloud plan total mass, the scene shell
cardinality sum equals the legal maximum cardinality of the realized legal graph
(the number of matched pairs). -/
theorem scene_totalMass_eq_legalMaximumCard_of_palm_mass_transfer
    {q : ℕ} {s : LegalMarkedOptimalInputScene q}
    (hs : IsFullOriginalInputMatching q s) (ω : TwoMarkedCloudSpace q ℝ ℝ)
    (L r : ℝ) (kin : ℝ → ℝ → (Fin q → ℝ) → ℝ) (g : ℝ → ℝ → ℝ) (t : ℝ)
    (hmass : PalmSceneCloudMassTransfer L r kin g t s ω) :
    (∑' n, ((sceneEdgeConfig hs n).card : ℝ≥0∞)) =
      ((PartialMatching.legalMaximumCard
        (legalMarkedGraph q (mSourceCount ω) (mTargetCount ω) id id ω) : ℕ) :
          ℝ≥0∞) := by
  rw [← scene_edge_totalMass hs]
  rw [hmass, legalMarkedOptimalPlan_univ]

end OTSelector.Reconstruction
