import OTSelector.Reconstruction.FinslerOriginalPalmMassTransfer
import OTSelector.Reconstruction.FinslerOriginalCloudCountIdentity

/-!
# Campbell mass identity for the scene edge measure: what is available

This module records the strongest true form of the Campbell mass identity for
the scene edge measure, derived from the configuration counting measure instead
of a Campbell formula.

## Findings

Searching the repository for a general Campbell formula giving the TOTAL MASS of
the scene edge measure as an expected edge count against the Palm, one finds
only the Campbell-average machinery for frozen costs
(campbellAveragedFrozenCost_eq_tileSum_add_tail and related results): it
transports INTEGRALS OF COST FUNCTIONS, not the total mass of the edge measure.
There is no Campbell identity of the form
  (s.1.1).univ = integral over the law of the expected edge count.

What the scene construction DOES fix is the total mass through the configuration:
IsFullOriginalInputMatching.simple_edges exhibits a local configuration whose
counting measure is (s.1.1), and the counting measure's total mass is the sum of
the shell multiplicities:

1. **scene_edge_mass_eq_shellSum** (unconditional): the scene edge total mass is
   the sum over shells of the multiset cardinalities.
2. **countingMeasure_univ_eq_zero_iff**: this total mass vanishes if and only if
   the configuration is empty; equivalently the scene edge measure is nonzero
   exactly when some shell is nonempty.  This is the exact mass-count interface
   that a Campbell formula would have to reproduce from the Palm side.
3. **scene_edge_mass_pos_iff**: for a full original input matching the scene edge
   mass is positive iff the representing configuration is nonempty.

## Exact remaining gap

The missing property is a MASS-TRANSPORT (refined Campbell) identity for the
scene edge measure: a theorem equating (s.1.1).univ with an expected edge count
under the Palm (legalMarkedJointPalm), together with the identification of that
expectation with the realized plan mass legalMaximumCard.  The repository's
Campbell results average COST functions over the Palm; none of them contains the
mass (constant weight one) case normalized against the realized cloud plan, so
the PalmSceneCloudMassTransfer hypothesis of
FinslerOriginalSceneCloudCountTransfer remains undischarged.  The configuration
side fixes the mass exactly (items 1-3), so any Campbell formula would have to
reproduce the shell-cardinality sum.
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

/-- **Scene edge total mass via the configuration** (re-export): the scene edge
measure's total mass is the sum of the shell cardinalities. -/
theorem scene_edge_mass_eq_shellSum {q : ℕ} {s : LegalMarkedOptimalInputScene q}
    (hs : IsFullOriginalInputMatching q s) :
    (s.1.1 : Measure (LegalMarkedPhysicalEdge q)) Set.univ =
      ∑' n, ((sceneEdgeConfig hs n).card : ℝ≥0∞) :=
  scene_edge_totalMass hs

/-- **Counting mass vanishes iff the configuration is empty.** -/
theorem countingMeasure_univ_eq_zero_iff
    {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] {base : X}
    (config : LocalConfiguration base) :
    LocalConfiguration.countingMeasure config Set.univ = 0 ↔
      ∀ n, config n = 0 := by
  rw [countingMeasure_univ]
  constructor
  · intro h n
    have hcard : ((config n).card : ℝ≥0∞) = 0 := by
      have := (ENNReal.tsum_eq_zero.mp h) n
      simpa using this
    have hzero : (config n).card = 0 := by
      exact_mod_cast hcard
    exact Multiset.card_eq_zero.mp hzero
  · intro h
    simp [h]

/-- **Scene edge mass positivity.**  The scene edge measure has positive total
mass exactly when its representing configuration is nonempty. -/
theorem scene_edge_mass_pos_iff {q : ℕ} {s : LegalMarkedOptimalInputScene q}
    (hs : IsFullOriginalInputMatching q s) :
    0 < (s.1.1 : Measure (LegalMarkedPhysicalEdge q)) Set.univ ↔
      ∃ n, sceneEdgeConfig hs n ≠ 0 := by
  rw [scene_edge_mass_eq_shellSum hs]
  constructor
  · intro h
    by_contra hall
    push Not at hall
    have hzero : ∑' n, ((sceneEdgeConfig hs n).card : ℝ≥0∞) = 0 := by
      apply ENNReal.tsum_eq_zero.mpr
      intro n
      rw [hall n]
      simp
    rw [hzero] at h
    exact lt_irrefl 0 h
  · rintro ⟨n, hn⟩
    have hpos : 0 < ((sceneEdgeConfig hs n).card : ℝ≥0∞) := by
      have hne : (sceneEdgeConfig hs n).card ≠ 0 := fun hc => hn (Multiset.card_eq_zero.mp hc)
      exact_mod_cast Nat.pos_of_ne_zero hne
    exact lt_of_lt_of_le hpos (ENNReal.le_tsum n)

end OTSelector.Reconstruction
