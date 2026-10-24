import OTSelector.Reconstruction.FinslerOriginalSceneCountIdentity
import OTSelector.Probability.MarkedPoissonCube

/-!
# Cloud count identity: total mass of the scene edge measure

This module provides the counting-mass interface needed for the cloud count
identity, and states the exact remaining bridge.

1. **sum_dirac_univ**: the total mass of a finite sum of Dirac masses over a
   finite index type is the cardinality of the index type.  This is the abstract
   content of "number of matched pairs = number of colour labels": the cloud
   plan of a cloud state is a finite sum of Diracs indexed by the matched pairs
   of Fin (mSourceCount) x Fin (mTargetCount).

2. **countingMeasure_univ**: the total mass of a configuration counting measure
   is the sum over shells of the multiset cardinalities.

3. **scene_edge_totalMass**: consequently the total mass of the scene edge
   measure is the shell-cardinality sum of its representing configuration
   (sceneEdgeConfig from the previous module).

## Exact remaining sub-gap

The identification with the CLOUD counts mSourceCount/mTargetCount still needs
the Palm correspondence: the cloud plan legalMarkedOptimalPlan q L (L^q) kin g t
omega is (by construction, cf. the finsetSum/dirac structure used in
MarkedStationaryValueLegalOptimalPalmSupport) a finite sum of Dirac masses
indexed by the matched pairs of Fin (mSourceCount omega) x Fin (mTargetCount
omega).  Chaining sum_dirac_univ with a full-matching cardinality statement
(mSourceCount = mTargetCount = number of matched pairs) would give the cloud
identity; the library has the full-matching cardinality facts only in the
MAXIMUM-cardinality form (legalMaximumCard), and the Palm field
palm_probability links the scene law to the cloud law only through Palm-square
probabilities, not through a cardinality-transport statement.  Hence the
scene-to-cloud count transfer is not derived here; the counting-mass interface
above is proved.
-/

open Set Function MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace
open OTSelector.Probability OTSelector.PointProcess
open scoped ENNReal NNReal BigOperators

noncomputable section
namespace OTSelector.Reconstruction

set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

/-- **Total mass of a finite sum of Dirac masses.** -/
theorem sum_dirac_univ {ι X : Type*} [MeasurableSpace X] [Fintype ι]
    (f : ι → X) :
    (∑ i, Measure.dirac (f i)) Set.univ = (Fintype.card ι : ℝ≥0∞) := by
  simp

/-- **Total mass of a configuration counting measure.** -/
theorem countingMeasure_univ
    {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] {base : X}
    (config : LocalConfiguration base) :
    LocalConfiguration.countingMeasure config Set.univ =
      ∑' n, ((config n).card : ℝ≥0∞) := by
  rw [LocalConfiguration.countingMeasure_apply config MeasurableSet.univ]
  congr 1
  funext n
  rw [LocalConfiguration.shellMeasure_apply config n MeasurableSet.univ]
  have hconst : (fun x : LocalConfiguration.Shell base n =>
      (Set.univ.indicator (fun _ => (1 : ℝ≥0∞))) x.val) =
      fun _ => (1 : ℝ≥0∞) := by
    funext x
    rw [Set.indicator_of_mem]
    exact mem_univ _
  rw [hconst]
  induction (config n) using Multiset.induction_on with
  | empty => simp
  | cons a m ih =>
      rw [Multiset.map_cons, Multiset.sum_cons, Multiset.card_cons, ih,
        Nat.cast_add, Nat.cast_one]
      exact add_comm _ _

/-- **Total mass of the scene edge measure.** -/
theorem scene_edge_totalMass {q : ℕ} {s : LegalMarkedOptimalInputScene q}
    (hs : IsFullOriginalInputMatching q s) :
    (s.1.1 : Measure (LegalMarkedPhysicalEdge q)) Set.univ =
      ∑' n, ((sceneEdgeConfig hs n).card : ℝ≥0∞) := by
  have hval : (s.1.1 : Measure (LegalMarkedPhysicalEdge q)) =
      LocalConfiguration.countingMeasure (sceneEdgeConfig hs) := by
    have h := congrArg
      (fun μ : LocalFiniteMeasure (LegalMarkedPhysicalEdge q) =>
        (μ : Measure (LegalMarkedPhysicalEdge q))) (sceneEdgeConfig_spec hs)
    rw [scene_toLocalFiniteMeasure_coe hs] at h
    exact h.symm
  rw [hval]
  exact countingMeasure_univ (sceneEdgeConfig hs)

end OTSelector.Reconstruction
