import OTSelector.Reconstruction.FinslerOriginalCloudCountIdentity
import OTSelector.Reconstruction.MarkedStationaryValueLegalOptimalScene

/-!
# Realized cloud count identity

The physical optimal plan of a cloud state is a finite sum of Dirac masses over
the edges of the realized legal matching.  This module proves the realized-count
forms of the cloud count identity.

1. **finset_sum_dirac_univ**: the total mass of a finite set of Dirac masses is
   the cardinality of the edge set (the abstract cardinality interface).
2. **legalMarkedFixedOptimalPlan_univ_eq_edgesCard** and
   **legalMarkedOptimalPlan_univ_eq_edgesCard**: the realized plan of a cloud
   state has total mass equal to the number of edges of the realized legal
   matching (also derivable from the library's legalMaximumCard total-mass
   theorem, which already gives mass = legalMaximumCard of the legal graph).
3. **legalMarkedOptimalPlan_univ_eq_mSourceCount_of_maxCard** and the target
   analogue: if the legal graph has maximum cardinality equal to mSourceCount
   (resp. mTargetCount), which is the full-matching case, then the realized
   plan mass equals that cloud count.

## Exact remaining sub-gap

The remaining step is the HYPOTHESIS of (3): proving
legalMaximumCard (legalMarkedGraph q (mSourceCount w) (mTargetCount w) id id w) =
mSourceCount w for a.e. cloud state.  This is the full-matching statement: every
source/target clock pair is legally forward, so the legal graph is the complete
bipartite graph and its maximum cardinality is min(mSourceCount, mTargetCount);
with mSourceCount = mTargetCount =: r this is r.  The library's clock-gap work
(MarkedStationaryValueLegalOptimalPalmSupport) proves the forward clock gap only
on the Palm-support event, not for a.e. cloud state, and no theorem identifies
the realized legal graph with the complete graph.  Finally, transferring this
count identity through the Palm correspondence to the scene edge measure of
FinslerOriginalSceneCountIdentity is the remaining bridge.
-/

open Set Function MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace
open OTSelector.Probability OTSelector.PointProcess
open scoped ENNReal NNReal BigOperators

noncomputable section
namespace OTSelector.Reconstruction

set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

/-- **Total mass of a finite set of Dirac masses.** -/
theorem finset_sum_dirac_univ {ι X : Type*} [MeasurableSpace X]
    (E : Finset ι) (f : ι → X) :
    (∑ e ∈ E, Measure.dirac (f e)) Set.univ = (E.card : ℝ≥0∞) := by
  classical
  induction E using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, Measure.add_apply, ih]
      have h1 : (Measure.dirac (f a)) Set.univ = 1 := by simp
      rw [h1, Finset.card_insert_of_notMem ha, Nat.cast_add, Nat.cast_one]
      exact add_comm _ _

/-- **Realized edge count of the fixed-prefix plan.** -/
theorem legalMarkedFixedOptimalPlan_univ_eq_edgesCard (q m n : ℕ) (L r : ℝ)
    (kin : ℝ → ℝ → (Fin q → ℝ) → ℝ) (g : ℝ → ℝ → ℝ) (t : ℝ)
    (ω : TwoMarkedCloudSpace q ℝ ℝ) :
    legalMarkedFixedOptimalPlan q m n L r kin g t ω Set.univ =
      (((firstLegalMarkedOptimalMatching q m n id id r kin g t ω).edges.card : ℕ) :
        ℝ≥0∞) := by
  rw [legalMarkedFixedOptimalPlan]
  exact finset_sum_dirac_univ _ _

/-- **Realized edge count of the actual cloud plan.** -/
theorem legalMarkedOptimalPlan_univ_eq_edgesCard (q : ℕ) (L r : ℝ)
    (kin : ℝ → ℝ → (Fin q → ℝ) → ℝ) (g : ℝ → ℝ → ℝ) (t : ℝ)
    (ω : TwoMarkedCloudSpace q ℝ ℝ) :
    legalMarkedOptimalPlan q L r kin g t ω Set.univ =
      (((firstLegalMarkedOptimalMatching q (mSourceCount ω) (mTargetCount ω)
        id id r kin g t ω).edges.card : ℕ) : ℝ≥0∞) := by
  rw [legalMarkedOptimalPlan]
  exact legalMarkedFixedOptimalPlan_univ_eq_edgesCard q (mSourceCount ω)
    (mTargetCount ω) L r kin g t ω

/-- **Realized source count under full matching (maximum-cardinality form).**
If the realized legal graph has maximum cardinality mSourceCount, the plan mass
is the cloud source count. -/
theorem legalMarkedOptimalPlan_univ_eq_mSourceCount_of_maxCard
    (q : ℕ) (L r : ℝ) (kin : ℝ → ℝ → (Fin q → ℝ) → ℝ)
    (g : ℝ → ℝ → ℝ) (t : ℝ) (ω : TwoMarkedCloudSpace q ℝ ℝ)
    (hcard : PartialMatching.legalMaximumCard
      (legalMarkedGraph q (mSourceCount ω) (mTargetCount ω) id id ω) =
        mSourceCount ω) :
    legalMarkedOptimalPlan q L r kin g t ω Set.univ =
      (mSourceCount ω : ℝ≥0∞) := by
  rw [legalMarkedOptimalPlan_univ, hcard]

/-- **Realized target count under full matching (maximum-cardinality form).** -/
theorem legalMarkedOptimalPlan_univ_eq_mTargetCount_of_maxCard
    (q : ℕ) (L r : ℝ) (kin : ℝ → ℝ → (Fin q → ℝ) → ℝ)
    (g : ℝ → ℝ → ℝ) (t : ℝ) (ω : TwoMarkedCloudSpace q ℝ ℝ)
    (hcard : PartialMatching.legalMaximumCard
      (legalMarkedGraph q (mSourceCount ω) (mTargetCount ω) id id ω) =
        mTargetCount ω) :
    legalMarkedOptimalPlan q L r kin g t ω Set.univ =
      (mTargetCount ω : ℝ≥0∞) := by
  rw [legalMarkedOptimalPlan_univ, hcard]

end OTSelector.Reconstruction
