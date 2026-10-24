import OTSelector.Reconstruction.FinslerOriginalAeFullMatching
import OTSelector.Probability.MarkedPoissonCube

/-!
# Cloud count definitional audit

This module audits the definitions of the cloud counts mSourceCount and
mTargetCount in the marked cloud model.

Findings (all proved):

1. **mSourceCount_apply / mTargetCount_apply**: the counts are the two Poisson
   count coordinates of the two independent marked clouds:
   mSourceCount w = w.1.1 and mTargetCount w = w.2.1 (definitionally).
2. **twoMarkedCloudLaw_def**: the cloud law is the product of the two marked
   Poisson cloud laws, i.e. the two clouds - and hence their counts - are
   independent.
3. **twoMarkedCloudLaw_counts**: the joint law of the count pair
   (mSourceCount, mTargetCount) is the product poissonMeasure r x poissonMeasure r.
4. **mSourceCount_ne_mTargetCount_demo**: cloud states with unequal counts exist,
   so the counts are NOT equal by construction.

## Conclusion and exact remaining sub-gap

The counts are GENUINELY INDEPENDENT Poisson counts, not one shared count: they
are the count coordinates of two independent Poissonized clouds.  Hence
mSourceCount = mTargetCount cannot be proved for all cloud states, and it is not
an almost-every property of twoMarkedCloudLaw either (the diagonal in the
product of two Poisson laws has mass sum_n P(n)^2 < 1).  The only count
equalization available in the marked stationary value lane is on the Palm/rooted
event, where one atom per side is removed; the library does not expose a theorem
stating mSourceCount = mTargetCount on that event.  Consequently the transfer of
FinslerOriginalAeFullMatching's realized count identity to the scene count stays
conditional on that rooted-event identification.
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

variable {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]

/-- The source count is the first Poisson count coordinate. -/
theorem mSourceCount_apply {q : ℕ} (ω : TwoMarkedCloudSpace q A B) :
    mSourceCount ω = ω.1.1 := rfl

/-- The target count is the second cloud's Poisson count coordinate. -/
theorem mTargetCount_apply {q : ℕ} (ω : TwoMarkedCloudSpace q A B) :
    mTargetCount ω = ω.2.1 := rfl

/-- The cloud law is the product of the two independent marked cloud laws. -/
theorem twoMarkedCloudLaw_def {q : ℕ} (α : Measure A) [IsProbabilityMeasure α]
    (β : Measure B) [IsProbabilityMeasure β] (r : ℝ≥0) :
    twoMarkedCloudLaw q A B α β r =
      (markedPoissonLaw (q := q) A α r).prod (markedPoissonLaw (q := q) B β r) :=
  rfl

/-- **The counts are independent Poisson counts.**  The joint law of the count
pair is the product of two Poisson measures. -/
theorem twoMarkedCloudLaw_counts {q : ℕ} (α : Measure A) [IsProbabilityMeasure α]
    (β : Measure B) [IsProbabilityMeasure β] (r : ℝ≥0) :
    (twoMarkedCloudLaw q A B α β r).map
        (fun ω => (mSourceCount ω, mTargetCount ω)) =
      (poissonMeasure r).prod (poissonMeasure r) := by
  rw [twoMarkedCloudLaw_def]
  have h1 : Measure.map Prod.fst (markedPoissonLaw (q := q) A α r) =
      poissonMeasure r := by
    rw [markedPoissonLaw, Measure.map_fst_prod, measure_univ, one_smul]
  have h2 : Measure.map Prod.fst (markedPoissonLaw (q := q) B β r) =
      poissonMeasure r := by
    rw [markedPoissonLaw, Measure.map_fst_prod, measure_univ, one_smul]
  have hcondeq : (fun ω : TwoMarkedCloudSpace q A B =>
      (mSourceCount ω, mTargetCount ω)) = fun ω => Prod.map Prod.fst Prod.fst ω := by
    funext ω
    simp [mSourceCount, mTargetCount, Prod.map]
  rw [hcondeq]
  rw [show (fun ω => Prod.map Prod.fst Prod.fst ω) = Prod.map Prod.fst Prod.fst from rfl]
  trans (Measure.map Prod.fst (markedPoissonLaw (q := q) A α r)).prod
      (Measure.map Prod.fst (markedPoissonLaw (q := q) B β r))
  · exact (Measure.map_prod_map (markedPoissonLaw (q := q) A α r)
      (markedPoissonLaw (q := q) B β r) measurable_fst measurable_fst).symm
  · rw [h1, h2]

/-- **Counts are not equal by construction.**  Explicit cloud states with
different source and target counts. -/
theorem mSourceCount_ne_mTargetCount_demo {q : ℕ} (a : A) (b : B) :
    ∃ ω : TwoMarkedCloudSpace q A B, mSourceCount ω ≠ mTargetCount ω :=
  ⟨((0, fun _ => (0, a)), (1, fun _ => (0, b))), by
    simp [mSourceCount_apply, mTargetCount_apply]⟩

end OTSelector.Reconstruction
