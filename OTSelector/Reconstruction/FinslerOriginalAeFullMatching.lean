import OTSelector.Reconstruction.FinslerOriginalRealizedCloudCount
import OTSelector.Probability.MarkedCloudCarriers

/-!
# Almost-everywhere full matching

This module proves the a.e. full-matching statement left open by
FinslerOriginalRealizedCloudCount.lean: for a.e. cloud state the legal marked
graph is the complete bipartite graph, hence its maximum cardinality is
min (mSourceCount) (mTargetCount), and the realized optimal plan's total mass is
that minimum.

1. **ae_legalMarkedGraph_eq_univ**: if the clocks of the two marked clouds are
   a.e. in increasing order (∀ᵐ p ∂α.prod β, sourceClock p.1 < targetClock p.2),
   then for a.e. cloud state every source/target pair is legally forward, i.e.
   the legal marked graph is Finset.univ.  Proof: the library's ae_all_mMarkPair
   promotes the pairwise a.e. order to an a.e. statement about all mark pairs of
   the cloud state.
2. **ae_legalMaximumCard_eq_min**: consequently for a.e. cloud state the legal
   maximum cardinality is min (mSourceCount) (mTargetCount) (legalMaximumCard_univ).
3. **ae_legalMarkedOptimalPlan_univ_eq_min**: for a.e. cloud state the total mass
   of the realized optimal physical plan is that minimum.
4. **ae_legalMarkedOptimalPlan_univ_eq_sourceCount_of_counts_eq**: if moreover
   the two cloud counts agree a.e., the plan mass equals the source count.

## Exact remaining sub-gap

The CLOUD COUNT EQUALITY (mSourceCount ω = mTargetCount ω) is NOT an a.e.
property of twoMarkedCloudLaw: the two marked clouds are independent Poisson
point processes with independent count variables, so equality holds only on
null-free subevents such as the Palm/rooted event where one atom per side is
removed (the marked stationary value lane works on that Palm event).  The
library has no theorem asserting the count equality for the cloud law, so item 4
is stated conditionally on it.  Given that event, items 1-3 already give the
full-matching maximum cardinality and the realized plan mass equal to the cloud
count, which is exactly the realized cloud count identity requested.
-/

open Set Function MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace
open OTSelector.Probability OTSelector.PointProcess
open scoped ENNReal NNReal BigOperators

noncomputable section
namespace OTSelector.Reconstruction

set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

/-- **A.e. complete legal graph.**  Under an a.e. increasing clock order, the
legal marked graph of a cloud state is complete. -/
theorem ae_legalMarkedGraph_eq_univ {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    (q : ℕ) (α : Measure A) [IsProbabilityMeasure α]
    (β : Measure B) [IsProbabilityMeasure β] (ρ : ℝ≥0)
    (sourceClock : A → ℝ) (targetClock : B → ℝ)
    (horder : ∀ᵐ p ∂α.prod β, sourceClock p.1 < targetClock p.2) :
    ∀ᵐ ω ∂twoMarkedCloudLaw q A B α β ρ,
      legalMarkedGraph q (mSourceCount ω) (mTargetCount ω)
        sourceClock targetClock ω = Finset.univ := by
  filter_upwards [ae_all_mMarkPair q α β ρ
    (P := fun a b => sourceClock a < targetClock b) horder] with ω hω
  ext e
  simp only [legalMarkedGraph, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
  exact hω e.1 e.2

/-- **A.e. maximum cardinality is the minimum of the cloud counts.** -/
theorem ae_legalMaximumCard_eq_min {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    (q : ℕ) (α : Measure A) [IsProbabilityMeasure α]
    (β : Measure B) [IsProbabilityMeasure β] (ρ : ℝ≥0)
    (sourceClock : A → ℝ) (targetClock : B → ℝ)
    (horder : ∀ᵐ p ∂α.prod β, sourceClock p.1 < targetClock p.2) :
    ∀ᵐ ω ∂twoMarkedCloudLaw q A B α β ρ,
      PartialMatching.legalMaximumCard
        (legalMarkedGraph q (mSourceCount ω) (mTargetCount ω)
          sourceClock targetClock ω) =
        min (mSourceCount ω) (mTargetCount ω) := by
  filter_upwards [ae_legalMarkedGraph_eq_univ q α β ρ sourceClock targetClock horder]
    with ω hω
  rw [hω, PartialMatching.legalMaximumCard_univ]

/-- **A.e. realized plan mass equals the minimum of the cloud counts.** -/
theorem ae_legalMarkedOptimalPlan_univ_eq_min (q : ℕ) (L r : ℝ)
    (kin : ℝ → ℝ → (Fin q → ℝ) → ℝ) (g : ℝ → ℝ → ℝ) (t : ℝ)
    (α β : Measure ℝ) [IsProbabilityMeasure α] [IsProbabilityMeasure β] (ρ : ℝ≥0)
    (horder : ∀ᵐ p ∂α.prod β, p.1 < p.2) :
    ∀ᵐ ω ∂twoMarkedCloudLaw q ℝ ℝ α β ρ,
      legalMarkedOptimalPlan q L r kin g t ω Set.univ =
        ((min (mSourceCount ω) (mTargetCount ω) : ℕ) : ℝ≥0∞) := by
  filter_upwards [ae_legalMaximumCard_eq_min q α β ρ id id horder] with ω hω
  rw [legalMarkedOptimalPlan_univ, hω]

/-- **A.e. realized plan mass equals the cloud source count under agreeing
counts.** -/
theorem ae_legalMarkedOptimalPlan_univ_eq_sourceCount_of_counts_eq (q : ℕ) (L r : ℝ)
    (kin : ℝ → ℝ → (Fin q → ℝ) → ℝ) (g : ℝ → ℝ → ℝ) (t : ℝ)
    (α β : Measure ℝ) [IsProbabilityMeasure α] [IsProbabilityMeasure β] (ρ : ℝ≥0)
    (horder : ∀ᵐ p ∂α.prod β, p.1 < p.2)
    (hcounts : ∀ᵐ ω ∂twoMarkedCloudLaw q ℝ ℝ α β ρ,
      mSourceCount ω = mTargetCount ω) :
    ∀ᵐ ω ∂twoMarkedCloudLaw q ℝ ℝ α β ρ,
      legalMarkedOptimalPlan q L r kin g t ω Set.univ =
        (mSourceCount ω : ℝ≥0∞) := by
  filter_upwards [ae_legalMarkedOptimalPlan_univ_eq_min q L r kin g t α β ρ horder,
    hcounts] with ω hω hc
  rw [hω, hc, min_self]

end OTSelector.Reconstruction
