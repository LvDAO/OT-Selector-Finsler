import OTSelector.Reconstruction.MarkedStationaryValueLegalCloud
import OTSelector.Finite.LegalMatchingValue
import OTSelector.Reconstruction.MarkedStationaryValueLegalStationaryPoissonCandidate
import OTSelector.Reconstruction.FinslerOriginalCandidateWindowLowerBound

/-!
# Concrete window cardinality and legality identification

This module provides the concrete identification pieces for the windowed lower
bound of FinslerOriginalCandidateWindowLowerBound.

1. The legal tilted value is exactly the finite legal maximum value of the
   concrete legal marked graph (definitional identification).

2. The legal maximum cardinality of the concrete legal marked graph is at most
   the smaller color count.

3. For a finite legal matching that already saturates all vertices (cardinality
   equal to the smaller count), the legal maximum cardinality equals that count,
   so the missing-cardinality defect is exactly zero.

4. Consequently the normalized missing-cardinality defect vanishes: a zero
   defect divided by any nonzero volume tends to zero.  This is the exact
   "finite legal cardinality asymptotically full" input consumed by the
   two-defect squeeze of FinslerOriginalCandidateWindowLowerBound.

For a genuine candidate matching the actual matching is full
(LegalWeightedStationaryPoissonMatching.full_matching) and every support edge is
forward (LegalWeightedStationaryPoissonMatching.forward), so the finite legal
graph already contains a legal matching saturating all vertices; hence the
missing-cardinality defect is zero almost surely.  The reduction of that
almost-sure statement to the finite cardinality identity is recorded here.

## Exact remaining sub-gap

The remaining step is the measure-theoretic counting identification: extracting
from IsFullOriginalInputMatching the integer edge count of the scene support and
identifying it with the color counts mSourceCount and mTargetCount, so that the
finite cardinality identity applies.  The finite cardinality and defect
vanishing are proved here.
-/

open Set Function MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace
open OTSelector.Probability
open scoped ENNReal NNReal BigOperators

noncomputable section
namespace OTSelector.Reconstruction

set_option maxHeartbeats 1200000
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

/-- **Identification of the legal tilted value with the finite legal maximum of
the concrete legal marked graph.**  This is definitional: the legal tilted value
is the signed minimum over the actual legal maximum-cardinality class of the
concrete forward-edge graph. -/
theorem legalMarkedTilted_eq_legalMaximumValue (q : ℕ)
    {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    (sourceClock : A → ℝ) (targetClock : B → ℝ) (r : ℝ)
    (kin : A → B → (Fin q → ℝ) → ℝ) (g : A → B → ℝ) (t : ℝ)
    (ω : TwoMarkedCloudSpace q A B) :
    legalMarkedTilted q sourceClock targetClock r kin g t ω =
      PartialMatching.legalMaximumValue
        (legalMarkedGraph q (mSourceCount ω) (mTargetCount ω) sourceClock targetClock ω)
        (fun i j => mKineticCost q r kin ω i j + t * mProbe g ω i j) :=
  rfl

/-- **Window cardinality bound.**  The legal maximum cardinality of the concrete
legal marked graph is at most the smaller color count. -/
theorem legalMarkedGraph_legalMaximumCard_le_min (q : ℕ)
    {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    (sourceClock : A → ℝ) (targetClock : B → ℝ)
    (ω : TwoMarkedCloudSpace q A B) :
    PartialMatching.legalMaximumCard
        (legalMarkedGraph q (mSourceCount ω) (mTargetCount ω) sourceClock targetClock ω) ≤
      min (mSourceCount ω) (mTargetCount ω) :=
  PartialMatching.legalMaximumCard_le_min _

/-- **Zero missing-cardinality defect at full cardinality.**  If the concrete
legal marked graph contains a legal matching saturating the smaller color count,
then its legal maximum cardinality is maximal and the missing-cardinality defect
is zero. -/
theorem legalMarkedGraph_missingCardinality_eq_zero_of_full (q : ℕ)
    {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    (sourceClock : A → ℝ) (targetClock : B → ℝ)
    (ω : TwoMarkedCloudSpace q A B)
    (hmn : mSourceCount ω = mTargetCount ω)
    (hfull : PartialMatching.legalMaximumCard
        (legalMarkedGraph q (mSourceCount ω) (mTargetCount ω) sourceClock targetClock ω) =
      min (mSourceCount ω) (mTargetCount ω)) :
    ((mTargetCount ω -
        PartialMatching.legalMaximumCard
          (legalMarkedGraph q (mSourceCount ω) (mTargetCount ω) sourceClock targetClock ω) : ℕ) : ℝ) = 0
    ∧ (mSourceCount ω -
        PartialMatching.legalMaximumCard
          (legalMarkedGraph q (mSourceCount ω) (mTargetCount ω) sourceClock targetClock ω) : ℕ) = 0 := by
  have hmin : min (mSourceCount ω) (mTargetCount ω) = mTargetCount ω := by
    rw [hmn, min_self]
  constructor
  · rw [hfull, hmin]
    norm_num
  · rw [hfull, hmin, hmn]
    exact Nat.sub_self _

/-- **Vanishing normalized missing-cardinality defect.**  A missing-cardinality
defect that is eventually zero, normalized by a positive volume, tends to zero.
This is the exact lower-defect vanishing input of the two-defect squeeze. -/
theorem normalized_missingCardinality_tendsto_zero
    (missing vol : ℕ → ℝ) (B : ℝ)
    (hmissing : ∀ n, missing n = 0)
    (hvol : ∀ n, vol n ≠ 0) :
    Tendsto (fun n => (missing n * B) / vol n) atTop (𝓝 0) := by
  have hzero : (fun n => (missing n * B) / vol n) = fun _ => (0 : ℝ) := by
    funext n
    rw [hmissing n]
    simp
  rw [hzero]
  exact tendsto_const_nhds

/-- **Candidate missing defect vanishes.**  For a genuine weighted stationary
matching, once the a.e. full-cardinality identification supplies the zero
missing-cardinality defect, the normalized lower defect of the two-sided
local-optimality squeeze vanishes. -/
theorem candidateWindowMissingDefect_vanishes
    (missing vol : ℕ → ℝ) (B : ℝ)
    (hmissing : ∀ n, missing n = 0)
    (hvol : ∀ n, vol n ≠ 0) :
    Tendsto (fun n => ((missing n * B) / vol n)) atTop (𝓝 0) :=
  normalized_missingCardinality_tendsto_zero missing vol B hmissing hvol

end OTSelector.Reconstruction
