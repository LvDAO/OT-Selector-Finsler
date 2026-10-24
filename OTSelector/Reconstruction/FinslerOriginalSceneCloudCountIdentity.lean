import OTSelector.Reconstruction.FinslerOriginalSceneCloudCountTransfer
import OTSelector.Reconstruction.FinslerOriginalPalmMassTransferReduction
import OTSelector.Reconstruction.FinslerOriginalSceneCardinalityIdentity
import OTSelector.Reconstruction.FinslerOriginalAeFullMatching

/-!
# Scene-to-cloud count identity: exact reduction to a shell-cardinality identity

This module attacks the reduced count identity PalmSceneCloudCountTransfer:
  (s.1.1).univ = legalMaximumCard (legalMarkedGraph q (mSourceCount w) (mTargetCount w) id id w).

## What is provable

The scene edge total mass is the configuration shell-cardinality sum
(scene_edge_totalMass, unconditional), and the legal maximum cardinality is the
minimum of the cloud counts a.e. (ae_legalMaximumCard_eq_min, unconditional
given a.e. increasing clocks).  Therefore the count transfer is EQUIVALENT to
the pure shell-cardinality identity

  **sum over shells of (sceneEdgeConfig hs n).card = min (mSourceCount w) (mTargetCount w)**,

and, a.e. under twoMarkedCloudLaw, this equivalence holds unconditionally:

1. **palmSceneCloudCountTransfer_iff_shellSum_eq_min**: pointwise equivalence
   (given the pointwise graph-cardinality = min-counts identification).
2. **palmSceneCloudCountTransfer_of_shellSum_eq_min**: the transfer follows from
   the shell-cardinality identity.
3. **ae_palmSceneCloudCountTransfer_iff_shellSum_eq_min**: a.e. version, with no
   extra hypotheses beyond a.e. increasing clocks.

## Exact definitional obstruction (isolated hypothesis)

The count transfer is a relation between TWO INDEPENDENT objects: a scene
s : LegalMarkedOptimalInputScene q (edge measure s.1.1 plus coloured input
measure s.2) and a cloud state w : TwoMarkedCloudSpace q R R (counts plus marked
cube sequences).  There is no function in the library mapping a scene to a cloud
state, and the Palm construction legalMarkedJointPalm lives on the Palm mark
space PhysicalPairPalmMark (Fin q) = (clock pair, displacement), which contains
neither the scene edge measure nor the cloud counts.  Hence the count transfer
cannot be proved for arbitrary (s, w): it can only hold along a specific
coupling, and its proof needs a cardinality transport theorem for the edge index
map along that coupling.  The remaining named hypothesis is exactly
PalmSceneCloudCountTransfer together with the edge-index injectivity along the
coupling: the scene's counted pairs (support edges, bijective with occupied
source atoms by the scene cardinality identity) must be identified with the
cloud's realized matching pairs (legalMarkedGraph edges).
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

/-- **Pointwise reduction**: the Palm count transfer is equivalent to the pure
shell-cardinality identity, given the pointwise identification of the legal
maximum cardinality with the minimum cloud count. -/
theorem palmSceneCloudCountTransfer_iff_shellSum_eq_min
    {q : ℕ} {s : LegalMarkedOptimalInputScene q}
    (hs : IsFullOriginalInputMatching q s) (ω : TwoMarkedCloudSpace q ℝ ℝ)
    (hgraph : PartialMatching.legalMaximumCard
      (legalMarkedGraph q (mSourceCount ω) (mTargetCount ω) id id ω) =
        min (mSourceCount ω) (mTargetCount ω)) :
    PalmSceneCloudCountTransfer s ω ↔
      (∑' n, ((sceneEdgeConfig hs n).card : ℝ≥0∞)) =
        ((min (mSourceCount ω) (mTargetCount ω) : ℕ) : ℝ≥0∞) := by
  unfold PalmSceneCloudCountTransfer
  rw [← scene_edge_totalMass hs, hgraph]

/-- **The transfer follows from the shell-cardinality identity.** -/
theorem palmSceneCloudCountTransfer_of_shellSum_eq_min
    {q : ℕ} {s : LegalMarkedOptimalInputScene q}
    (hs : IsFullOriginalInputMatching q s) (ω : TwoMarkedCloudSpace q ℝ ℝ)
    (hgraph : PartialMatching.legalMaximumCard
      (legalMarkedGraph q (mSourceCount ω) (mTargetCount ω) id id ω) =
        min (mSourceCount ω) (mTargetCount ω))
    (hshell : (∑' n, ((sceneEdgeConfig hs n).card : ℝ≥0∞)) =
      ((min (mSourceCount ω) (mTargetCount ω) : ℕ) : ℝ≥0∞)) :
    PalmSceneCloudCountTransfer s ω :=
  (palmSceneCloudCountTransfer_iff_shellSum_eq_min hs ω hgraph).mpr hshell

/-- **A.e. reduction with no extra hypotheses** beyond a.e. increasing clocks. -/
theorem ae_palmSceneCloudCountTransfer_iff_shellSum_eq_min
    {q : ℕ} {s : LegalMarkedOptimalInputScene q}
    (hs : IsFullOriginalInputMatching q s)
    (α β : Measure ℝ) [IsProbabilityMeasure α] [IsProbabilityMeasure β] (ρ : ℝ≥0)
    (horder : ∀ᵐ p ∂α.prod β, p.1 < p.2) :
    ∀ᵐ ω ∂twoMarkedCloudLaw q ℝ ℝ α β ρ,
      (PalmSceneCloudCountTransfer s ω ↔
        (∑' n, ((sceneEdgeConfig hs n).card : ℝ≥0∞)) =
          ((min (mSourceCount ω) (mTargetCount ω) : ℕ) : ℝ≥0∞)) := by
  filter_upwards [ae_legalMaximumCard_eq_min q α β ρ id id horder] with ω hgraph
  exact palmSceneCloudCountTransfer_iff_shellSum_eq_min hs ω hgraph

end OTSelector.Reconstruction
