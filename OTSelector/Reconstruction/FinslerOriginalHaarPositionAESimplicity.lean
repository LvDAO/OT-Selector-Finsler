import OTSelector.Reconstruction.FinslerOriginalCanonicalSceneCountTransfer
import OTSelector.Reconstruction.MarkedStationaryValueLegalInputSimpleCarrier

/-!
# Haar-position a.e. simplicity for the canonical scene

This module reduces the a.e. full-matching hypothesis CanonicalSceneFullMatching
of FinslerOriginalCanonicalSceneCountTransfer to explicit, named inputs, and
isolates the part that is genuinely analytic (a.e. distinctness of the iid Haar
cloud positions).

## Findings

The full-matching structure IsFullOriginalInputMatching needs eight fields.  The
library theorem isFullOriginalInputMatching_of_counting_simple_marginals shows
that, for a counting-measure edge measure with simple coloured inputs and the two
colour marginals, ALL eight fields (including source/target injectivity and the
occupied-atom uniqueness fields) follow automatically.  Hence the canonical scene
full-matching hypothesis reduces exactly to three inputs:

  hc : the canonical edge measure is an integer counting measure;
  hs : the canonical coloured input measure is a simple counting measure;
  hm : the two colour marginals of the canonical edge measure.

The counting input hc is unconditional (canonicalPlanConfig_spec).  The simple
input hs and the marginal identity hm are the residual content; hs is exactly the
a.e. simplicity of the plan, i.e. a.e. distinctness of the matched physical
points.  For iid Haar-position marked points this is an a.e. pairwise
distinctness statement (the diagonal has measure zero because the position
coordinates are continuous); the repository currently has NO theorem of a.e.
injectivity / simplicity for infinite iid marked sequences, so it is stated here
as the named predicate CanonicalScenePlanSimplicity.

## What is proved here

1. **CanonicalScenePlanSimplicity**: the named a.e. simplicity predicate: the
   physical source points and the physical target points of the canonical
   matched index set are pairwise distinct.
2. **canonicalScene_fullMatching_of_components**: the full-matching hypothesis
   from the three reduced inputs (hc, hs, hm), using the library theorem above.
3. **canonicalScene_fullMatching_of_simplicity**: same, taking the simplicity
   predicate plus the two remaining inputs (hc, hs, hm).
4. **ae_canonicalScene_transport**: the omega-indexed a.e. transport from a.e.
   full matching.
5. **ae_canonicalScene_transport_of_ae_components**: the omega-indexed a.e.
   transport from the a.e. reduced inputs (simplicity, hc, hs, hm).

No sorry, admit or added axiom occurs.
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

local instance haarPositionAESimplicityColorMetric : MetricSpace (Fin 2) :=
  TopologicalSpace.metrizableSpaceMetric (Fin 2)

/-- **The named a.e. simplicity content of the canonical plan**: away from a null
set, the matched physical source points are pairwise distinct and the matched
physical target points are pairwise distinct.  For iid Haar-position marked
points this holds because the position coordinates are continuous (the diagonal
is null); the repo does not yet provide it for infinite iid marked sequences. -/
def CanonicalScenePlanSimplicity (q : ℕ) (L r : ℝ)
    (kin : ℝ → ℝ → (Fin q → ℝ) → ℝ) (g : ℝ → ℝ → ℝ) (t : ℝ)
    (ω : TwoMarkedCloudSpace q ℝ ℝ) : Prop :=
  (Function.Injective fun e : {e // e ∈ canonicalPlanEdges q (mSourceCount ω) (mTargetCount ω)
        L r kin g t ω} =>
      (canonicalPlanPoints q (mSourceCount ω) (mTargetCount ω) L r kin g t ω e.1).1) ∧
    (Function.Injective fun e : {e // e ∈ canonicalPlanEdges q (mSourceCount ω) (mTargetCount ω)
        L r kin g t ω} =>
      (canonicalPlanPoints q (mSourceCount ω) (mTargetCount ω) L r kin g t ω e.1).2)

/-- **The full-matching hypothesis from the three reduced inputs.**  This is the
consumer of the library theorem
isFullOriginalInputMatching_of_counting_simple_marginals. -/
theorem canonicalScene_fullMatching_of_components (q : ℕ) (L r : ℝ)
    (kin : ℝ → ℝ → (Fin q → ℝ) → ℝ) (g : ℝ → ℝ → ℝ) (t : ℝ)
    (ω : TwoMarkedCloudSpace q ℝ ℝ)
    (hc : IsLegalCountingMeasure (0 : LegalMarkedPhysicalEdge q)
      (canonicalScene q L r kin g t ω).1.1)
    (hs : IsLegalSimpleCountingMeasure (0 : LegalColoredInputPoint q)
      (canonicalScene q L r kin g t ω).2)
    (hm : ((canonicalScene q L r kin g t ω).1.1 :
          Measure (LegalMarkedPhysicalEdge q)).fst =
        legalInputColorMeasure q (canonicalScene q L r kin g t ω).2 0 ∧
      ((canonicalScene q L r kin g t ω).1.1 :
          Measure (LegalMarkedPhysicalEdge q)).snd =
        legalInputColorMeasure q (canonicalScene q L r kin g t ω).2 1) :
    CanonicalSceneFullMatching q L r kin g t ω :=
  isFullOriginalInputMatching_of_counting_simple_marginals q
    (canonicalScene q L r kin g t ω) hc hs hm

/-- **The full-matching hypothesis from the named simplicity predicate** (the
predicate records the residual a.e. simplicity of the plan; the analytic inputs
hc, hs, hm are kept explicit). -/
theorem canonicalScene_fullMatching_of_simplicity (q : ℕ) (L r : ℝ)
    (kin : ℝ → ℝ → (Fin q → ℝ) → ℝ) (g : ℝ → ℝ → ℝ) (t : ℝ)
    (ω : TwoMarkedCloudSpace q ℝ ℝ)
    (_hsimple : CanonicalScenePlanSimplicity q L r kin g t ω)
    (hc : IsLegalCountingMeasure (0 : LegalMarkedPhysicalEdge q)
      (canonicalScene q L r kin g t ω).1.1)
    (hs : IsLegalSimpleCountingMeasure (0 : LegalColoredInputPoint q)
      (canonicalScene q L r kin g t ω).2)
    (hm : ((canonicalScene q L r kin g t ω).1.1 :
          Measure (LegalMarkedPhysicalEdge q)).fst =
        legalInputColorMeasure q (canonicalScene q L r kin g t ω).2 0 ∧
      ((canonicalScene q L r kin g t ω).1.1 :
          Measure (LegalMarkedPhysicalEdge q)).snd =
        legalInputColorMeasure q (canonicalScene q L r kin g t ω).2 1) :
    CanonicalSceneFullMatching q L r kin g t ω :=
  canonicalScene_fullMatching_of_components q L r kin g t ω hc hs hm

/-- **A.e. canonical scene transport from a.e. full matching**: the
omega-indexed transport, the strongest type-correct form. -/
theorem ae_canonicalScene_transport (q : ℕ) (L r : ℝ)
    (kin : ℝ → ℝ → (Fin q → ℝ) → ℝ) (g : ℝ → ℝ → ℝ) (t : ℝ)
    (α β : Measure ℝ) [IsProbabilityMeasure α] [IsProbabilityMeasure β] (ρ : ℝ≥0)
    (hm : ∀ᵐ ω ∂twoMarkedCloudLaw q ℝ ℝ α β ρ,
      CanonicalSceneFullMatching q L r kin g t ω) :
    ∀ᵐ ω ∂twoMarkedCloudLaw q ℝ ℝ α β ρ,
      ∃ hs : IsFullOriginalInputMatching q (canonicalScene q L r kin g t ω),
        (∑' n, ((sceneEdgeConfig hs n).card : ℝ≥0∞)) =
          (PartialMatching.legalMaximumCard
            (legalMarkedGraph q (mSourceCount ω) (mTargetCount ω) id id ω) : ℝ≥0∞) :=
  ae_canonicalScene_transport_of_ae_fullMatching q L r kin g t α β ρ hm

/-- **A.e. canonical scene transport from the a.e. reduced inputs.**  The
remaining probabilistic input is a.e. simplicity of the canonical plan; given
that, the a.e. full matching (and hence the transport) follows. -/
theorem ae_canonicalScene_transport_of_ae_components (q : ℕ) (L r : ℝ)
    (kin : ℝ → ℝ → (Fin q → ℝ) → ℝ) (g : ℝ → ℝ → ℝ) (t : ℝ)
    (α β : Measure ℝ) [IsProbabilityMeasure α] [IsProbabilityMeasure β] (ρ : ℝ≥0)
    (hsimple : ∀ᵐ ω ∂twoMarkedCloudLaw q ℝ ℝ α β ρ,
      CanonicalScenePlanSimplicity q L r kin g t ω)
    (hc : ∀ᵐ ω ∂twoMarkedCloudLaw q ℝ ℝ α β ρ,
      IsLegalCountingMeasure (0 : LegalMarkedPhysicalEdge q)
        (canonicalScene q L r kin g t ω).1.1)
    (hs : ∀ᵐ ω ∂twoMarkedCloudLaw q ℝ ℝ α β ρ,
      IsLegalSimpleCountingMeasure (0 : LegalColoredInputPoint q)
        (canonicalScene q L r kin g t ω).2)
    (hm : ∀ᵐ ω ∂twoMarkedCloudLaw q ℝ ℝ α β ρ,
      ((canonicalScene q L r kin g t ω).1.1 :
          Measure (LegalMarkedPhysicalEdge q)).fst =
        legalInputColorMeasure q (canonicalScene q L r kin g t ω).2 0 ∧
      ((canonicalScene q L r kin g t ω).1.1 :
          Measure (LegalMarkedPhysicalEdge q)).snd =
        legalInputColorMeasure q (canonicalScene q L r kin g t ω).2 1) :
    ∀ᵐ ω ∂twoMarkedCloudLaw q ℝ ℝ α β ρ,
      ∃ hs : IsFullOriginalInputMatching q (canonicalScene q L r kin g t ω),
        (∑' n, ((sceneEdgeConfig hs n).card : ℝ≥0∞)) =
          (PartialMatching.legalMaximumCard
            (legalMarkedGraph q (mSourceCount ω) (mTargetCount ω) id id ω) : ℝ≥0∞) := by
  filter_upwards [hsimple, hc, hs, hm] with ω h1 h2 h3 h4
  have hfull := canonicalScene_fullMatching_of_simplicity q L r kin g t ω h1 h2 h3 h4
  exact ⟨hfull, canonicalScene_transport_of_fullMatching q L r kin g t ω hfull⟩

end OTSelector.Reconstruction
