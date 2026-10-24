import OTSelector.Reconstruction.FinslerOriginalConditionalEndgame

/-!
# The paper endgame data structure

This module packages the paper-side endgame data of the general Finsler
selector: the paper geometric hypotheses together with the six analytic endgame
fields produced by the lane analyses (lower half, upper half, value), as
|FinslerPaperEndgameData|, and converts it into the conditional endgame
structure consumed by the final assembly.

The remaining inputs are exactly the fields of |FinslerPaperEndgameData|: the
paper geometric hypotheses, and the six analytic fields (|pressureLower|,
|pressureUpper|, |radius|, |radius| positivity, |hprob|, |hupper|, |hvalue|),
each of which now has a producer bundle in the reconstruction lane.

**The paper-facing theorem is not stated here.**  A wrapper of the conditional
endgame that assumes the endgame data for *every* 1-Lipschitz potential is
vacuous: the constant potential is 1-Lipschitz but has empty calibrated
interior, so it admits no paper geometric hypotheses
(research/AUDIT-PAPER-WRAPPER.md, flag F10, with the machine-checked witnesses
in team-staging/AUDIT-PAPER-WRAPPER-check.lean).  The paper-facing theorem must
instead produce this datum at the potential selected by the final assembly,
i.e. after the pressure/value lane data have been constructed at that
potential; until then the correct interface is the data structure and
|toConditionalEndgame|.  No |sorry|, |admit| or added axiom occurs.
-/

open Set Function Filter MeasureTheory ProbabilityTheory Manifold Module
open OTSelector.Geometry OTSelector.Probability TopologicalSpace
open OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex
open scoped Topology ContDiff ENNReal NNReal CompactlySupported BoundedContinuousFunction

noncomputable section
namespace OTSelector.Reconstruction

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 400000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  {F : ContinuousFinslerNorm E M}

/-- **The paper endgame data**: the paper-side geometric hypotheses together with
the six analytic endgame fields, stated in the exact consumer interfaces of
|FinslerConditionalEndgameHypotheses|. -/
structure FinslerPaperEndgameData
    (F : ContinuousFinslerNorm E M) (μ ν : ProbabilityMeasure M)
    {A B : Set M} (hA : IsCompact A) (hB : IsCompact B)
    (hμA : ∀ᵐ x ∂(μ : Measure M), x ∈ A)
    (hνB : ∀ᵐ y ∂(ν : Measure M), y ∈ B)
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (P : ∀ n, Measure (Ω n))
    (X Y : ∀ n, Fin (n + 1) → Ω n → M) (u : M → ℝ) where
  /-- The paper-side geometric hypotheses. -/
  geometric : FinslerPaperGeometricHypotheses F u μ ν
  /-- The lower pressure localization limit. -/
  pressureLower : FinalPressureField A B
  /-- The upper pressure localization limit. -/
  pressureUpper : FinalPressureField A B
  /-- The common tilt interval. -/
  radius : FinalRadiusField A B
  /-- The tilt interval is positive at every probe. -/
  hradius : FinalPositiveRadius radius
  /-- The original iid lower pressure localization. -/
  hprob : FinalProbLowerData F μ ν hA hB hμA hνB P X Y u pressureLower radius
  /-- The original iid upper pressure localization. -/
  hupper : FinalProbUpperData F μ ν hA hB hμA hνB P X Y u pressureUpper radius
  /-- The value identification closing the pressure bracket. -/
  hvalue : FinalValueIdentification pressureLower pressureUpper

namespace FinslerPaperEndgameData

variable {u : M → ℝ} {μ ν : ProbabilityMeasure M}
  {A B : Set M} {hA : IsCompact A} {hB : IsCompact B}
  {hμA : ∀ᵐ x ∂(μ : Measure M), x ∈ A}
  {hνB : ∀ᵐ y ∂(ν : Measure M), y ∈ B}
  {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
  {P : ∀ n, Measure (Ω n)}
  {X Y : ∀ n, Fin (n + 1) → Ω n → M}

/-- The paper endgame data yield the conditional endgame structure. -/
def toConditionalEndgame
    (D : FinslerPaperEndgameData F μ ν hA hB hμA hνB P X Y u) :
    FinslerConditionalEndgameHypotheses F u μ ν hA hB hμA hνB P X Y where
  geometric := D.geometric
  pressureLower := D.pressureLower
  pressureUpper := D.pressureUpper
  radius := D.radius
  hradius := D.hradius
  hvalue := D.hvalue
  hprob := D.hprob
  hupper := D.hupper

/-- The paper endgame data make the consumer final inputs nonempty. -/
theorem nonempty_finalInputs
    (D : FinslerPaperEndgameData F μ ν hA hB hμA hνB P X Y u) :
    Nonempty (FinslerSelectorFinalInputs F μ ν hA hB hμA hνB P X Y u) :=
  D.toConditionalEndgame.nonempty_finalInputs


/-- The paper endgame datum yields the conditional endgame structure, hence the
endgame hypotheses are inhabited whenever the paper endgame data are. -/
theorem nonempty_conditionalEndgame
    (D : FinslerPaperEndgameData F μ ν hA hB hμA hνB P X Y u) :
    Nonempty (FinslerConditionalEndgameHypotheses F u μ ν hA hB hμA hνB P X Y) :=
  ⟨D.toConditionalEndgame⟩

end FinslerPaperEndgameData

end OTSelector.Reconstruction
