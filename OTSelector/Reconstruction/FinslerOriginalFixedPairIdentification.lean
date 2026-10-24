import OTSelector.Reconstruction.FinslerOriginalMaskCouplingLaw

/-!
# Exchangeability and fixed-pair identification: the clipping decomposition

This module isolates the two remaining pieces of the mask-coupling law
(`FinslerOriginalMaskCouplingLaw.lean`) at the level where they become *additive*.

**Clipping decomposition (proved).**  The frozen core entry is a clipped linear
expression,

  `maskedFrozenCost Q (frozenCoreMatrix C ε z₀ X Y k t h) i j
    = 1_{(i,j) ∈ Q} · max (x i j) 0,`

where `x = (1-2ε) k · frozenPhysicalCost + t · probe` is linear in the cost and probe.
The identity `max x 0 = x + max (-x) 0` therefore splits every fixed-pair masked
frozen expectation into

  `E[1_Q · max x 0] = E[1_Q · x] + E[1_Q · max (-x) 0],`

i.e. the **linear (cost + probe) part** plus a **clipping correction** term.  The
proved theorem `integral_indicator_max_eq` is exactly this additive decomposition
(abstract form; instantiate with `x = (1-2ε)k·frozenPhysicalCost + t·probe` and
`Q = edgeEvent`).

**What remains.**  Two pieces are *not* proved here and are stated with explicit
quantifiers:

* `MaskedEntryExchangeability`: the equal-expectation hypothesis of the uniform
  masked-entry identity must be derived from permutation invariance of the iid
  sample and of the mask condition `edgeEvent` (with integrability);
* `FixedPairLinearIdentification`: the *linear* fixed-pair expectation
  `E[1_Q · ((1-2ε) k · frozenPhysicalCost + t · probe)]` divided by `(n+1)^{2/q}`
  must converge to the population tile value `tilePopValue` (Palm/stationary
  identification of the single-edge conditional law given mask membership).  The
  clipping correction is separately bounded by the frozen absolute entry bound and
  is part of the same input.

No `sorry`, `admit` or added axiom occurs.
-/

open Set Function Matrix Filter MeasureTheory ProbabilityTheory Manifold Module
  OTSelector.Probability
open OTSelector.Geometry
open scoped Topology ContDiff NNReal ENNReal BoundedContinuousFunction

noncomputable section

set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace OTSelector.Reconstruction

/-- **The clipping identity.**  `max x 0 = x + max (-x) 0`. -/
theorem max_zero_eq_add_max_neg (x : ℝ) : max x 0 = x + max (-x) 0 := by
  rcases le_total 0 x with h | h
  · rw [max_eq_left h]
    have : max (-x) 0 = 0 := max_eq_right (by linarith)
    rw [this, add_zero]
  · rw [max_eq_right h]
    have : max (-x) 0 = -x := max_eq_left (by linarith)
    rw [this]
    ring

/-- **Additive decomposition of a masked clipped expectation.**  For any real
valued `E`, mask `Q` and integrable pieces,

  `∫ s, Q.indicator (fun s => max (E s) 0) s
      = ∫ s, Q.indicator E s + ∫ s, Q.indicator (fun s => max (-E s) 0) s.`

This splits the fixed-pair masked frozen expectation into its linear (cost + probe)
part and a clipping correction. -/
theorem integral_indicator_max_eq {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (E : Ω → ℝ) (Q : Set Ω)
    (h1 : Integrable (Q.indicator E) μ)
    (h2 : Integrable (Q.indicator (fun s ↦ max (-E s) 0)) μ) :
    ∫ s, Q.indicator (fun s ↦ max (E s) 0) s ∂μ =
      ∫ s, Q.indicator E s ∂μ + ∫ s, Q.indicator (fun s ↦ max (-E s) 0) s ∂μ := by
  have hfun : Q.indicator (fun s ↦ max (E s) 0) =
      Q.indicator E + Q.indicator (fun s ↦ max (-E s) 0) := by
    funext s
    rw [Pi.add_apply]
    by_cases hs : s ∈ Q
    · rw [Set.indicator_of_mem hs, Set.indicator_of_mem hs, Set.indicator_of_mem hs]
      exact max_zero_eq_add_max_neg (E s)
    · rw [Set.indicator_of_notMem hs, Set.indicator_of_notMem hs,
        Set.indicator_of_notMem hs, add_zero]
  rw [hfun]
  exact integral_add h1 h2

/-- **Masked-entry exchangeability input.**  All masked entries of the frozen tile
matrix have equal expectations.  For iid samples this follows from permutation
invariance of the sample law and of `edgeEvent`; it is stated here with explicit
quantifiers as the exact remaining exchangeability obligation. -/
def MaskedEntryExchangeability {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    {n : ℕ} (E : Ω → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) : Prop :=
  ∀ (i j i' j' : Fin (n + 1)), ∫ s, E s i j ∂μ = ∫ s, E s i' j' ∂μ

/-- **Fixed-pair linear identification input.**  The linear (cost + probe) part of
the fixed-pair masked frozen expectation, normalized by `(n+1)^{2/q}` through the
sequence `fixedPair`, converges to the population tile value.  This is the
Palm/stationary identification of the single-edge conditional law given mask
membership. -/
def FixedPairLinearIdentification (fixedPair popVal : ℕ → ℝ) : Prop :=
  Tendsto (fun n ↦ fixedPair n - popVal n) atTop (𝓝 0)

/-- **Both remaining inputs are consistent with the plan-free LLN.**  The plan-free
LLN follows from masked-entry exchangeability at every `n` (which turns the
normalized pair average into the fixed-pair expectation) together with the fixed-pair
linear identification.  This packages the logical shape of the last step. -/
theorem planFreeTileLLN_of_exchangeability_and_fixedPair
    (mean fixedPair popVal : ℕ → ℝ)
    (hmean : ∀ n, mean n = fixedPair n)
    (hid : FixedPairLinearIdentification fixedPair popVal) :
    PlanFreeTileLLN (fun n ↦ mean n - popVal n) :=
  planFreeTileLLN_of_fixedPairIdentification mean fixedPair popVal hmean hid

end OTSelector.Reconstruction
