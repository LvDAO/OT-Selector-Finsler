import OTSelector.Reconstruction.FinslerOriginalUniformTileAverage

/-!
# Plan-free per-tile law of large numbers: the exact input

This module states and packages the **exact remaining analytic input** of the
tile lane: the plan-free per-tile iid law of large numbers

  `(1/(n+1)^2) · uniformTilePart n c  →  population tile value`

for the masked frozen kernel, with the random probe and the `(n+1)^{2/q}`
normalization of the scale.

**Why it is isolated rather than proved.**  The repo iid counting laws
(`FinslerOriginalFrozenCoreLLN.integral_pairTest_eq`) give the exact expectation of
a *quadratic pair sum* of the form `∑ i ∑ j, Φ (X i, Y j)` for a single fixed kernel
`Φ` whose only randomness comes from the iid pairs.  The frozen tile matrix is
*not* of this form: its entry is

  `maskedFrozenCost (edgeEvent X Y c) (frozenCoreMatrix ... (scale n) t (probe n c)) i j,`

i.e. the kernel depends on the outcome through the *random probe*
`probe = hprobe f t n s c` (a matrix-valued random variable), and the mask
`edgeEvent` depends jointly on the whole configuration.  A general iid pair law with
a random matrix-valued kernel is therefore needed; it is not available in the repo.

**What is proved here.**  The rate form of the input (`PlanFreeTileLLN`), the
reduction `rate bound ⇒ PlanFreeTileLLN`, and the assembly
`plan-free LLN + plan-residual vanishing ⇒ per-tile mean convergence` which is the
remaining shape of the tile-lane mean step.

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

/-- **The plan-free per-tile iid law of large numbers (named input).**
`diff n` is the normalized deviation of the plan-free tile average from the
population tile value; the law says it vanishes. -/
def PlanFreeTileLLN (diff : ℕ → ℝ) : Prop :=
  Tendsto diff atTop (𝓝 0)

/-- **Rate form of the plan-free LLN.**  A vanishing error sequence bounding the
deviation proves the plan-free LLN. -/
theorem planFreeTileLLN_of_rate (diff γ : ℕ → ℝ)
    (hγ : Tendsto γ atTop (𝓝 0)) (h : ∀ n, |diff n| ≤ γ n) :
    PlanFreeTileLLN diff := by
  have habs : Tendsto (fun n ↦ |diff n|) atTop (𝓝 0) :=
    squeeze_zero (fun n ↦ abs_nonneg _) h hγ
  show Tendsto diff atTop (𝓝 0)
  rw [tendsto_zero_iff_abs_tendsto_zero]
  exact habs

/-- **Assembly of the per-tile mean step.**  If the plan-free tile average
converges to the population value (plan-free LLN) and the plan residual vanishes,
then the plan-weighted tile mean converges to the population value: the sum of two
vanishing deviations is vanishing. -/
theorem tileMeanConvergence_of_planFreeLLN_and_residual
    (mean pop free residual : ℕ → ℝ)
    (hdecomp : ∀ n, |(mean n - pop n) - (free n + residual n)| ≤ 0)
    (hfree : PlanFreeTileLLN free) (hres : Tendsto residual atTop (𝓝 0)) :
    Tendsto (fun n ↦ mean n - pop n) atTop (𝓝 0) := by
  have hsum : Tendsto (fun n ↦ free n + residual n) atTop (𝓝 (0 + 0)) :=
    hfree.add hres
  rw [add_zero] at hsum
  refine Tendsto.congr' ?_ hsum
  filter_upwards [Eventually.of_forall hdecomp] with n hn
  have h0 : |(mean n - pop n) - (free n + residual n)| = 0 :=
    le_antisymm hn (abs_nonneg _)
  have hzero : (mean n - pop n) - (free n + residual n) = 0 := abs_eq_zero.mp h0
  linarith

end OTSelector.Reconstruction
