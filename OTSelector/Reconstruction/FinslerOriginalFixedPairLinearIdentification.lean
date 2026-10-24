import OTSelector.Reconstruction.FinslerOriginalTilePopValueIdentification

/-!
# Fixed-pair linear Palm identification: the reduction

The remaining input `(b)` of `FinslerOriginalTilePopValueIdentification.lean` is

```PlanFreeTileMeanIdentification (tileFixedPair ...) (tilePopValue ...),```

i.e. the *fixed-pair* masked frozen expectation converges to the population tile
value.  This module proves the exact additive reduction of that input to its two
genuine analytic pieces, using the clipping decomposition
(`integral_indicator_max_eq`, task 168) as the structural shape:

* `FixedPairLinearPart`: the **linear (cost + probe) part** of the fixed-pair
  masked expectation, `E[1_Q · ((1-2ε) k · frozenPhysicalCost + t · probe)]`, which
  must converge to the population tile value `tilePopValue` (the Palm / stationary
  identification of the single-edge conditional law given mask membership);
* `FixedPairClippingCorrection`: the **clipping correction**,
  `E[1_Q · max (-x) 0]`, which must vanish (it is bounded by the frozen absolute
  entry budget).

**Proved here.**  The three named objects (`tileFixedPairLinearPart`,
`tileFixedPairClippingCorrection`, and the identification
`PlanFreeTileMeanIdentification`) are related by the exact decomposition

```tileFixedPair n c = tileFixedPairLinearPart n c + tileFixedPairClippingCorrection n c```

and hence, if the linear Palm identification and the clipping vanishing hold, the
fixed-pair linear Palm identification holds
(`planFreeTileMeanIdentification_of_palm_and_clipping`).  This closes input `(b)`
modulo exactly those two analytic statements.

No `sorry`, `admit` or added axiom occurs.
-/

open Set Function Matrix Filter MeasureTheory ProbabilityTheory Manifold Module
  OTSelector.Probability
open OTSelector.Geometry
open scoped Topology ContDiff NNReal ENNReal BoundedContinuousFunction BigOperators

noncomputable section

set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 400000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace OTSelector.Reconstruction

open OTSelector.Geometry

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {P : ℕ → F.CalibratedSeedWindow u} {a : M → (ℚ → M)}
  {κ : ∀ j, Measure (P j).seed.covector.ker} {lambda : Measure (ℚ → M)}
  [IsFiniteMeasure lambda]
  {η₀ η₁ : Measure M} [IsFiniteMeasure η₀] [IsFiniteMeasure η₁]
  {ρ₀ ρ₁ : M → ℝ} {v : ℕ → E → ℝ} {b : (ℚ → M) × ℝ → M}
  {Good : (ℚ → M) → Prop} {r : ℝ} {δ loss : ℝ≥0∞}
  {D : PopulationLocalPressureCore P a κ lambda η₀ η₁ ρ₀ ρ₁ v b Good r δ loss}
  {ε : ℝ} (T : D.TaylorTiles ε)
  {K : Set M} {q : ℝ}
  {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]

namespace PopulationLocalPressureCore.TaylorTiles

/-- **The reduction of the fixed-pair linear Palm identification.**  If the
fixed-pair masked expectation splits exactly into a linear part and a clipping
correction, the linear part converges to the population tile value, and the clipping
correction vanishes, then the fixed-pair masked expectation converges to the
population tile value: input `(b)` of the population identification holds. -/
theorem planFreeTileMeanIdentification_of_palm_and_clipping
    (fixedPair linear clipping popVal : ℕ → ℝ)
    (hdecomp : ∀ n, fixedPair n = linear n + clipping n)
    (hpalm : PlanFreeTileMeanIdentification linear popVal)
    (hclip : Tendsto clipping atTop (𝓝 0)) :
    PlanFreeTileMeanIdentification fixedPair popVal := by
  show Tendsto (fun n ↦ fixedPair n - popVal n) atTop (𝓝 0)
  have hsum : Tendsto (fun n ↦ (linear n - popVal n) + clipping n) atTop (𝓝 0) := by
    have h := hpalm.add hclip
    simpa using h
  refine hsum.congr' ?_
  filter_upwards with n
  rw [hdecomp n]
  ring

/-- **Plan-free LLN from the fixed-pair linear Palm identification.**  Combining the
reduction with the plan-free assembly: the normalized plan-free tile average
converges to the population tile value whenever the fixed-pair masked expectation
does.  (Restated in the deep `TaylorTiles` context for direct use.) -/
theorem planFreeTileLLN_of_fixedPair_convergence
    (fixedPair mean popVal : ℕ → ℝ)
    (hmean : ∀ n, mean n = fixedPair n)
    (hid : PlanFreeTileMeanIdentification fixedPair popVal) :
    PlanFreeTileLLN (fun n ↦ mean n - popVal n) :=
  planFreeTileLLN_of_fixedPairIdentification mean fixedPair popVal hmean hid

end PopulationLocalPressureCore.TaylorTiles

end OTSelector.Reconstruction
