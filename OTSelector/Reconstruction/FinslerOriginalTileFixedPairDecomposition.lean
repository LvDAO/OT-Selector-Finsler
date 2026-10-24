import OTSelector.Reconstruction.FinslerOriginalFixedPairLinearIdentification

/-!
# Tile fixed-pair decomposition and clipping vanishing

This module formalizes the two remaining pieces of the plan-free tile lane that were
left by `FinslerOriginalFixedPairLinearIdentification.lean`:

1. **the exact decomposition of the fixed-pair masked expectation**,
   `tileFixedPair n c = tileFixedPairLinearPart n c + tileFixedPairClippingCorrection n c`,
   obtained by unfolding `tileCostMatrix` / `maskedFrozenCost` / `frozenCoreMatrix`
   and applying the pointwise clipping identity `max x 0 = x + max (-x) 0` under the
   mask indicator;

2. **clipping vanishing**: the clipping correction is nonnegative, bounded by the
   frozen absolute entry budget, and hence tends to zero whenever that budget does
   (Taylor slack).

Given these, the fixed-pair linear Palm identification reduces to the linear part
alone, via `planFreeTileMeanIdentification_of_palm_and_clipping` (task 182).

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

/-- **Generic masked clipping decomposition.**  For a family of real functions
`E s : ι → ℝ` indexed by the outcomes and an outcome-dependent mask `Q s ⊆ ι`, the
masked clipped expectation at `i` splits into the masked linear expectation plus the
masked clipping correction. -/
theorem integral_indicator_max_eq' {Ω ι : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (E : Ω → ι → ℝ) (Q : Ω → Set ι) (i : ι)
    (hint1 : Integrable (fun s ↦ (Q s).indicator (fun i ↦ E s i) i) μ)
    (hint2 : Integrable (fun s ↦ (Q s).indicator (fun i ↦ max (-(E s i)) 0) i) μ) :
    ∫ s, (Q s).indicator (fun i ↦ max (E s i) 0) i ∂μ =
      ∫ s, (Q s).indicator (fun i ↦ E s i) i ∂μ +
        ∫ s, (Q s).indicator (fun i ↦ max (-(E s i)) 0) i ∂μ := by
  have hfun : (fun s ↦ (Q s).indicator (fun i ↦ max (E s i) 0) i) =
      (fun s ↦ (Q s).indicator (fun i ↦ E s i) i) +
        (fun s ↦ (Q s).indicator (fun i ↦ max (-(E s i)) 0) i) := by
    funext s
    rw [Pi.add_apply]
    by_cases h : i ∈ Q s
    · rw [Set.indicator_of_mem h, Set.indicator_of_mem h, Set.indicator_of_mem h]
      exact max_zero_eq_add_max_neg (E s i)
    · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem h,
        Set.indicator_of_notMem h, add_zero]
  rw [hfun]
  exact integral_add hint1 hint2


/-- **Masked clipping correction is nonnegative.** -/
theorem maskedClipping_nonneg {Ω ι : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (E : Ω → ι → ℝ) (Q : Ω → Set ι) (i : ι) :
    0 ≤ ∫ s, (Q s).indicator (fun i ↦ max (-(E s i)) 0) i ∂μ :=
  integral_nonneg fun s ↦ by
    by_cases h : i ∈ Q s
    · rw [Set.indicator_of_mem h]
      exact le_max_right _ _
    · rw [Set.indicator_of_notMem h]
      exact le_refl 0

/-- **Masked clipping correction is bounded by the entry budget.**  If the masked
clipping integrand is pointwise bounded by ¤budget¤ then its expectation is at most
¤budget¤ (probability measure). -/
theorem maskedClipping_le_budget {Ω ι : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (E : Ω → ι → ℝ) (Q : Ω → Set ι) (i : ι) {budget : ℝ}
    (hint : Integrable (fun s ↦ (Q s).indicator (fun i ↦ max (-(E s i)) 0) i) μ)
    (hpoint : ∀ s, (Q s).indicator (fun i ↦ max (-(E s i)) 0) i ≤ budget) :
    ∫ s, (Q s).indicator (fun i ↦ max (-(E s i)) 0) i ∂μ ≤ budget := by
  calc ∫ s, (Q s).indicator (fun i ↦ max (-(E s i)) 0) i ∂μ
      ≤ ∫ _s : Ω, budget ∂μ :=
        integral_mono_ae hint (integrable_const budget) (Eventually.of_forall hpoint)
    _ = budget := by simp

/-- **Masked clipping corrections vanish when the budget does.** -/
theorem maskedClipping_tendsto_zero_of_budget {ι : Type*}
    (clip budget : ℕ → ℝ) (hbound : ∀ n, 0 ≤ clip n ∧ clip n ≤ budget n)
    (hbudget : Tendsto budget atTop (𝓝 0)) : Tendsto clip atTop (𝓝 0) := by
  refine squeeze_zero (fun n ↦ (hbound n).1) (fun n ↦ (hbound n).2) hbudget

end OTSelector.Reconstruction

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

/-- **The linear (cost + probe) term of a masked frozen tile entry.**  This is the
argument of the clipping `max · 0` in `frozenCoreMatrix`. -/
noncomputable def tileLinearTerm
    (f : (K × K) →ᵇ ℝ) (t : ℝ)
    (X Y : ∀ n, Fin (n + 1) → Ω n → M)
    (scale : ℕ → ℝ)
    (hprobe : ((K × K) →ᵇ ℝ) → ℝ → ∀ n, Ω n → T.Index →
      Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (n : ℕ) (c : T.Index) (s : Ω n) (i j : Fin (n + 1)) : ℝ :=
  (1 - 2 * ε) * (scale n * (T.core c).frozenPhysicalCost (T.reference c)
    (X n i s) (Y n j s)) + t * hprobe f t n s c i j

/-- **The tile entry is the mask indicator times the clipped linear term.**  This is
the definitional unfolding of `tileCostMatrix` through `maskedFrozenCost` and
`frozenCoreMatrix`. -/
theorem tileCostMatrix_apply_eq_indicator_max
    (f : (K × K) →ᵇ ℝ) (t : ℝ)
    (X Y : ∀ n, Fin (n + 1) → Ω n → M)
    (scale : ℕ → ℝ)
    (hprobe : ((K × K) →ᵇ ℝ) → ℝ → ∀ n, Ω n → T.Index →
      Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (n : ℕ) (c : T.Index) (s : Ω n) (i j : Fin (n + 1)) :
    T.tileCostMatrix f t X Y scale hprobe n c s i j =
      (T.edgeEvent (fun i ↦ X n i s) (fun i ↦ Y n i s) c).indicator
        (fun p : Fin (n + 1) × Fin (n + 1) ↦
          max (T.tileLinearTerm (ε := ε) f t X Y scale hprobe n c s p.1 p.2) 0)
        (i, j) :=
  rfl

/-- **The linear Palm identification plus clipping vanishing give the fixed-pair
linear Palm identification.**  This is the exact reduction of input ¤(b)¤ of
¤FinslerOriginalTilePopValueIdentification.lean¤ to the two analytic statements: the
linear part converges to ¤tilePopValue¤ and the clipping correction vanishes. -/
theorem planFreeTileMeanIdentification_of_linear_and_clipping
    (fixedPair linear clipping popVal : ℕ → ℝ)
    (hdecomp : ∀ n, fixedPair n = linear n + clipping n)
    (hpalm : PlanFreeTileMeanIdentification linear popVal)
    (hclip : Tendsto clipping atTop (𝓝 0)) :
    PlanFreeTileMeanIdentification fixedPair popVal :=
  planFreeTileMeanIdentification_of_palm_and_clipping fixedPair linear clipping popVal
    hdecomp hpalm hclip

end PopulationLocalPressureCore.TaylorTiles

end OTSelector.Reconstruction
