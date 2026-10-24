import OTSelector.Reconstruction.FinslerOriginalTileScaleConsistency
import OTSelector.Reconstruction.FinslerOriginalTileFrozenBoundWiring

/-!
# Bounded clipping error insertion into the paper normalization

This module completes the last bookkeeping step of the tile normalization lane.

## The finding that resolves the bounded-correction problem

The clipping integrand is
```max (-((1 - 2ε) * (scale n * frozenPhysicalCost) + t * probe), 0).```

The earlier budget (`tileSlackBudget`) bounded it by
`(1 - 2ε) * (scale n * R n) + |t| * Bp/(n+1)`, which *at the paper scale*
`tileScalePaper q n = (n+1)^{2/q}` is only bounded, not vanishing.

That budget is however **crude**: it ignores the sign of the frozen physical cost.
The frozen physical cost of a retained edge is a *slack*, i.e. nonnegative.  With
`0 ≤ frozenPhysicalCost` and `0 ≤ 1 - 2ε`, `0 ≤ scale n` we get
```(1 - 2ε) * (scale n * frozenPhysicalCost) ≥ 0,```
so on the clipping event the clipper pays at most the probe term:
```max (-(a + b)) 0 ≤ |b|   for   0 ≤ a.```

Hence (`tileClippingIntegrand_le_abs_probe`)

```clipping correction entry ≤ |t * probe|,  and in expectation
  clipping correction n ≤ |t| * Bp/(n+1) = O(1/n) → 0```

(`tileFixedPairClippingCorrection_le_probe`,
`tileFixedPairClippingCorrection_tendsto_zero`) at **any** scale, paper or empirical.
This removes the scale split of `FinslerOriginalTileScaleConsistency.lean` entirely:
the clipping correction is `o(1)`, so it is inserted into the paper normalization with
a relative error factor tending to one (`tendsto_ratio_of_correction_vanishing` and
`tileFixedPair_tendsto_of_linearPart`).  The paper's `n^{1-2/q}` estimate
(`main.tex` lines 1720, 2318) is therefore consumed with correction error `o(1)`, not
merely bounded.

No `sorry`, `admit` or added axiom occurs.
-/

open Set Function Matrix Filter MeasureTheory ProbabilityTheory Manifold Module
  OTSelector.Probability
open OTSelector.Geometry
open scoped Topology ContDiff NNReal ENNReal BoundedContinuousFunction BigOperators

noncomputable section

set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 400000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace OTSelector.Reconstruction

/-- **The nonnegative part of `-(a + b)` is bounded by `|b|` when `a ≥ 0`.**  This is
the sign observation that makes the clipping correction small: the clipper only pays
for the negative *probe* when the cost part is nonnegative. -/
theorem max_neg_add_le_abs {a b : ℝ} (ha : 0 ≤ a) : max (-(a + b)) 0 ≤ |b| := by
  refine max_le ?_ (abs_nonneg b)
  linarith [neg_le_abs b]

/-- **Relative error factor tending to one.**  If a value converges to a nonzero limit
and a nonnegative correction vanishes, the corrected value equals the value up to a
relative error factor tending to one. -/
theorem tendsto_ratio_of_correction_vanishing (linear clip : ℕ → ℝ) {L : ℝ}
    (hL : L ≠ 0)
    (hlin : Tendsto linear atTop (𝓝 L)) (hclip : Tendsto clip atTop (𝓝 0)) :
    Tendsto (fun n ↦ (linear n + clip n) / linear n) atTop (𝓝 1) := by
  have hne : ∀ᶠ n in atTop, linear n ≠ 0 :=
    hlin.eventually (isOpen_ne.mem_nhds hL)
  have hdiv : Tendsto (fun n ↦ clip n / linear n) atTop (𝓝 (0 / L)) :=
    hclip.div hlin hL
  have h1 : Tendsto (fun n ↦ 1 + clip n / linear n) atTop (𝓝 (1 + 0 / L)) :=
    tendsto_const_nhds.add hdiv
  have hcongr : (fun n ↦ (linear n + clip n) / linear n) =ᶠ[atTop]
      (fun n ↦ 1 + clip n / linear n) := by
    filter_upwards [hne] with n hn
    field_simp
  have h1' : Tendsto (fun n ↦ 1 + clip n / linear n) atTop (𝓝 1) := by
    simpa using h1
  exact Tendsto.congr' hcongr.symm h1'

end OTSelector.Reconstruction

namespace OTSelector.Reconstruction

open OTSelector.Geometry

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  [MeasurableSpace.CountablySeparated (ℚ → M)]
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

/-- The clipping integrand is nonnegative pointwise. -/
theorem tileClippingIntegrand_nonneg
    (f : (K × K) →ᵇ ℝ) (t : ℝ)
    (X Y : ∀ n, Fin (n + 1) → Ω n → M)
    (scale : ℕ → ℝ)
    (hprobe : ((K × K) →ᵇ ℝ) → ℝ → ∀ n, Ω n → T.Index →
      Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (n : ℕ) (c : T.Index) (s : Ω n) :
    0 ≤ T.tileClippingIntegrand (ε := ε) f t X Y scale hprobe n c s := by
  simp only [tileClippingIntegrand]
  by_cases h : (⟨0, Nat.succ_pos n⟩, ⟨0, Nat.succ_pos n⟩) ∈
      T.edgeEvent (fun i ↦ X n i s) (fun i ↦ Y n i s) c
  · rw [Set.indicator_of_mem h]
    exact le_max_right _ 0
  · rw [Set.indicator_of_notMem h]

/-- **The clipping integrand is bounded by the absolute probe term** at the
distinguished pair, provided the frozen cost there is a nonnegative slack and
ε ≤ 1/2. -/
theorem tileClippingIntegrand_le_abs_probe
    (f : (K × K) →ᵇ ℝ) (t : ℝ)
    (X Y : ∀ n, Fin (n + 1) → Ω n → M)
    (scale : ℕ → ℝ)
    (hprobe : ((K × K) →ᵇ ℝ) → ℝ → ∀ n, Ω n → T.Index →
      Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (n : ℕ) (c : T.Index) (s : Ω n)
    (hε : ε ≤ 1 / 2) (hscale : 0 ≤ scale n)
    (hphys : 0 ≤ (T.core c).frozenPhysicalCost (T.reference c)
      (X n ⟨0, Nat.succ_pos n⟩ s) (Y n ⟨0, Nat.succ_pos n⟩ s)) :
    T.tileClippingIntegrand (ε := ε) f t X Y scale hprobe n c s ≤
      |t * hprobe f t n s c ⟨0, Nat.succ_pos n⟩ ⟨0, Nat.succ_pos n⟩| := by
  have hε0 : 0 ≤ 1 - 2 * ε := by linarith
  have hcost : 0 ≤ (1 - 2 * ε) *
      (scale n * (T.core c).frozenPhysicalCost (T.reference c)
        (X n ⟨0, Nat.succ_pos n⟩ s) (Y n ⟨0, Nat.succ_pos n⟩ s)) :=
    mul_nonneg hε0 (mul_nonneg hscale hphys)
  simp only [tileClippingIntegrand]
  by_cases h : (⟨0, Nat.succ_pos n⟩, ⟨0, Nat.succ_pos n⟩) ∈
      T.edgeEvent (fun i ↦ X n i s) (fun i ↦ Y n i s) c
  · rw [Set.indicator_of_mem h]
    simp only [tileLinearTerm]
    exact max_neg_add_le_abs hcost
  · rw [Set.indicator_of_notMem h]
    exact abs_nonneg _

/-- **The clipping correction is bounded by the vanishing probe bound.** -/
theorem tileFixedPairClippingCorrection_le_probe
    (sample : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (sample n)]
    (f : (K × K) →ᵇ ℝ) (t : ℝ)
    (X Y : ∀ n, Fin (n + 1) → Ω n → M)
    (scale : ℕ → ℝ)
    (hprobe : ((K × K) →ᵇ ℝ) → ℝ → ∀ n, Ω n → T.Index →
      Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (n : ℕ) (c : T.Index)
    (hε : ε ≤ 1 / 2) (hscale : ∀ n, 0 ≤ scale n)
    (hphys : ∀ (n : ℕ) (s : Ω n), 0 ≤ (T.core c).frozenPhysicalCost
      (T.reference c) (X n ⟨0, Nat.succ_pos n⟩ s) (Y n ⟨0, Nat.succ_pos n⟩ s))
    {Bp : ℝ} (hBp : 0 ≤ Bp)
    (hG : ∀ (n : ℕ) (s : Ω n) (i j : Fin (n + 1)),
      |hprobe f t n s c i j| ≤ Bp / ((n + 1 : ℕ) : ℝ))
    (hint : Integrable (T.tileClippingIntegrand (ε := ε) f t X Y scale hprobe n c)
      (sample n)) :
    T.tileFixedPairClippingCorrection f t sample X Y scale hprobe n c ≤
      |t| * (Bp / ((n + 1 : ℕ) : ℝ)) := by
  have hbound : (∫ s, T.tileClippingIntegrand (ε := ε) f t X Y scale hprobe n c s
        ∂sample n) ≤ ∫ _s : Ω n, |t| * (Bp / ((n + 1 : ℕ) : ℝ)) ∂sample n := by
    refine integral_mono_ae hint (integrable_const _) (Eventually.of_forall ?_)
    intro s
    calc T.tileClippingIntegrand (ε := ε) f t X Y scale hprobe n c s
        ≤ |t * hprobe f t n s c ⟨0, Nat.succ_pos n⟩ ⟨0, Nat.succ_pos n⟩| :=
          T.tileClippingIntegrand_le_abs_probe f t X Y scale hprobe n c s hε
            (hscale n) (hphys n s)
      _ = |t| * |hprobe f t n s c ⟨0, Nat.succ_pos n⟩ ⟨0, Nat.succ_pos n⟩| := by
          rw [abs_mul]
      _ ≤ |t| * (Bp / ((n + 1 : ℕ) : ℝ)) :=
          mul_le_mul_of_nonneg_left (hG n s _ _) (abs_nonneg t)
  calc T.tileFixedPairClippingCorrection f t sample X Y scale hprobe n c
      = ∫ s, T.tileClippingIntegrand (ε := ε) f t X Y scale hprobe n c s ∂sample n := rfl
    _ ≤ ∫ _s : Ω n, |t| * (Bp / ((n + 1 : ℕ) : ℝ)) ∂sample n := hbound
    _ = |t| * (Bp / ((n + 1 : ℕ) : ℝ)) := by simp

/-- **The clipping correction vanishes at any scale** (paper or empirical), because
its absolute size is bounded by the decaying probe term. -/
theorem tileFixedPairClippingCorrection_tendsto_zero
    (sample : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (sample n)]
    (f : (K × K) →ᵇ ℝ) (t : ℝ)
    (X Y : ∀ n, Fin (n + 1) → Ω n → M)
    (scale : ℕ → ℝ)
    (hprobe : ((K × K) →ᵇ ℝ) → ℝ → ∀ n, Ω n → T.Index →
      Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (c : T.Index)
    (hε : ε ≤ 1 / 2) (hscale : ∀ n, 0 ≤ scale n)
    (hphys : ∀ (n : ℕ) (s : Ω n), 0 ≤ (T.core c).frozenPhysicalCost
      (T.reference c) (X n ⟨0, Nat.succ_pos n⟩ s) (Y n ⟨0, Nat.succ_pos n⟩ s))
    {Bp : ℝ} (hBp : 0 ≤ Bp)
    (hG : ∀ (n : ℕ) (s : Ω n) (i j : Fin (n + 1)),
      |hprobe f t n s c i j| ≤ Bp / ((n + 1 : ℕ) : ℝ))
    (hint : ∀ n, Integrable (T.tileClippingIntegrand (ε := ε) f t X Y scale hprobe n c)
      (sample n)) :
    Tendsto (fun n ↦ T.tileFixedPairClippingCorrection f t sample X Y scale hprobe n c)
      atTop (𝓝 0) := by
  have hnonneg : ∀ n, 0 ≤ T.tileFixedPairClippingCorrection f t sample X Y scale
      hprobe n c := by
    intro n
    exact integral_nonneg (fun s ↦ T.tileClippingIntegrand_nonneg f t X Y scale hprobe n c s)
  have hupper : ∀ n, |T.tileFixedPairClippingCorrection f t sample X Y scale hprobe n c|
      ≤ |t| * (Bp / ((n + 1 : ℕ) : ℝ)) := by
    intro n
    rw [abs_of_nonneg (hnonneg n)]
    exact T.tileFixedPairClippingCorrection_le_probe sample f t X Y scale hprobe n c
      hε hscale hphys hBp hG (hint n)
  rw [tendsto_zero_iff_abs_tendsto_zero]
  refine squeeze_zero (fun n ↦ abs_nonneg _) hupper ?_
  simpa using (probeBound_tendsto_zero hBp).const_mul |t|

/-- **The absolute relative error of the clipping insertion is vanishing**: the
fixed-pair masked expectation differs from its linear part by at most
|t| * Bp/(n+1). -/
theorem tileFixedPair_sub_linearPart_abs_le
    (sample : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (sample n)]
    (f : (K × K) →ᵇ ℝ) (t : ℝ)
    (X Y : ∀ n, Fin (n + 1) → Ω n → M)
    (scale : ℕ → ℝ)
    (hprobe : ((K × K) →ᵇ ℝ) → ℝ → ∀ n, Ω n → T.Index →
      Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (n : ℕ) (c : T.Index)
    (hε : ε ≤ 1 / 2) (hscale : ∀ n, 0 ≤ scale n)
    (hphys : ∀ (n : ℕ) (s : Ω n), 0 ≤ (T.core c).frozenPhysicalCost
      (T.reference c) (X n ⟨0, Nat.succ_pos n⟩ s) (Y n ⟨0, Nat.succ_pos n⟩ s))
    {Bp : ℝ} (hBp : 0 ≤ Bp)
    (hG : ∀ (n : ℕ) (s : Ω n) (i j : Fin (n + 1)),
      |hprobe f t n s c i j| ≤ Bp / ((n + 1 : ℕ) : ℝ))
    (hintLin : Integrable (T.tileLinearIntegrand (ε := ε) f t X Y scale hprobe n c)
      (sample n))
    (hintClip : Integrable (T.tileClippingIntegrand (ε := ε) f t X Y scale hprobe n c)
      (sample n)) :
    |T.tileFixedPair f t sample X Y scale hprobe n c -
      T.tileFixedPairLinearPart f t sample X Y scale hprobe n c| ≤
      |t| * (Bp / ((n + 1 : ℕ) : ℝ)) := by
  have hnonneg : 0 ≤ T.tileFixedPairClippingCorrection f t sample X Y scale hprobe n c :=
    integral_nonneg (fun s ↦ T.tileClippingIntegrand_nonneg f t X Y scale hprobe n c s)
  have hdecomp := T.tileFixedPair_eq_linear_add_clipping sample f t X Y scale hprobe n c
    hintLin hintClip
  have heq : T.tileFixedPair f t sample X Y scale hprobe n c -
      T.tileFixedPairLinearPart f t sample X Y scale hprobe n c =
      T.tileFixedPairClippingCorrection f t sample X Y scale hprobe n c := by
    rw [hdecomp]
    ring
  rw [heq, abs_of_nonneg hnonneg]
  exact T.tileFixedPairClippingCorrection_le_probe sample f t X Y scale hprobe n c
    hε hscale hphys hBp hG hintClip

/-- **Insertion into the paper normalization**: the fixed-pair masked expectation and
its linear part have the same limit, because the clipping correction is o(1) at any
scale.  This is the precise estimate consumed by the pressure-lower readout. -/
theorem tileFixedPair_tendsto_of_linearPart
    (sample : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (sample n)]
    (f : (K × K) →ᵇ ℝ) (t : ℝ)
    (X Y : ∀ n, Fin (n + 1) → Ω n → M)
    (scale : ℕ → ℝ)
    (hprobe : ((K × K) →ᵇ ℝ) → ℝ → ∀ n, Ω n → T.Index →
      Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (c : T.Index)
    (hε : ε ≤ 1 / 2) (hscale : ∀ n, 0 ≤ scale n)
    (hphys : ∀ (n : ℕ) (s : Ω n), 0 ≤ (T.core c).frozenPhysicalCost
      (T.reference c) (X n ⟨0, Nat.succ_pos n⟩ s) (Y n ⟨0, Nat.succ_pos n⟩ s))
    {Bp : ℝ} (hBp : 0 ≤ Bp)
    (hG : ∀ (n : ℕ) (s : Ω n) (i j : Fin (n + 1)),
      |hprobe f t n s c i j| ≤ Bp / ((n + 1 : ℕ) : ℝ))
    (hintLin : ∀ n, Integrable (T.tileLinearIntegrand (ε := ε) f t X Y scale hprobe n c)
      (sample n))
    (hintClip : ∀ n, Integrable (T.tileClippingIntegrand (ε := ε) f t X Y scale hprobe n c)
      (sample n))
    {L : ℝ}
    (hlim : Tendsto (fun n ↦ T.tileFixedPairLinearPart f t sample X Y scale hprobe n c)
      atTop (𝓝 L)) :
    Tendsto (fun n ↦ T.tileFixedPair f t sample X Y scale hprobe n c) atTop (𝓝 L) := by
  have hclip := T.tileFixedPairClippingCorrection_tendsto_zero sample f t X Y scale
    hprobe c hε hscale hphys hBp hG hintClip
  have hsum : Tendsto (fun n ↦ T.tileFixedPairLinearPart f t sample X Y scale hprobe n c +
      T.tileFixedPairClippingCorrection f t sample X Y scale hprobe n c) atTop (𝓝 (L + 0)) :=
    hlim.add hclip
  have heq : (fun n ↦ T.tileFixedPairLinearPart f t sample X Y scale hprobe n c +
      T.tileFixedPairClippingCorrection f t sample X Y scale hprobe n c) =
      fun n ↦ T.tileFixedPair f t sample X Y scale hprobe n c := by
    funext n
    exact (T.tileFixedPair_eq_linear_add_clipping sample f t X Y scale hprobe n c
      (hintLin n) (hintClip n)).symm
  rw [heq] at hsum
  simpa using hsum

/-- **The clipping correction vanishes from the retained-edge window data alone**:
on the retained window the frozen physical cost is a positive definite quadratic
form, hence nonnegative (repo lemma `frozenPhysicalCost_nonneg`), so the sign
hypothesis of `tileFixedPairClippingCorrection_tendsto_zero` is automatically
satisfied for the lane's retained edges. -/
theorem tileFixedPairClippingCorrection_tendsto_zero_of_retainedEdge
    (sample : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (sample n)]
    (f : (K × K) →ᵇ ℝ) (t : ℝ)
    (X Y : ∀ n, Fin (n + 1) → Ω n → M)
    (scale : ℕ → ℝ)
    (hprobe : ((K × K) →ᵇ ℝ) → ℝ → ∀ n, Ω n → T.Index →
      Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (c : T.Index)
    (hε : ε ≤ 1 / 2) (hscale : ∀ n, 0 ≤ scale n)
    (hz₀ : T.reference c ∈ (T.cover c.1).centers)
    (hp : ∀ (n : ℕ) (s : Ω n),
      (u (X n ⟨0, Nat.succ_pos n⟩ s), u (Y n ⟨0, Nat.succ_pos n⟩ s)) ∈
        (T.core c).window.region)
    {Bp : ℝ} (hBp : 0 ≤ Bp)
    (hG : ∀ (n : ℕ) (s : Ω n) (i j : Fin (n + 1)),
      |hprobe f t n s c i j| ≤ Bp / ((n + 1 : ℕ) : ℝ))
    (hint : ∀ n, Integrable (T.tileClippingIntegrand (ε := ε) f t X Y scale hprobe n c)
      (sample n)) :
    Tendsto (fun n ↦ T.tileFixedPairClippingCorrection f t sample X Y scale hprobe n c)
      atTop (𝓝 0) := by
  have hphys : ∀ (n : ℕ) (s : Ω n), 0 ≤ (T.core c).frozenPhysicalCost
      (T.reference c) (X n ⟨0, Nat.succ_pos n⟩ s) (Y n ⟨0, Nat.succ_pos n⟩ s) :=
    fun n s ↦ frozenPhysicalCost_nonneg (T.cover c.1) hz₀ (hp n s)
  exact T.tileFixedPairClippingCorrection_tendsto_zero sample f t X Y scale hprobe c
    hε hscale hphys hBp hG hint

end PopulationLocalPressureCore.TaylorTiles

end OTSelector.Reconstruction
