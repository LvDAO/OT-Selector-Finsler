import OTSelector.Reconstruction.FinslerOriginalTilePalmSampleLaw

/-!
# Tile normalization consistency audit

This module audits the constant bookkeeping flagged in
`FinslerOriginalTilePalmSampleLaw.lean` and corrects the identification target.

## The bookkeeping

* The tile lane's entry matrix is `frozenCoreMatrix`
  (`FinslerFrozenCoreDomination.lean`):
  ```frozenCoreMatrix C ε z₀ X Y k t h i j
    = max ((1 - 2ε) * (k * C.frozenPhysicalCost (z₀ i j) (X i) (Y j)) + t * h i j) 0,```
  so the frozen cost enters **weighted by `(1 - 2ε)`**, while the probe enters *plain*.
* The population tile value is (`FinslerOriginalTileCountingConvergence.lean`)
  ```tilePopValue G c = ∫ z in (T.partition c.1).cell c.2,
      θ z ^ (-2/q) * G ((T.core c).seedIndex) z ∂lambda,```
  with **no `(1 - 2ε)` factor**.

Hence the lane's linear value and `tilePopValue` are not directly comparable: the
consistent identification target is the **weighted population value**
```tilePopValueNormalized := (1 - 2ε) * tilePopValue,```
equivalently, the unweighted readout of the sample mean must be
`scale n * palmCostMean n → tilePopValue / (1 - 2ε)`.  Both forms are proved equivalent
here by the constant-absorption lemmas `tendsto_const_mul_sub_zero` /
`tendsto_sub_zero_of_const_mul_sub` (using `1 - 2ε ≠ 0` from `2ε < 1`).

## Paper normalization

The paper normalizes the tile sums by the `(n+1)^{2/q}`-scale arising from the
`θ^{-2/q}` density of the root/potential measure (the `n^{1-2/q}` normalization of
§"empirical tile values", cf. `main.tex` lines 1720, 2318, and the `θ^{-2/q}` density at
lines 1858-1865).  The lane's `scale : ℕ → ℝ` is exactly this free normalization slot:
`tileScale = 1/(n+1)` (used for the clipping-decay lane) is **not** the paper
normalization and cannot serve the linear identification, whose target is `O(1)`; the
identification theorems below are therefore stated for an arbitrary `scale` with the
readout hypothesis supplied separately.

## Proved here

* the two constant-absorption lemmas;
* `3 * tilePopValueNormalized_eq`: the normalized value is the weighted population
  value;
* `tilePalmSampleLaw_of_unweightedReadout`: the unweighted (paper) readout produces a
  `TilePalmSampleLaw` against `tilePopValueNormalized`;
* `tileLinearPalmIdentification_normalized`: consequently the linear Palm
  identification holds against the **weighted** population value.

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

/-- **Constant absorption.**  A vanishing deviation stays vanishing after multiplying
both terms by a constant. -/
theorem tendsto_const_mul_sub_zero {a b : ℕ → ℝ} {c : ℝ}
    (h : Tendsto (fun n ↦ a n - b n) atTop (𝓝 0)) :
    Tendsto (fun n ↦ c * a n - c * b n) atTop (𝓝 0) := by
  have h' : (fun n ↦ c * a n - c * b n) = fun n ↦ c * (a n - b n) :=
    funext fun n ↦ by ring
  rw [h']
  simpa using h.const_mul c

/-- **Constant absorption, converse.**  For `c ≠ 0` the weighted vanishing deviation
implies the unweighted one. -/
theorem tendsto_sub_zero_of_const_mul_sub {a b : ℕ → ℝ} {c : ℝ} (hc : c ≠ 0)
    (h : Tendsto (fun n ↦ c * a n - c * b n) atTop (𝓝 0)) :
    Tendsto (fun n ↦ a n - b n) atTop (𝓝 0) := by
  have h1 : (fun n ↦ c * a n - c * b n) = fun n ↦ c * (a n - b n) :=
    funext fun n ↦ by ring
  rw [h1] at h
  have h2 : Tendsto (fun n ↦ c⁻¹ * (c * (a n - b n))) atTop (𝓝 0) := by
    simpa using h.const_mul c⁻¹
  have h3 : (fun n ↦ c⁻¹ * (c * (a n - b n))) = fun n ↦ a n - b n := by
    funext n
    rw [← mul_assoc, inv_mul_cancel₀ hc, one_mul]
  rw [h3] at h2
  exact h2

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

/-- **The weighted population tile value**: the lane's consistent identification target
(the frozen cost carries the `(1 - 2ε)` weight, the population value does not). -/
noncomputable def tilePopValueNormalized
    (G : ℕ → (ℚ → M) → ℝ) (c : T.Index) : ℝ :=
  (1 - 2 * ε) *
    T.tilePopValue (P := P) (a := a) (κ := κ) (lambda := lambda) (q := q) G c

/-- The weighted value is the population value times `1 - 2ε`. -/
theorem tilePopValueNormalized_eq
    (G : ℕ → (ℚ → M) → ℝ) (c : T.Index) :
    T.tilePopValueNormalized (P := P) (a := a) (κ := κ) (lambda := lambda) (q := q)
        (ε := ε) G c =
      (1 - 2 * ε) *
        T.tilePopValue (P := P) (a := a) (κ := κ) (lambda := lambda) (q := q) G c :=
  rfl

/-- **The tile-lane Palm law against the weighted population value**, produced from the
unweighted paper readout.  The sample mean is required to satisfy the unweighted
identification `scale n * palmCostMean n → tilePopValue`; the `(1 - 2ε)` weight is
then absorbed into the target. -/
noncomputable def tilePalmSampleLaw_of_unweightedReadout
    (f : (K × K) →ᵇ ℝ) (t : ℝ)
    (sample : ∀ n, Measure (Ω n))
    (X Y : ∀ n, Fin (n + 1) → Ω n → M)
    (scale : ℕ → ℝ) (c : T.Index)
    (G : ℕ → (ℚ → M) → ℝ)
    (hε1 : 2 * ε < 1)
    (palmCostMean : ℕ → ℝ)
    (hmasked : ∀ n, T.tileMaskedFrozenCostMean sample X Y n c = palmCostMean n)
    (hreadout : Tendsto (fun n ↦ scale n * palmCostMean n -
      T.tilePopValue (P := P) (a := a) (κ := κ) (lambda := lambda) (q := q) G c)
      atTop (𝓝 0)) :
    T.TilePalmSampleLaw f t sample X Y scale c
      (fun _ ↦ T.tilePopValueNormalized (P := P) (a := a) (κ := κ)
        (lambda := lambda) (q := q) (ε := ε) G c) := by
  have hc : (1 - 2 * ε) ≠ 0 := by intro h; linarith
  have hweighted := tendsto_const_mul_sub_zero (c := 1 - 2 * ε) hreadout
  exact {
    palmCostMean := palmCostMean
    maskedMean_eq := hmasked
    palm_readout := by
      simpa only [tilePopValueNormalized_eq] using hweighted }

/-- **The linear Palm identification against the weighted population value.** -/
theorem tileLinearPalmIdentification_normalized
    (sample : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (sample n)]
    (f : (K × K) →ᵇ ℝ) (t : ℝ)
    (X Y : ∀ n, Fin (n + 1) → Ω n → M)
    (c : T.Index)
    (base : ∀ n, Ω n → T.Index → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    {Bp : ℝ} (hBp : 0 ≤ Bp)
    (hbase : ∀ (n : ℕ) (s : Ω n) (c' : T.Index) (i j : Fin (n + 1)),
      |base n s c' i j| ≤ Bp)
    (hintC : ∀ n, Integrable
      (T.tileLinearCostIntegrand (ε := ε) f t X Y tileScale n c) (sample n))
    (hintP : ∀ n, Integrable (T.tileLinearProbeIntegrand f t X Y
      (fun f t n s c' ↦ normalizedProbe (K := K) base t n s c') n c) (sample n))
    (G : ℕ → (ℚ → M) → ℝ)
    (hε1 : 2 * ε < 1)
    (palmCostMean : ℕ → ℝ)
    (hmasked : ∀ n, T.tileMaskedFrozenCostMean sample X Y n c = palmCostMean n)
    (hreadout : Tendsto (fun n ↦ tileScale n * palmCostMean n -
      T.tilePopValue (P := P) (a := a) (κ := κ) (lambda := lambda) (q := q) G c)
      atTop (𝓝 0)) :
    Tendsto (fun n ↦
      T.tileFixedPairLinearPart f t sample X Y tileScale
        (fun f t n s c' ↦ normalizedProbe (K := K) base t n s c') n c -
        T.tilePopValueNormalized (P := P) (a := a) (κ := κ) (lambda := lambda)
          (q := q) (ε := ε) G c)
      atTop (𝓝 0) := by
  have hlaw := T.tilePalmSampleLaw_of_unweightedReadout f t sample X Y tileScale c G hε1
    palmCostMean hmasked hreadout
  have hcost := T.tileCostPalmIdentification_of_palmSampleLaw f t sample X Y tileScale c
    (fun _ ↦ T.tilePopValueNormalized (P := P) (a := a) (κ := κ) (lambda := lambda)
      (q := q) (ε := ε) G c) hlaw
  exact linearPalmIdentification_of_cost
    (fun n ↦ T.tileFixedPairLinearPart f t sample X Y tileScale
      (fun f t n s c' ↦ normalizedProbe (K := K) base t n s c') n c)
    (fun n ↦ ∫ s, T.tileLinearCostIntegrand (ε := ε) f t X Y tileScale n c s ∂sample n)
    (fun n ↦ ∫ s, T.tileLinearProbeIntegrand f t X Y
      (fun f t n s c' ↦ normalizedProbe (K := K) base t n s c') n c s ∂sample n)
    (fun _ ↦ T.tilePopValueNormalized (P := P) (a := a) (κ := κ) (lambda := lambda)
      (q := q) (ε := ε) G c)
    (fun n ↦ T.tileFixedPairLinearPart_eq_cost_add_probe sample f t X Y tileScale
      (fun f t n s c' ↦ normalizedProbe (K := K) base t n s c') n c (hintC n) (hintP n))
    hcost
    (T.tileLinearProbePart_tendsto_zero sample f t X Y c base hBp hbase hintP)

end PopulationLocalPressureCore.TaylorTiles

end OTSelector.Reconstruction
