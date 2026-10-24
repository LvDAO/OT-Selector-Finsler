import OTSelector.Reconstruction.FinslerOriginalConcretePalmSampleLaw
import OTSelector.Reconstruction.FinslerOriginalTileMeanValues

/-!
# Field (b) of the concrete scene lane from the empirical tile counting convergence

Continues `FinslerOriginalConcretePalmSampleLaw.lean` (field (a) computed for the
concrete empirical scene lane) and derives field (b), the sample-level Campbell
bridge, from the shape of the per-tile empirical counting convergence.

## Field (b)

```(1 - 2ε) * (scale n * cloudAverageReadout n) → tilePopValue.```

It follows from exactly three named inputs, the paper's route (i):

1. `hlln`: the empirical readout of the cloud is convergent,
   `sceneCloudAverage n - popReadout n → 0` (the per-tile LLN in the cloud
   normalization; from `RootedTileMeanConvergence`-shaped per-tile error budgets by
   `tileError_tendsto_zero_of_budget`);
2. `hpop`: the population Campbell/normalization identity
   `(1 - 2ε) * (scale n * popReadout n) → tilePopValue`;
3. `hbounded`: the paper multiplier is bounded, `|(1 - 2ε) * scale n| ≤ C`.

The composite `tilePalmSampleLaw_sceneCloud_of_countingConvergence` then produces
the full `TilePalmSampleLaw` for the concrete lane with BOTH fields discharged:
field (a) by the cloud-average computation of
`FinslerOriginalConcretePalmSampleLaw.lean`, field (b) by
`sceneCloudReadout_tendsto_popValue`.

## Conventions bridged

The counting lane normalizes by `1/(n+1)` while the tile Palm lane uses a
probability sample law.  `sceneCloudCounting` is the unnormalized counting measure on
the cloud slots; `integral_counting_eq_empirical` proves that the normalized
counting integral is the integral against the probability empirical sample law, so
the two normalizations are the same sequence.

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

/-! ## The abstract composition lemmas -/

/-- **Bounded times vanishing is vanishing.** -/
theorem tendsto_zero_of_bounded_mul (a b : ℕ → ℝ) {C : ℝ}
    (hC : ∀ n, |a n| ≤ C) (hb : Tendsto b atTop (𝓝 0)) :
    Tendsto (fun n ↦ a n * b n) atTop (𝓝 0) := by
  rw [tendsto_zero_iff_abs_tendsto_zero]
  have hb' : Tendsto (fun n ↦ |b n|) atTop (𝓝 0) := by
    simpa using hb.abs
  have hbound : Tendsto (fun n ↦ C * |b n|) atTop (𝓝 0) := by
    simpa using hb'.const_mul C
  refine squeeze_zero (fun n ↦ abs_nonneg _) (fun n ↦ ?_) hbound
  simp only [Function.comp_apply, abs_mul]
  exact mul_le_mul_of_nonneg_right (hC n) (abs_nonneg _)

/-- **The paper readout composition** (field (b) in abstract form): if the readout
converges to the population mean and the population mean is correctly normalized,
then the normalized readout converges to the population tile Campbell value. -/
theorem tileReadout_tendsto_of_population_identification
    (readout popReadout : ℕ → ℝ) (scale : ℕ → ℝ) {L C : ℝ}
    (hbounded : ∀ n, |(1 - 2 * ε) * scale n| ≤ C)
    (hlln : Tendsto (fun n ↦ readout n - popReadout n) atTop (𝓝 0))
    (hpop : Tendsto (fun n ↦ (1 - 2 * ε) * (scale n * popReadout n) - L)
      atTop (𝓝 0)) :
    Tendsto (fun n ↦ (1 - 2 * ε) * (scale n * readout n) - L) atTop (𝓝 0) := by
  have hsplit : (fun n ↦ (1 - 2 * ε) * (scale n * readout n) - L) =
      (fun n ↦ ((1 - 2 * ε) * scale n) * (readout n - popReadout n) +
        ((1 - 2 * ε) * (scale n * popReadout n) - L)) := by
    funext n
    ring
  rw [hsplit]
  have h := (tendsto_zero_of_bounded_mul (fun n ↦ (1 - 2 * ε) * scale n)
    (fun n ↦ readout n - popReadout n) hbounded hlln).add hpop
  simpa using h

/-- **Per-tile convergence from a vanishing total error budget** (the shape of
`RootedTileMeanConvergence`): if the per-tile errors are nonnegative and bounded by
the tile budgets, and the total budget vanishes, then the error of any fixed tile
vanishes. -/
theorem tileError_tendsto_zero_of_budget [Fintype T.Index]
    (err budget : ℕ → T.Index → ℝ)
    (herrLe : ∀ n (c : T.Index), 0 ≤ err n c ∧ err n c ≤ budget n c)
    (hbudget : Tendsto (fun n ↦ ∑ c, budget n c) atTop (𝓝 0)) (c : T.Index) :
    Tendsto (fun n ↦ err n c) atTop (𝓝 0) := by
  refine squeeze_zero (fun n ↦ (herrLe n c).1) (fun n ↦ ?_) hbudget
  refine le_trans (herrLe n c).2 (Finset.single_le_sum (f := fun c' ↦ budget n c') ?_ ?_)
  · intro c' _
    exact le_trans (herrLe n c').1 (herrLe n c').2
  · exact Finset.mem_univ c

namespace PopulationLocalPressureCore.TaylorTiles

/-! ## The cloud counting normalization -/

/-- The unnormalized counting measure on the cloud slots: the empirical counting
normalization of the per-tile counting lane. -/
noncomputable def sceneCloudCounting (n : ℕ) : Measure (Fin (n + 1)) :=
  ∑ s : Fin (n + 1), Measure.dirac s

/-- The counting measure is the probability empirical sample law scaled by
`(n+1)⁻¹`. -/
theorem sceneCloudSample_eq_inv_smul_counting (n : ℕ) :
    sceneCloudSample n = ((n + 1 : ℕ) : ℝ≥0∞)⁻¹ • sceneCloudCounting n := rfl

/-- **The two normalizations coincide**: the `1/(n+1)`-normalized integral against
the counting measure equals the integral against the probability empirical sample
law.  Hence the per-tile counting convergence and the tile Palm sample mean are the
same sequence. -/
theorem integral_counting_eq_empirical (n : ℕ) (f : Fin (n + 1) → ℝ) :
    ((n + 1 : ℕ) : ℝ)⁻¹ * ∫ s, f s ∂(sceneCloudCounting n) =
      ∫ s, f s ∂(sceneCloudSample n) := by
  have hsmul := integral_smul_measure (f := f) (c := ((n + 1 : ℕ) : ℝ≥0∞)⁻¹)
    (μ := sceneCloudCounting n)
  have hsample : sceneCloudSample n = ((n + 1 : ℕ) : ℝ≥0∞)⁻¹ • sceneCloudCounting n := rfl
  have hcoe : (((n + 1 : ℕ) : ℝ≥0∞)⁻¹).toReal = ((n + 1 : ℕ) : ℝ)⁻¹ := by
    rw [ENNReal.toReal_inv, ENNReal.toReal_natCast]
  calc ((n + 1 : ℕ) : ℝ)⁻¹ * ∫ s, f s ∂(sceneCloudCounting n)
      = (((n + 1 : ℕ) : ℝ≥0∞)⁻¹).toReal * ∫ s, f s ∂(sceneCloudCounting n) := by
        rw [hcoe]
    _ = (((n + 1 : ℕ) : ℝ≥0∞)⁻¹).toReal • ∫ s, f s ∂(sceneCloudCounting n) := by
        rw [smul_eq_mul]
    _ = ∫ s, f s ∂(((n + 1 : ℕ) : ℝ≥0∞)⁻¹ • sceneCloudCounting n) := hsmul.symm
    _ = ∫ s, f s ∂(sceneCloudSample n) := by
        rw [hsample]

/-! ## Field (b) from the empirical counting convergence -/

/-- **The explicit finite cloud average readout** of the masked frozen cost: the
paper's empirical tile value for the concrete lane. -/
noncomputable def sceneCloudAverage (pcloud qcloud : ∀ n, Fin (n + 1) → M)
    (n : ℕ) (c : T.Index) : ℝ :=
  ((n + 1 : ℕ) : ℝ)⁻¹ *
    ∑ s : Fin (n + 1),
      T.tileMaskedFrozenCostIntegrand (sceneCloudX pcloud) (sceneCloudY qcloud) n c s

/-- The masked frozen cost sample mean of the concrete empirical lane IS the finite
cloud average (field (a)). -/
theorem tileMaskedFrozenCostMean_sceneCloud_eq_average
    (pcloud qcloud : ∀ n, Fin (n + 1) → M) (n : ℕ) (c : T.Index) :
    T.tileMaskedFrozenCostMean sceneCloudSample (sceneCloudX pcloud) (sceneCloudY qcloud) n c =
      T.sceneCloudAverage pcloud qcloud n c :=
  T.tileMaskedFrozenCostMean_sceneCloud pcloud qcloud n c

/-- **Field (b) from the empirical counting convergence** (route (i)). -/
theorem sceneCloudReadout_tendsto_popValue
    (pcloud qcloud : ∀ n, Fin (n + 1) → M) (scale : ℕ → ℝ) (c : T.Index)
    (popReadout : ℕ → ℝ) (G : ℕ → (ℚ → M) → ℝ) {C : ℝ}
    (hbounded : ∀ n, |(1 - 2 * ε) * scale n| ≤ C)
    (hlln : Tendsto (fun n ↦ T.sceneCloudAverage pcloud qcloud n c - popReadout n)
      atTop (𝓝 0))
    (hpop : Tendsto (fun n ↦
      (1 - 2 * ε) * (scale n * popReadout n) -
        T.tilePopValue (P := P) (a := a) (κ := κ) (lambda := lambda) (q := q) G c)
      atTop (𝓝 0)) :
    Tendsto (fun n ↦
      (1 - 2 * ε) * (scale n * T.sceneCloudAverage pcloud qcloud n c) -
        T.tilePopValue (P := P) (a := a) (κ := κ) (lambda := lambda) (q := q) G c)
      atTop (𝓝 0) :=
  tileReadout_tendsto_of_population_identification (ε := ε)
    (fun n ↦ T.sceneCloudAverage pcloud qcloud n c) popReadout scale hbounded hlln hpop

/-- **The full tile Palm sample law for the concrete lane, with BOTH fields
discharged**: field (a) by the cloud-average computation, field (b) by the empirical
counting convergence. -/
noncomputable def tilePalmSampleLaw_sceneCloud_of_countingConvergence
    (f : (K × K) →ᵇ ℝ) (t : ℝ)
    (pcloud qcloud : ∀ n, Fin (n + 1) → M) (scale : ℕ → ℝ) (c : T.Index)
    (popReadout : ℕ → ℝ) (G : ℕ → (ℚ → M) → ℝ) {C : ℝ}
    (hbounded : ∀ n, |(1 - 2 * ε) * scale n| ≤ C)
    (hlln : Tendsto (fun n ↦ T.sceneCloudAverage pcloud qcloud n c - popReadout n)
      atTop (𝓝 0))
    (hpop : Tendsto (fun n ↦
      (1 - 2 * ε) * (scale n * popReadout n) -
        T.tilePopValue (P := P) (a := a) (κ := κ) (lambda := lambda) (q := q) G c)
      atTop (𝓝 0)) :
    T.TilePalmSampleLaw (ε := ε) f t sceneCloudSample
      (sceneCloudX pcloud) (sceneCloudY qcloud) scale c
      (fun _ ↦ T.tilePopValue (P := P) (a := a) (κ := κ) (lambda := lambda) (q := q) G c) :=
  T.tilePalmSampleLaw_sceneCloud f t pcloud qcloud scale c
    (fun _ ↦ T.tilePopValue (P := P) (a := a) (κ := κ) (lambda := lambda) (q := q) G c)
    (T.sceneCloudReadout_tendsto_popValue pcloud qcloud scale c popReadout G hbounded
      hlln hpop)

/-- **The per-tile counting convergence gives field (b)**: the error-budget form in
which the named per-tile counting convergence `RootedTileMeanConvergence` feeds
field (b) for the concrete lane. -/
theorem sceneCloudReadout_tendsto_popValue_of_tile_errors
    (pcloud qcloud : ∀ n, Fin (n + 1) → M) (scale : ℕ → ℝ) (c : T.Index)
    (popReadout : ℕ → ℝ) (G : ℕ → (ℚ → M) → ℝ) {C : ℝ}
    (err budget : ℕ → T.Index → ℝ)
    (hbounded : ∀ n, |(1 - 2 * ε) * scale n| ≤ C)
    (herrLe : ∀ n (c' : T.Index), 0 ≤ err n c' ∧ err n c' ≤ budget n c')
    (hreadout : ∀ n, |T.sceneCloudAverage pcloud qcloud n c - popReadout n| ≤ err n c)
    (hbudget : Tendsto (fun n ↦ ∑ c', budget n c') atTop (𝓝 0))
    (hpop : Tendsto (fun n ↦
      (1 - 2 * ε) * (scale n * popReadout n) -
        T.tilePopValue (P := P) (a := a) (κ := κ) (lambda := lambda) (q := q) G c)
      atTop (𝓝 0)) :
    Tendsto (fun n ↦
      (1 - 2 * ε) * (scale n * T.sceneCloudAverage pcloud qcloud n c) -
        T.tilePopValue (P := P) (a := a) (κ := κ) (lambda := lambda) (q := q) G c)
      atTop (𝓝 0) := by
  have herr := tileError_tendsto_zero_of_budget (T := T) err budget herrLe hbudget c
  have hlln : Tendsto (fun n ↦ T.sceneCloudAverage pcloud qcloud n c - popReadout n)
      atTop (𝓝 0) := by
    rw [tendsto_zero_iff_abs_tendsto_zero]
    exact squeeze_zero (fun n ↦ abs_nonneg _) hreadout herr
  exact T.sceneCloudReadout_tendsto_popValue pcloud qcloud scale c popReadout G
    hbounded hlln hpop

end PopulationLocalPressureCore.TaylorTiles

end OTSelector.Reconstruction
