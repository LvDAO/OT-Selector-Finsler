import OTSelector.Reconstruction.FinslerOriginalLinearPalmIdentification

/-!
# The tile-lane Palm structure

This module implements the two structural hypotheses identified in
`FinslerOriginalLinearPalmIdentification.lean` as an explicit, honest interface
(`TilePalmSampleLaw`), and derives the cost and linear Palm identifications from it.

## The interface

`TilePalmSampleLaw f t sample X Y scale c popVal` carries three fields:

* `palmCostMean : ℕ → ℝ` — the assumed Palm readout of the masked frozen cost, i.e.
  the population cell mean `∫ z in cell, θ ^ (-2/q) * G c z ∂lambda` in the units of
  the scaled masked cost (paper data; this is the *definition* of the readout);
* `maskedMean_eq : ∀ n, ∫ s, 1_{edgeEvent} · frozenPhysicalCost ∂sample n = palmCostMean n`
  — **field (a)**: the sample law of the tile lane is the scene Palm law, so the
  sample mean of the masked frozen cost is the population cell mean.  Justified by:
  the sample measure being the Palm product law of the scene; this is *new structure*,
  not derivable from the current lane (the lane carries `sample` abstractly);
* `palm_readout : Tendsto (fun n => (1-2ε) * (scale n * palmCostMean n) - popVal n) 0`
  — **field (b)**: the sample-level Campbell bridge together with the tile
  normalization `scale n`; i.e. the paper identity
  `(1-2ε) · scale · (population cell mean) → tilePopValue`.  Justified by the repo's
  Campbell bridge `campbellAveragedFrozenCost_eq_tileSum_add_tail` after the
  normalization and the `θ^(-2/q)` weighting.

Every field is explicitly marked as paper data / new structure; nothing is silently
assumed.

## Proved here

* `tileMaskedFrozenCostIntegrand`, `tileMaskedFrozenCostMean`: the masked frozen cost
  integrand and its sample mean;
* `tileLinearCostIntegrand_eq_const_mul_masked`: the cost part of the linear integrand
  is `(1-2ε) · scale` times the masked frozen cost (pointwise);
* `tileLinearCostPart_eq_const_mul_mean`: hence the cost integral is
  `(1-2ε) * (scale n * maskedMean n)` — the exact factorization;
* `tileCostPalmIdentification_of_palmSampleLaw`: field (b) plus the factorization give
  the cost Palm identification;
* `tileLinearPalmIdentification_of_palmSampleLaw`: the full linear Palm identification
  (via the probe vanishing of task 236).

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
  {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]

namespace PopulationLocalPressureCore.TaylorTiles

/-- The **masked frozen cost integrand** at the distinguished pair. -/
noncomputable def tileMaskedFrozenCostIntegrand
    (X Y : ∀ n, Fin (n + 1) → Ω n → M)
    (n : ℕ) (c : T.Index) (s : Ω n) : ℝ :=
  (T.edgeEvent (fun i ↦ X n i s) (fun i ↦ Y n i s) c).indicator
    (fun p : Fin (n + 1) × Fin (n + 1) ↦
      (T.core c).frozenPhysicalCost (T.reference c) (X n p.1 s) (Y n p.2 s))
    (⟨0, Nat.succ_pos n⟩, ⟨0, Nat.succ_pos n⟩)

/-- The **masked frozen cost sample mean**. -/
noncomputable def tileMaskedFrozenCostMean
    (sample : ∀ n, Measure (Ω n))
    (X Y : ∀ n, Fin (n + 1) → Ω n → M)
    (n : ℕ) (c : T.Index) : ℝ :=
  ∫ s, T.tileMaskedFrozenCostIntegrand X Y n c s ∂sample n

/-- **The cost part of the linear integrand is `(1-2ε)·scale` times the masked frozen
cost** (pointwise). -/
theorem tileLinearCostIntegrand_eq_const_mul_masked
    (f : (K × K) →ᵇ ℝ) (t : ℝ)
    (X Y : ∀ n, Fin (n + 1) → Ω n → M)
    (scale : ℕ → ℝ)
    (n : ℕ) (c : T.Index) (s : Ω n) :
    T.tileLinearCostIntegrand (ε := ε) f t X Y scale n c s =
      (1 - 2 * ε) * scale n * T.tileMaskedFrozenCostIntegrand X Y n c s := by
  simp only [tileLinearCostIntegrand, tileMaskedFrozenCostIntegrand]
  by_cases h : (⟨0, Nat.succ_pos n⟩, ⟨0, Nat.succ_pos n⟩) ∈
      T.edgeEvent (fun i ↦ X n i s) (fun i ↦ Y n i s) c
  · rw [Set.indicator_of_mem h, Set.indicator_of_mem h]
    ring
  · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem h, mul_zero]

/-- **The cost integral factorizes**: it is `(1-2ε)·scale` times the masked frozen
cost sample mean. -/
theorem tileLinearCostPart_eq_const_mul_mean
    (sample : ∀ n, Measure (Ω n))
    (f : (K × K) →ᵇ ℝ) (t : ℝ)
    (X Y : ∀ n, Fin (n + 1) → Ω n → M)
    (scale : ℕ → ℝ)
    (n : ℕ) (c : T.Index) :
    ∫ s, T.tileLinearCostIntegrand (ε := ε) f t X Y scale n c s ∂sample n =
      (1 - 2 * ε) * (scale n * T.tileMaskedFrozenCostMean sample X Y n c) := by
  have hfun : (fun s ↦ T.tileLinearCostIntegrand (ε := ε) f t X Y scale n c s) =
      (fun s ↦ (1 - 2 * ε) * scale n *
        T.tileMaskedFrozenCostIntegrand X Y n c s) :=
    funext fun s ↦ T.tileLinearCostIntegrand_eq_const_mul_masked f t X Y scale n c s
  rw [hfun]
  rw [integral_const_mul]
  simp only [tileMaskedFrozenCostMean]
  ring

/-- **The tile-lane Palm sample law (the honest interface).**  All fields are paper
data / new structure, as documented in the module header. -/
structure TilePalmSampleLaw
    (f : (K × K) →ᵇ ℝ) (t : ℝ)
    (sample : ∀ n, Measure (Ω n))
    (X Y : ∀ n, Fin (n + 1) → Ω n → M)
    (scale : ℕ → ℝ) (c : T.Index) (popVal : ℕ → ℝ) : Type where
  /-- The population Palm readout of the masked frozen cost (paper data). -/
  palmCostMean : ℕ → ℝ
  /-- **Field (a)**: the sample law is the scene Palm law, so the sample mean of the
  masked frozen cost is the population readout.  New structure, not derivable from
  the lane (which carries `sample` abstractly). -/
  maskedMean_eq : ∀ n, T.tileMaskedFrozenCostMean sample X Y n c = palmCostMean n
  /-- **Field (b)**: the sample-level Campbell bridge plus tile normalization
  (paper identity, cf. `campbellAveragedFrozenCost_eq_tileSum_add_tail`). -/
  palm_readout : Tendsto
    (fun n ↦ (1 - 2 * ε) * (scale n * palmCostMean n) - popVal n) atTop (𝓝 0)

/-- **The cost Palm identification from the tile-lane Palm structure.** -/
theorem tileCostPalmIdentification_of_palmSampleLaw
    (f : (K × K) →ᵇ ℝ) (t : ℝ)
    (sample : ∀ n, Measure (Ω n))
    (X Y : ∀ n, Fin (n + 1) → Ω n → M)
    (scale : ℕ → ℝ) (c : T.Index) (popVal : ℕ → ℝ)
    (h : T.TilePalmSampleLaw f t sample X Y scale c popVal) :
    Tendsto (fun n ↦
      (∫ s, T.tileLinearCostIntegrand (ε := ε) f t X Y scale n c s ∂sample n) -
        popVal n) atTop (𝓝 0) := by
  have heq : (fun n ↦
      (∫ s, T.tileLinearCostIntegrand (ε := ε) f t X Y scale n c s ∂sample n) -
        popVal n) =
      (fun n ↦ (1 - 2 * ε) * (scale n * h.palmCostMean n) - popVal n) := by
    funext n
    rw [T.tileLinearCostPart_eq_const_mul_mean, h.maskedMean_eq n]
  rw [heq]
  exact h.palm_readout

/-- **The full linear Palm identification from the tile-lane Palm structure** (using
the probe vanishing proved in task 236). -/
theorem tileLinearPalmIdentification_of_palmSampleLaw
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
    (h : T.TilePalmSampleLaw f t sample X Y tileScale c
      (fun _ ↦ T.tilePopValue (P := P) (a := a) (κ := κ) (lambda := lambda) (q := q) G c)) :
    Tendsto (fun n ↦
      T.tileFixedPairLinearPart f t sample X Y tileScale
        (fun f t n s c' ↦ normalizedProbe (K := K) base t n s c') n c -
        T.tilePopValue (P := P) (a := a) (κ := κ) (lambda := lambda) (q := q) G c)
      atTop (𝓝 0) :=
  T.tileLinearPalmIdentification_of_costPalm sample f t X Y c base hBp hbase hintC
    hintP G (T.tileCostPalmIdentification_of_palmSampleLaw f t sample X Y tileScale c
      (fun _ ↦ T.tilePopValue (P := P) (a := a) (κ := κ) (lambda := lambda) (q := q) G c)
      h)

end PopulationLocalPressureCore.TaylorTiles

end OTSelector.Reconstruction
