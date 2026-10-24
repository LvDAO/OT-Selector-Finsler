import OTSelector.Reconstruction.FinslerOriginalLowerLaneMeanLawClosed

/-!
# The tile Palm sample law at the concrete scene cloud: field-by-field reduction

## Attack on the F16 empirical Palm LLN residual

The tile Palm sample law family hlaw (see FinslerOriginalLowerLaneMeanLawClosed) has
two fields.  This module resolves them field by field.

### Field (a) - CLOSED

The scene-cloud sample is the uniform empirical measure on the n+1 cloud slots
(sceneCloudSample n = empiricalMeasure id on Fin (n+1)).  Hence the masked frozen cost
sample mean is EXACTLY the finite empirical average, with no probabilistic input:
tileMaskedFrozenCostMean_sceneCloud_eq_average identifies it with
T.sceneCloudAverage pcloud qcloud n c.  Field (a) is therefore discharged exactly by
taking palmCostMean := fun n => T.sceneCloudAverage pcloud qcloud n c.

### Field (b) - reduced to two typed residuals

Field (b) asks (1 - 2 eps) * (tileScale n * cloud average) -> tilePopValue.  It is
reduced to the sharpest typed pair:

* hLLN : PalmReadoutIdentification pcloud qcloud c popReadout, i.e.
  Tendsto (fun n => T.sceneCloudAverage pcloud qcloud n c - popReadout n) 0
  (the empirical Palm LLN: cloud average -> population readout);
* hBias : PalmPopulationReadoutIdentification G c popReadout, i.e.
  Tendsto (fun n => (1 - 2 eps) * (tileScale n * popReadout n) - tilePopValue G c) 0
  (the population normalization / bias identity).

The multiplier bound |(1 - 2 eps) * tileScale n| <= |1 - 2 eps| is proved from the
concrete scale, so the only analytic content of field (b) is the pair (hLLN, hBias).

### Why the repo does not close hLLN

The repo probability modules contain empirical LLN machinery (e.g.
OTSelector.Probability.EmpiricalWeak.tendsto_empiricalProbabilityMeasure_row,
Mathlib's StrongLaw) but they are theorems about an infinite product probability space.
Here the cloud arrays pcloud n s, qcloud n s are deterministic arrays
(sceneCloudX pcloud n i s = pcloud n s), so the empirical average convergence is not a
measurable statement on a probability space carried by the lane: it is precisely the
paper's Palm LLN input (the sampling law of the cloud, cf. the endgame hypotheses
hXlaw/hYlaw/iIndepFun).  Hence hLLN/hBias remain as the exact residual list of the
interface, and the interface itself is constructed below from them.

No sorry, admit or added axiom occurs.
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
set_option linter.style.haveILetI false

namespace OTSelector.Reconstruction

open OTSelector.Geometry
open OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex
open OTSelector.Reconstruction.PopulationLocalPressureCore.TaylorTiles

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [IsManifold 𝓘(ℝ, E) ⊤ M]
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
  {ε : ℝ} {q : ℝ}
/-! ## 1. Field (a): exact empirical identification (no residual) -/

/-- **Field (a) of the interface, closed exactly.**  At the concrete scene cloud the
masked frozen cost sample mean IS the explicit finite cloud average; no probabilistic
input is involved. -/
theorem tileMaskedFrozenCostMean_sceneCloud_eq_sceneCloudAverage
    (T : D.TaylorTiles ε)
    (pcloud qcloud : ∀ n, Fin (n + 1) → M) (n : ℕ) (c : T.Index) :
    T.tileMaskedFrozenCostMean sceneCloudSample (sceneCloudX pcloud)
      (sceneCloudY qcloud) n c = T.sceneCloudAverage pcloud qcloud n c :=
  T.tileMaskedFrozenCostMean_sceneCloud_eq_average pcloud qcloud n c

/-! ## 2. Field (b): from the empirical Palm LLN and the population bias identity -/

/-- **Field (b) from the two typed residuals.**  The empirical Palm LLN puts the cloud
average at popReadout; the population normalization puts (1 - 2 eps) * tileScale *
popReadout at tilePopValue; the multiplier bound is proved from the concrete scale.
Hence the normalized frozen readout converges to the population tile value. -/
theorem sceneCloudReadout_tendsto_of_LLN_and_bias
    (T : D.TaylorTiles ε) {A B : Set M}
    (pcloud qcloud : ∀ n, Fin (n + 1) → M) (c : T.Index)
    (popReadout : ℕ → ℝ) (G : ℕ → (ℚ → M) → ℝ)
    (hLLN : PalmReadoutIdentification (T := T) pcloud qcloud c popReadout)
    (hBias : PalmPopulationReadoutIdentification (T := T) (G := G) (c := c)
      (popReadout := popReadout) (q := q)) :
    Tendsto (fun n ↦
      (1 - 2 * ε) * (tileScale n * T.sceneCloudAverage pcloud qcloud n c) -
        T.tilePopValue (P := P) (a := a) (κ := κ) (lambda := lambda) (q := q) G c)
      atTop (𝓝 0) :=
  T.sceneCloudReadout_tendsto_popValue pcloud qcloud tileScale c popReadout G
    (fun n ↦ abs_one_sub_two_mul_tileScale_le n) hLLN hBias

/-! ## 3. The interface constructed from the residuals -/

/-- **The tile Palm sample law at the scene cloud from the two typed residuals.**
Field (a) is the exact empirical identification; field (b) is
sceneCloudReadout_tendsto_of_LLN_and_bias.  The only probabilistic inputs are the
empirical Palm LLN hLLN and the population bias identity hBias. -/
noncomputable def tilePalmSampleLaw_sceneCloud_of_LLN
    (T : D.TaylorTiles ε) {A B : Set M}
    (pcloud qcloud : ∀ n, Fin (n + 1) → M)
    (f : (↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) (t : ℝ) (c : T.Index)
    (popReadout : ℕ → ℝ) (G : ℕ → (ℚ → M) → ℝ)
    (hLLN : PalmReadoutIdentification (T := T) pcloud qcloud c popReadout)
    (hBias : PalmPopulationReadoutIdentification (T := T) (G := G) (c := c)
      (popReadout := popReadout) (q := q)) :
    T.TilePalmSampleLaw (ε := ε) f t sceneCloudSample (sceneCloudX pcloud)
      (sceneCloudY qcloud) tileScale c
      (fun _ ↦ T.tilePopValue (P := P) (a := a) (κ := κ) (lambda := lambda) (q := q) G c) where
  palmCostMean := fun n ↦ T.sceneCloudAverage pcloud qcloud n c
  maskedMean_eq := fun n ↦
    tileMaskedFrozenCostMean_sceneCloud_eq_sceneCloudAverage (T := T) pcloud qcloud n c
  palm_readout :=
    sceneCloudReadout_tendsto_of_LLN_and_bias (T := T) (A := A) (B := B) pcloud qcloud
      c popReadout G hLLN hBias
