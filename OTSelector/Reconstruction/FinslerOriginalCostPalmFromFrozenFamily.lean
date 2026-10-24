import OTSelector.Reconstruction.FinslerOriginalFixedPairLinearSplit
import OTSelector.Reconstruction.FinslerOriginalConcretePalmSampleLaw

/-!
# The cost Palm identification from the frozen cost family

This module closes the last probabilistic input of the lower lane: the cost Palm
identification left open by
planFreeTileMeanIdentification_sceneCloud_of_costPalm
(FinslerOriginalFixedPairLinearSplit),

  Tendsto (fun n => integral of tileLinearCostIntegrand at tileScale n c - tilePopValue G c)
    atTop (neighborhood 0).

## 1. The exact statement

CostPalmIdentificationSceneCloud is the named proposition TileCostPalmIdentification
(FinslerOriginalLinearPalmIdentification) at the scene-cloud lane: the integral of the
linear cost integrand at tileScale converges to the population tile value.

## 2. Reduction to the frozen cost family readout

The cost integral factorizes exactly (tileLinearCostPart_eq_const_mul_mean) as
(1 - 2 eps) * (scale n * masked frozen cost mean), where the masked frozen cost
integrand is the tile component of the frozen core cost family (hprobFrozenCostFamily
of FinslerOriginalHprobMeanWiring is its finite tile sum, cf.
fractionalAssignmentCost_originalFrozenCoreMatrix_eq_sum).  Hence the cost Palm
identification is *exactly* the frozen cost family readout:

* field (a) (hmean): the sample mean of the masked frozen cost is the population
  readout (the tile Palm sample law, repo TilePalmSampleLaw);
* field (b) (hreadout): the normalized frozen readout converges to the population
  tile value.

tileCostPalmIdentification_sceneCloud_of_frozenReadout derives the cost Palm
identification from these two fields (via the repo tile Palm sample law), and
tileCostPalmIdentification_sceneCloud_of_frozenAverageReadout states the readout in
the empirical frozen-family average form used by the lane producer
tilePalmSampleLaw_sceneCloud (FinslerOriginalConcretePalmSampleLaw).

## 3. Instantiation

lowerLaneRootedTileMeanLaw_of_frozenCostReadout instantiates
LowerLaneRootedTileMeanLaw with the final residual list: the frozen cost family
readout hmean/hreadout plus the analytic lane fields.  No remaining convergence beyond
hreadout.

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

/-! ## 1. The exact cost Palm identification -/

/-- **The cost Palm identification at the scene-cloud lane.**  The integral of the
linear cost integrand at tileScale converges to the population tile value.  This is
the last probabilistic input of the fixed-pair lane. -/
def CostPalmIdentificationSceneCloud
    (T : D.TaylorTiles ε) {A B : Set M}
    (pcloud qcloud : ∀ n, Fin (n + 1) → M)
    (G : ℕ → (ℚ → M) → ℝ)
    (f : (↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) (t : ℝ) (c : T.Index) : Prop :=
  TileCostPalmIdentification
    (fun n ↦ ∫ s, T.tileLinearCostIntegrand (ε := ε) f t (sceneCloudX pcloud)
      (sceneCloudY qcloud) tileScale n c s ∂sceneCloudSample n)
    (fun _ ↦ T.tilePopValue (P := P) (a := a) (κ := κ) (lambda := lambda) (q := q) G c)

/-! ## 2. Reduction to the frozen cost family readout -/

/-- **The cost Palm identification from the frozen cost family readout.**  The tile
Palm sample law carries the two frozen-family readout facts (sample mean of the masked
frozen cost equals the population readout; normalized readout converges to the
population tile value).  The exact factorization of the cost integral then gives the
cost Palm identification. -/
theorem tileCostPalmIdentification_sceneCloud_of_frozenReadout
    (T : D.TaylorTiles ε) {A B : Set M}
    (pcloud qcloud : ∀ n, Fin (n + 1) → M)
    (f : (↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) (t : ℝ) (c : T.Index)
    (G : ℕ → (ℚ → M) → ℝ) (palmCostMean : ℕ → ℝ)
    (hmean : ∀ (n : ℕ), T.tileMaskedFrozenCostMean sceneCloudSample
      (sceneCloudX pcloud) (sceneCloudY qcloud) n c = palmCostMean n)
    (hreadout : Tendsto (fun n ↦ (1 - 2 * ε) * (tileScale n * palmCostMean n) -
      T.tilePopValue (P := P) (a := a) (κ := κ) (lambda := lambda) (q := q) G c)
      atTop (𝓝 0)) :
    CostPalmIdentificationSceneCloud (D := D) (ε := ε) (P := P) (a := a) (κ := κ)
      (lambda := lambda) (q := q) T (A := A) (B := B) pcloud qcloud G f t c :=
  T.tileCostPalmIdentification_of_palmSampleLaw f t sceneCloudSample
    (sceneCloudX pcloud) (sceneCloudY qcloud) tileScale c
    (fun _ ↦ T.tilePopValue (P := P) (a := a) (κ := κ) (lambda := lambda) (q := q) G c)
    { palmCostMean := palmCostMean
      maskedMean_eq := hmean
      palm_readout := hreadout }

/-- **The frozen cost family readout in empirical-average form.**  At the concrete
empirical scene lane the masked frozen cost mean is the finite cloud average, so the
readout hypothesis can be stated verbatim in the frozen-family sample-sum form used by
the lane producer tilePalmSampleLaw_sceneCloud. -/
theorem tileCostPalmIdentification_sceneCloud_of_frozenAverageReadout
    (T : D.TaylorTiles ε) {A B : Set M}
    (pcloud qcloud : ∀ n, Fin (n + 1) → M)
    (f : (↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) (t : ℝ) (c : T.Index)
    (G : ℕ → (ℚ → M) → ℝ) (palmCostMean : ℕ → ℝ)
    (haverage : ∀ (n : ℕ), ((n + 1 : ℕ) : ℝ)⁻¹ * ∑ s : Fin (n + 1),
      T.tileMaskedFrozenCostIntegrand (sceneCloudX pcloud) (sceneCloudY qcloud) n c s =
        palmCostMean n)
    (hreadout : Tendsto (fun n ↦ (1 - 2 * ε) * (tileScale n * palmCostMean n) -
      T.tilePopValue (P := P) (a := a) (κ := κ) (lambda := lambda) (q := q) G c)
      atTop (𝓝 0)) :
    CostPalmIdentificationSceneCloud (D := D) (ε := ε) (P := P) (a := a) (κ := κ)
      (lambda := lambda) (q := q) T (A := A) (B := B) pcloud qcloud G f t c :=
  tileCostPalmIdentification_sceneCloud_of_frozenReadout (D := D) (ε := ε) (P := P)
    (a := a) (κ := κ) (lambda := lambda) (q := q) T (A := A) (B := B) pcloud qcloud
    f t c G palmCostMean
    (fun n ↦ (T.tileMaskedFrozenCostMean_sceneCloud pcloud qcloud n c).trans (haverage n))
    hreadout

/-! ## 3. The final residual list of the lower lane -/

/-- **LowerLaneRootedTileMeanLaw with the final residual list.**  The cost Palm
identification is reduced to the frozen cost family readout (hmean, hreadout); every
other input is an analytic lane field (exchangeability, integrabilities, plan residual
vanishing, probe base bound, retained-edge window facts, eps <= 1/2).  No remaining
convergence beyond hreadout. -/
theorem lowerLaneRootedTileMeanLaw_of_frozenCostReadout
    (T : D.TaylorTiles ε) {A B : Set M}
    (pcloud qcloud : ∀ n, Fin (n + 1) → M)
    (base : ∀ n, Fin (n + 1) → T.Index → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (G : ℕ → (ℚ → M) → ℝ)
    (hintEntry : ∀ (f : (↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) (t : ℝ) (n : ℕ) (c : T.Index)
      (i j : Fin (n + 1)),
      Integrable (fun s ↦ T.tileCostMatrix f t (sceneCloudX pcloud) (sceneCloudY qcloud)
        tileScale (fun f t n s c' ↦ normalizedProbe (K := A ∪ B) base t n s c')
        n c s i j) (sceneCloudSample n))
    (hExch : ∀ (f : (↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) (t : ℝ) (n : ℕ) (c : T.Index),
      MaskedEntryExchangeability (sceneCloudSample n)
        (T.tileCostMatrix f t (sceneCloudX pcloud) (sceneCloudY qcloud) tileScale
          (fun f t n s c' ↦ normalizedProbe (K := A ∪ B) base t n s c') n c))
    (hintCost : ∀ (f : (↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) (t : ℝ) (n : ℕ) (c : T.Index),
      Integrable (fun s ↦ ∑ i, ∑ j,
        T.tileCostMatrix f t (sceneCloudX pcloud) (sceneCloudY qcloud) tileScale
          (fun f t n s c' ↦ normalizedProbe (K := A ∪ B) base t n s c') n c s i j)
        (sceneCloudSample n))
    (hintRes : ∀ (f : (↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) (t : ℝ) (n : ℕ) (c : T.Index),
      Integrable (fun s ↦ ∑ i, ∑ j,
        (uniformTilePlan (fun n ↦ Fin (n + 1)) n s i j - 1 / ((n + 1 : ℕ) : ℝ)) *
          T.tileCostMatrix f t (sceneCloudX pcloud) (sceneCloudY qcloud) tileScale
            (fun f t n s c' ↦ normalizedProbe (K := A ∪ B) base t n s c') n c s i j)
        (sceneCloudSample n))
    (hresv : T.TilePlanResidualVanishing sceneCloudSample
      (uniformTilePlan (fun n ↦ Fin (n + 1))) (sceneCloudX pcloud) (sceneCloudY qcloud)
      tileScale
      (fun (f : (↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) t n s c' ↦
        normalizedProbe (K := A ∪ B) base t n s c'))
    {Bp : ℝ} (hBp : 0 ≤ Bp)
    (hbase : ∀ (n : ℕ) (s : Fin (n + 1)) (c' : T.Index) (i j : Fin (n + 1)),
      |base n s c' i j| ≤ Bp)
    (hintC : ∀ (f : (↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) (t : ℝ) (n : ℕ) (c : T.Index),
      Integrable (T.tileLinearCostIntegrand (ε := ε) f t (sceneCloudX pcloud)
        (sceneCloudY qcloud) tileScale n c) (sceneCloudSample n))
    (hintP : ∀ (f : (↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) (t : ℝ) (n : ℕ) (c : T.Index),
      Integrable (T.tileLinearProbeIntegrand f t (sceneCloudX pcloud)
        (sceneCloudY qcloud)
        (fun f t n s c' ↦ normalizedProbe (K := A ∪ B) base t n s c') n c)
        (sceneCloudSample n))
    (hintLin : ∀ (f : (↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) (t : ℝ) (n : ℕ) (c : T.Index),
      Integrable (T.tileLinearIntegrand (ε := ε) f t (sceneCloudX pcloud)
        (sceneCloudY qcloud) tileScale
        (fun f t n s c' ↦ normalizedProbe (K := A ∪ B) base t n s c') n c)
        (sceneCloudSample n))
    (hintClip : ∀ (f : (↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) (t : ℝ) (n : ℕ) (c : T.Index),
      Integrable (T.tileClippingIntegrand (ε := ε) f t (sceneCloudX pcloud)
        (sceneCloudY qcloud) tileScale
        (fun f t n s c' ↦ normalizedProbe (K := A ∪ B) base t n s c') n c)
        (sceneCloudSample n))
    (hε : ε ≤ 1 / 2)
    (hz₀ : ∀ c : T.Index, T.reference c ∈ (T.cover c.1).centers)
    (hp : ∀ (c : T.Index) (n : ℕ) (s : Fin (n + 1)),
      (u ((sceneCloudX pcloud) n ⟨0, Nat.succ_pos n⟩ s),
        u ((sceneCloudY qcloud) n ⟨0, Nat.succ_pos n⟩ s)) ∈ (T.core c).window.region)
    (palmCostMean : (f : (↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) → ℝ → T.Index → ℕ → ℝ)
    (hmean : ∀ (f : (↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) (t : ℝ) (c : T.Index) (n : ℕ),
      T.tileMaskedFrozenCostMean sceneCloudSample (sceneCloudX pcloud)
        (sceneCloudY qcloud) n c = palmCostMean f t c n)
    (hreadout : ∀ (f : (↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) (t : ℝ) (c : T.Index),
      Tendsto (fun n ↦ (1 - 2 * ε) * (tileScale n * palmCostMean f t c n) -
        T.tilePopValue (P := P) (a := a) (κ := κ) (lambda := lambda) (q := q) G c)
        atTop (𝓝 0)) :
    LowerLaneRootedTileMeanLaw (P := P) (a := a) (κ := κ) (lambda := lambda) (q := q)
      T (A := A) (B := B) pcloud qcloud base G :=
  lowerLaneRootedTileMeanLaw_of_costPalm (T := T) (A := A) (B := B)
    pcloud qcloud base G hintEntry hExch hintCost hintRes hresv hBp hbase
    hintC hintP hintLin hintClip hε hz₀ hp
    (fun f t c ↦
      tileCostPalmIdentification_sceneCloud_of_frozenReadout (D := D) (ε := ε) (P := P)
        (a := a) (κ := κ) (lambda := lambda) (q := q) T (A := A) (B := B) pcloud qcloud
        f t c G (palmCostMean f t c) (hmean f t c) (hreadout f t c))
