import OTSelector.Reconstruction.FinslerOriginalPalmSampleLawProof

/-!
# hLLN and hBias are V7's existing sampling-law binders

## Determination

FinslerOriginalPalmSampleLawProof (batch108) reduced the tile Palm sample law to the
pair hLLN + hBias.  These are not new assumptions: they are **literally the existing
binder list of the V7 paper assembly** (FinslerOriginalPaperTheoremFinalV7.lean).

V7's endgame data carries (header table, lines 64-66; binders at 307-313, 654-660,
943-949):

* popReadout : ((A u B) x (A u B) ->_b R) -> R -> T.Index -> N -> R   (F16 population
  Palm readout sequence, data);
* hlln : forall f t c, Tendsto (fun n => T.sceneCloudAverage pcloud qcloud n c -
  popReadout f t c n) atTop (nhds 0)   (F16 empirical Palm LLN, paper hypothesis);
* hpop : forall f t c, Tendsto (fun n => (1 - 2 eps) * (tileScale n *
  popReadout f t c n) - T.tilePopValue G c) atTop (nhds 0)   (F16 population readout
  normalization, paper-proven side statement).

They are consumed at V7 lines 413, 751, 1040 by passing popReadout hlln hpop into the
derived lower-lane fields (the V7 assembly imports FinslerOriginalPalmReadoutFromLaneProducer
and FinslerOriginalLowerLaneMeanLawClosed).  Hence:

* hLLN is exactly V7's hlln (per f t c); it is a paper hypothesis, NOT derivable from
  the iid sampling laws hXlaw/hYlaw/iIndepFun: those describe the slot laws only, while
  hlln is the empirical-cloud average convergence (the cloud arrays are deterministic,
  so no repo LLN theorem applies);
* hBias is exactly V7's hpop (per f t c); popReadout is data, not defined as a limit,
  so hBias is not definitional - it is the paper's normalization side statement.

## What is delivered

The bridge from the V7 binder shapes to the batch107/batch108 interface, the tile Palm
sample law family, and LowerLaneRootedTileMeanLaw from the shortest residual list
(hlln, hpop plus the analytic lane fields).

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
/-! ## 1. The bridge: V7-style sampling binders give the typed residuals -/

/-- **hLLN from V7's hlln binder.** -/
theorem palmReadoutIdentification_of_paperSamplingLaws
    (T : D.TaylorTiles ε) {A B : Set M}
    (pcloud qcloud : ∀ n, Fin (n + 1) → M)
    (popReadout : (f : (↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) → ℝ → T.Index → ℕ → ℝ)
    (hlln : ∀ (f : (↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) (t : ℝ) (c : T.Index),
      Tendsto (fun n ↦ T.sceneCloudAverage pcloud qcloud n c - popReadout f t c n)
        atTop (𝓝 0)) :
    ∀ (f : (↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) (t : ℝ) (c : T.Index),
      PalmReadoutIdentification (T := T) pcloud qcloud c (popReadout f t c) :=
  fun f t c ↦ hlln f t c

/-- **hBias from V7's hpop binder.** -/
theorem palmPopulationReadoutIdentification_of_paperSamplingLaws
    (T : D.TaylorTiles ε) {A B : Set M}
    (popReadout : (f : (↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) → ℝ → T.Index → ℕ → ℝ)
    (G : ℕ → (ℚ → M) → ℝ)
    (hpop : ∀ (f : (↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) (t : ℝ) (c : T.Index),
      Tendsto (fun n ↦ (1 - 2 * ε) * (tileScale n * popReadout f t c n) -
        T.tilePopValue (P := P) (a := a) (κ := κ) (lambda := lambda) (q := q) G c)
        atTop (𝓝 0)) :
    ∀ (f : (↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) (t : ℝ) (c : T.Index),
      PalmPopulationReadoutIdentification (T := T) (G := G) (c := c)
        (popReadout := popReadout f t c) (q := q) :=
  fun f t c ↦ hpop f t c

/-! ## 2. The tile Palm sample law family from the V7 binders -/

/-- **The tile Palm sample law family from V7's hlln + hpop.**
Field (a) is the exact empirical identification, field (b) comes from
sceneCloudReadout_tendsto_of_LLN_and_bias. -/
noncomputable def tilePalmSampleLaw_sceneCloud_of_paperSamplingLaws
    (T : D.TaylorTiles ε) {A B : Set M}
    (pcloud qcloud : ∀ n, Fin (n + 1) → M)
    (popReadout : (f : (↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) → ℝ → T.Index → ℕ → ℝ)
    (G : ℕ → (ℚ → M) → ℝ)
    (hlln : ∀ (f : (↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) (t : ℝ) (c : T.Index),
      Tendsto (fun n ↦ T.sceneCloudAverage pcloud qcloud n c - popReadout f t c n)
        atTop (𝓝 0))
    (hpop : ∀ (f : (↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) (t : ℝ) (c : T.Index),
      Tendsto (fun n ↦ (1 - 2 * ε) * (tileScale n * popReadout f t c n) -
        T.tilePopValue (P := P) (a := a) (κ := κ) (lambda := lambda) (q := q) G c)
        atTop (𝓝 0)) :
    ∀ (f : (↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) (t : ℝ) (c : T.Index),
      T.TilePalmSampleLaw (ε := ε) f t sceneCloudSample (sceneCloudX pcloud)
        (sceneCloudY qcloud) tileScale c
        (fun _ ↦ T.tilePopValue (P := P) (a := a) (κ := κ) (lambda := lambda) (q := q) G c) :=
  fun f t c ↦
    tilePalmSampleLaw_sceneCloud_of_LLN (T := T) (A := A) (B := B) pcloud qcloud f t c
      (popReadout f t c) G (hlln f t c) (hpop f t c)

/-! ## 3. LowerLaneRootedTileMeanLaw from the V7 sampling binders -/

/-- **LowerLaneRootedTileMeanLaw from V7's hlln + hpop.**  The shortest residual list:
hlln (paper hypothesis), hpop (paper-proven side statement) and the analytic lane
fields. -/
theorem lowerLaneRootedTileMeanLaw_of_paperSamplingLaws
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
    (popReadout : (f : (↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) → ℝ → T.Index → ℕ → ℝ)
    (hlln : ∀ (f : (↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) (t : ℝ) (c : T.Index),
      Tendsto (fun n ↦ T.sceneCloudAverage pcloud qcloud n c - popReadout f t c n)
        atTop (𝓝 0))
    (hpop : ∀ (f : (↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) (t : ℝ) (c : T.Index),
      Tendsto (fun n ↦ (1 - 2 * ε) * (tileScale n * popReadout f t c n) -
        T.tilePopValue (P := P) (a := a) (κ := κ) (lambda := lambda) (q := q) G c)
        atTop (𝓝 0)) :
    LowerLaneRootedTileMeanLaw (P := P) (a := a) (κ := κ) (lambda := lambda) (q := q)
      T (A := A) (B := B) pcloud qcloud base G :=
  lowerLaneRootedTileMeanLaw_of_palmReadoutClosed (T := T) (A := A) (B := B)
    pcloud qcloud base G hintEntry hExch hintCost hintRes hresv hBp hbase
    hintC hintP hintLin hintClip hε hz₀ hp popReadout hlln hpop
