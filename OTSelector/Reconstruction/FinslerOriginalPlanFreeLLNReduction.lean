import OTSelector.Reconstruction.FinslerOriginalPalmLLNFromRootedConvergence
import OTSelector.Reconstruction.FinslerOriginalTilePopValueIdentification

/-!
# Plan-free tile LLN from masked-entry exchangeability and the fixed-pair identification

This module reduces the sharpest remaining probabilistic input isolated in
FinslerOriginalPalmLLNFromRootedConvergence, the plan-free per-tile LLN
PlanFreeTileLLN (free f t c), towards the repo's known reduction
planFreeTileLLN_of_exchangeability_and_fixedPair (FinslerOriginalFixedPairIdentification).

## 1. Exact type of PlanFreeTileLLN and its instance data

The named statement (FinslerOriginalPlanFreeTileLLN) is

  def PlanFreeTileLLN (diff : ℕ → ℝ) : Prop := Tendsto diff atTop (𝓝 0).

Its instance data at the scene-cloud / uniform-plan tile scale are, for each probe
f : (A union B) x (A union B) ->b R, tilt t : R and retained tile c : T.Index:

* the probe sequence hprobe f t n s c' = normalizedProbe base t n s c';
* the plan-free uniform tile average
  upart n = (1/(n+1)) * ((1/(n+1)) * T.uniformTilePart f t sceneCloudSample
    (sceneCloudX pcloud) (sceneCloudY qcloud) tileScale hprobe n c);
* the fixed-pair masked expectation
  fpair n = T.tileFixedPair f t sceneCloudSample (sceneCloudX pcloud)
    (sceneCloudY qcloud) tileScale hprobe n c;
* the population tile value pop = T.tilePopValue (P := P) (a := a) (κ := κ)
  (lambda := lambda) (q := q) G c, and the plan-free sequence
  free f t c n = upart n - pop.

## 2. What is proved here

* planFreeTileLLN_sceneCloud_of_fixedPairIdentification: PlanFreeTileLLN of the
  plan-free deviation (free f t c) follows from masked-entry exchangeability
  (which identifies the normalized plan-free tile mean with the fixed-pair
  expectation, uniformTilePart_eq_fixedPair) and the single fixed-pair linear
  identification; this is the exact instance of
  planFreeTileLLN_of_fixedPairIdentification.

* lowerLaneRootedTileMeanLaw_of_fixedPairIdentification: the Palm tile mean law
  LowerLaneRootedTileMeanLaw (FinslerOriginalTileCampbellMeanFromPalm) follows
  from masked-entry exchangeability, the fixed-pair linear identification, the
  entrywise / pair-sum / plan-residual integrabilities and plan-residual vanishing.
  All other steps (decomposition identity, plan-free LLN, per-tile mean
  convergence, single-tile convergence, rooted tile mean convergence) are repo
  theorems.  Hence the Palm LLN of the lower lane is reduced to the SINGLE
  fixed-pair identification
  PlanFreeTileMeanIdentification (tileFixedPair ...) (fun _ => tilePopValue ... G c).

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

/-! ## 2. The plan-free LLN at the scene-cloud instance -/

/-- **PlanFreeTileLLN from masked-entry exchangeability and the fixed-pair
identification.**  The normalized plan-free tile mean equals the fixed-pair masked
expectation (uniformTilePart_eq_fixedPair, using the entrywise integrability and
the masked-entry exchangeability), and the fixed-pair deviation vanishes by the
single fixed-pair linear identification; hence the plan-free per-tile LLN holds. -/
theorem planFreeTileLLN_sceneCloud_of_fixedPairIdentification
    (T : D.TaylorTiles ε) {A B : Set M}
    (pcloud qcloud : ∀ n, Fin (n + 1) → M)
    (base : ∀ n, Fin (n + 1) → T.Index → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (G : ℕ → (ℚ → M) → ℝ)
    (f : (↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) (t : ℝ) (c : T.Index)
    (hintEntry : ∀ (n : ℕ) (i j : Fin (n + 1)),
      Integrable (fun s ↦ T.tileCostMatrix f t (sceneCloudX pcloud) (sceneCloudY qcloud)
        tileScale (fun f t n s c' ↦ normalizedProbe (K := A ∪ B) base t n s c')
        n c s i j) (sceneCloudSample n))
    (hExch : ∀ (n : ℕ), MaskedEntryExchangeability (sceneCloudSample n)
      (T.tileCostMatrix f t (sceneCloudX pcloud) (sceneCloudY qcloud) tileScale
        (fun f t n s c' ↦ normalizedProbe (K := A ∪ B) base t n s c') n c))
    (hid : PlanFreeTileMeanIdentification
      (fun n ↦ T.tileFixedPair f t sceneCloudSample (sceneCloudX pcloud)
        (sceneCloudY qcloud) tileScale
        (fun f t n s c' ↦ normalizedProbe (K := A ∪ B) base t n s c') n c)
      (fun _ ↦ T.tilePopValue (P := P) (a := a) (κ := κ) (lambda := lambda) (q := q) G c)) :
    PlanFreeTileLLN (fun n ↦
      (1 / ((n + 1 : ℕ) : ℝ)) * ((1 / ((n + 1 : ℕ) : ℝ)) *
        T.uniformTilePart f t sceneCloudSample (sceneCloudX pcloud) (sceneCloudY qcloud)
          tileScale (fun f t n s c' ↦ normalizedProbe (K := A ∪ B) base t n s c') n c) -
      T.tilePopValue (P := P) (a := a) (κ := κ) (lambda := lambda) (q := q) G c) := by
  have hmean : ∀ n, (1 / ((n + 1 : ℕ) : ℝ)) * ((1 / ((n + 1 : ℕ) : ℝ)) *
      T.uniformTilePart f t sceneCloudSample (sceneCloudX pcloud) (sceneCloudY qcloud)
        tileScale (fun f t n s c' ↦ normalizedProbe (K := A ∪ B) base t n s c') n c) =
      T.tileFixedPair f t sceneCloudSample (sceneCloudX pcloud) (sceneCloudY qcloud)
        tileScale (fun f t n s c' ↦ normalizedProbe (K := A ∪ B) base t n s c') n c :=
    fun n ↦ uniformTilePart_eq_fixedPair (T := T) sceneCloudSample f t
      (sceneCloudX pcloud) (sceneCloudY qcloud) tileScale
      (fun f t n s c' ↦ normalizedProbe (K := A ∪ B) base t n s c') n c
      (hintEntry n) (hExch n)
  exact planFreeTileLLN_of_fixedPairIdentification _ _ _ hmean hid

/-! ## 3. The Palm tile mean law from the single fixed-pair identification -/

/-- **LowerLaneRootedTileMeanLaw from the single fixed-pair identification.**
The per-tile iid LLN TileMeanConvergence is derived in
FinslerOriginalTilePopValueIdentification from the population identification of the
scaled masked pair integral (uniform average convergence from masked-entry
exchangeability and the fixed-pair identification) and plan-residual vanishing;
the remaining chain TileMeanConvergence -> RootedTileSingleConvergenceInProbability
-> RootedTileSingleConvergence -> RootedTileMeanConvergence is proved in the repo.
Hence the Palm tile mean law of the lower lane has no probabilistic input other
than the fixed-pair linear identification. -/
theorem lowerLaneRootedTileMeanLaw_of_fixedPairIdentification
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
    (hid : ∀ (f : (↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) (t : ℝ) (c : T.Index),
      PlanFreeTileMeanIdentification
        (fun n ↦ T.tileFixedPair f t sceneCloudSample (sceneCloudX pcloud)
          (sceneCloudY qcloud) tileScale
          (fun f t n s c' ↦ normalizedProbe (K := A ∪ B) base t n s c') n c)
        (fun _ ↦ T.tilePopValue (P := P) (a := a) (κ := κ) (lambda := lambda) (q := q) G c))
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
        normalizedProbe (K := A ∪ B) base t n s c')) :
    LowerLaneRootedTileMeanLaw (P := P) (a := a) (κ := κ) (lambda := lambda) (q := q)
      T (A := A) (B := B) pcloud qcloud base G :=
  lowerLaneRootedTileMeanLaw_of_tileMeanConvergence (T := T) (A := A) (B := B)
    pcloud qcloud base G
    (tileMeanConvergence_of_fixedPair_and_residual (T := T) sceneCloudSample G
      (sceneCloudX pcloud) (sceneCloudY qcloud) tileScale
      (fun f t n s c' ↦ normalizedProbe (K := A ∪ B) base t n s c')
      hintEntry hExch hid (uniformTilePlan (fun n ↦ Fin (n + 1)))
      hintCost hintRes hresv)
