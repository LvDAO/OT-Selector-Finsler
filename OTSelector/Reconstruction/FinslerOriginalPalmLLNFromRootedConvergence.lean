import OTSelector.Reconstruction.FinslerOriginalTileCampbellMeanFromPalm
import OTSelector.Reconstruction.FinslerOriginalTileMeanConvergenceProof
import OTSelector.Reconstruction.FinslerOriginalTileCountingLaw
/-!
# The Palm tile mean law from the plan-free per-tile LLN

This module reduces the last probabilistic input of the lower endgame lane,
LowerLaneRootedTileMeanLaw (FinslerOriginalTileCampbellMeanFromPalm), to the
sharpest convergence statement currently isolated in the repository.

## 1. Is the rooted tile mean convergence already proved for the scene cloud?

No.  The repo chain is: RootedTileMeanConvergence is implied by
RootedTileSingleConvergence (rootedTileMeanConvergence_of_single,
FinslerOriginalTileCountingLaw), which is implied by the in-probability form
RootedTileSingleConvergenceInProbability (rootedTileSingleConvergence_of_inProbability,
FinslerOriginalRootedTileSingleInstantiation), which is implied by the per-tile
mean convergence TileMeanConvergence (rootedTileSingleConvergenceInProbability_of_tileMeanConvergence,
FinslerOriginalTileSingleConvergenceProof).  TileMeanConvergence is reduced in
FinslerOriginalTileMeanConvergenceProof to the plan-free per-tile LLN
(PlanFreeTileLLN, FinslerOriginalPlanFreeTileLLN) together with the exact
plan-free decomposition identity, with the plan residual either assumed vanishing
(tileMeanConvergence_of_planFree) or derived from plan-free average-cost control
(tileMeanConvergence_of_planFreeControl, FinslerOriginalUniformTileAverage).
None of these is proved for the concrete sceneCloudSample / uniformTilePlan /
tileScale instance; the plan-free LLN is the paper's remaining Palm LLN content
(F16), and the decomposition identity is the Palm/stationary readout of the
limiting matching.

## 2. What is proved here

The three reductions are composed with the repo producers, so that

* lowerLaneRootedTileMeanLaw_of_tileMeanConvergence: the Palm tile mean law
  follows from the single per-tile iid LLN TileMeanConvergence;
* lowerLaneRootedTileMeanLaw_of_planFree: it follows from the exact plan-free
  decomposition together with PlanFreeTileLLN for every probe/tilt/tile and the
  vanishing of the residual;
* lowerLaneRootedTileMeanLaw_of_planFreeControl: the residual is DERIVED from
  plan-free average-cost control, so the only probabilistic inputs are the
  plan-free per-tile LLN family and the cost control.

Hence the lower endgame lane has no probabilistic input other than the plan-free
per-tile LLN family, the exact plan-free decomposition identity and the plan-free
average-cost control.

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

/-! ## 2. From the per-tile iid LLN to the Palm tile mean law -/

/-- **The Palm tile mean law from the per-tile iid LLN.**  The repo chain
RootedTileMeanConvergence <- RootedTileSingleConvergence <-
RootedTileSingleConvergenceInProbability <- TileMeanConvergence is composed at the
concrete scene-cloud lane, so the single per-tile mean convergence proves
LowerLaneRootedTileMeanLaw. -/
theorem lowerLaneRootedTileMeanLaw_of_tileMeanConvergence
    (T : D.TaylorTiles ε) {A B : Set M}
    (pcloud qcloud : ∀ n, Fin (n + 1) → M)
    (base : ∀ n, Fin (n + 1) → T.Index → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (G : ℕ → (ℚ → M) → ℝ)
    (hmean : T.TileMeanConvergence
      (fun (f : (↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) (t : ℝ) (c : T.Index) ↦
        T.tilePopValue (P := P) (a := a) (κ := κ) (lambda := lambda) (q := q) G c)
      sceneCloudSample (sceneCloudX pcloud) (sceneCloudY qcloud) tileScale
      (fun f t n s c' ↦ normalizedProbe (K := A ∪ B) base t n s c')
      (uniformTilePlan (fun n ↦ Fin (n + 1)))) :
    LowerLaneRootedTileMeanLaw (P := P) (a := a) (κ := κ) (lambda := lambda) (q := q)
      T (A := A) (B := B) pcloud qcloud base G :=
  T.rootedTileMeanConvergence_of_single
    (fun (f : (↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) (t : ℝ) (c : T.Index) ↦
      T.tilePopValue (P := P) (a := a) (κ := κ) (lambda := lambda) (q := q) G c)
    sceneCloudSample (sceneCloudX pcloud) (sceneCloudY qcloud) tileScale
    (fun f t n s c' ↦ normalizedProbe (K := A ∪ B) base t n s c')
    (uniformTilePlan (fun n ↦ Fin (n + 1)))
    (T.rootedTileSingleConvergence_of_inProbability
      (fun (f : (↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) (t : ℝ) (c : T.Index) ↦
        T.tilePopValue (P := P) (a := a) (κ := κ) (lambda := lambda) (q := q) G c)
      sceneCloudSample (sceneCloudX pcloud) (sceneCloudY qcloud) tileScale
      (fun f t n s c' ↦ normalizedProbe (K := A ∪ B) base t n s c')
      (uniformTilePlan (fun n ↦ Fin (n + 1)))
      (T.rootedTileSingleConvergenceInProbability_of_tileMeanConvergence
        (fun (f : (↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) (t : ℝ) (c : T.Index) ↦
          T.tilePopValue (P := P) (a := a) (κ := κ) (lambda := lambda) (q := q) G c)
        sceneCloudSample (sceneCloudX pcloud) (sceneCloudY qcloud) tileScale
        (fun f t n s c' ↦ normalizedProbe (K := A ∪ B) base t n s c')
        (uniformTilePlan (fun n ↦ Fin (n + 1))) hmean))

/-! ## 3. From the plan-free per-tile LLN to the Palm tile mean law -/

/-- **The Palm tile mean law from the plan-free decomposition.**  The exact
plan-free decomposition identity of the expected frozen tile mean, the plan-free
per-tile LLN of its free part for every probe/tilt/tile, and the vanishing of the
residual prove LowerLaneRootedTileMeanLaw: this is the sharpest convergence
statement isolated by the repo (TileMeanConvergence is derived from it). -/
theorem lowerLaneRootedTileMeanLaw_of_planFree
    (T : D.TaylorTiles ε) {A B : Set M}
    (pcloud qcloud : ∀ n, Fin (n + 1) → M)
    (base : ∀ n, Fin (n + 1) → T.Index → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (G : ℕ → (ℚ → M) → ℝ)
    (free residual : ((↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) → ℝ → T.Index → ℕ → ℝ)
    (hplandec : ∀ (f : (↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) (t : ℝ) (c : T.Index) (n : ℕ),
      |(∫ s, T.tileValue f t sceneCloudSample (sceneCloudX pcloud) (sceneCloudY qcloud)
          tileScale (fun f t n s c' ↦ normalizedProbe (K := A ∪ B) base t n s c')
          (uniformTilePlan (fun n ↦ Fin (n + 1))) n c s ∂sceneCloudSample n) -
        T.tilePopValue (P := P) (a := a) (κ := κ) (lambda := lambda) (q := q) G c -
        (free f t c n + residual f t c n)| ≤ 0)
    (hfree : ∀ (f : (↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) (t : ℝ) (c : T.Index),
      PlanFreeTileLLN (free f t c))
    (hres : ∀ (f : (↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) (t : ℝ) (c : T.Index),
      Tendsto (fun n ↦ residual f t c n) atTop (𝓝 0)) :
    LowerLaneRootedTileMeanLaw (P := P) (a := a) (κ := κ) (lambda := lambda) (q := q)
      T (A := A) (B := B) pcloud qcloud base G :=
  lowerLaneRootedTileMeanLaw_of_tileMeanConvergence (T := T) (A := A) (B := B)
    pcloud qcloud base G
    (T.tileMeanConvergence_of_planFree sceneCloudSample G (sceneCloudX pcloud)
      (sceneCloudY qcloud) tileScale
      (fun f t n s c' ↦ normalizedProbe (K := A ∪ B) base t n s c')
      (uniformTilePlan (fun n ↦ Fin (n + 1))) free residual hplandec hfree hres)

/-! ## 4. With the residual derived from plan-free average-cost control -/

/-- **The Palm tile mean law from the plan-free LLN and average-cost control.**
The vanishing residual is not assumed: it is derived from plan-free average-cost
control, so the probabilistic inputs are exactly the plan-free per-tile LLN
family and that control. -/
theorem lowerLaneRootedTileMeanLaw_of_planFreeControl
    (T : D.TaylorTiles ε) {A B : Set M}
    (pcloud qcloud : ∀ n, Fin (n + 1) → M)
    (base : ∀ n, Fin (n + 1) → T.Index → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (G : ℕ → (ℚ → M) → ℝ)
    (free R fac : ((↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) → ℝ → T.Index → ℕ → ℝ)
    (hplandec : ∀ (f : (↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) (t : ℝ) (c : T.Index) (n : ℕ),
      |(∫ s, T.tileValue f t sceneCloudSample (sceneCloudX pcloud) (sceneCloudY qcloud)
          tileScale (fun f t n s c' ↦ normalizedProbe (K := A ∪ B) base t n s c')
          (uniformTilePlan (fun n ↦ Fin (n + 1))) n c s ∂sceneCloudSample n) -
        T.tilePopValue (P := P) (a := a) (κ := κ) (lambda := lambda) (q := q) G c -
        (free f t c n + R f t c n / ((n + 1 : ℕ) : ℝ))| ≤ 0)
    (hfree : ∀ (f : (↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) (t : ℝ) (c : T.Index),
      PlanFreeTileLLN (free f t c))
    (hcontrol : ∀ (f : (↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) (t : ℝ) (c : T.Index),
      PlanFreeAverageCostControl (R f t c) (fac f t c)) :
    LowerLaneRootedTileMeanLaw (P := P) (a := a) (κ := κ) (lambda := lambda) (q := q)
      T (A := A) (B := B) pcloud qcloud base G :=
  lowerLaneRootedTileMeanLaw_of_tileMeanConvergence (T := T) (A := A) (B := B)
    pcloud qcloud base G
    (T.tileMeanConvergence_of_planFreeControl sceneCloudSample G (sceneCloudX pcloud)
      (sceneCloudY qcloud) tileScale
      (fun f t n s c' ↦ normalizedProbe (K := A ∪ B) base t n s c')
      (uniformTilePlan (fun n ↦ Fin (n + 1))) free R fac hplandec hfree hcontrol)

