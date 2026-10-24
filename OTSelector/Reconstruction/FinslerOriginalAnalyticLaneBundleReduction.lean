import OTSelector.Reconstruction.FinslerOriginalLowerLaneMeanLawClosed

/-!
# Collapsing the analytic lane side conditions into one scene-cloud bundle

## 1. What the repo already discharges or bundles (FinslerOriginalPalmLLNAnalyticSideConditions)

* the lane structure of the tile lane (atlas readout family, thin plan, masked-entry
  exchangeability, entrywise/pair-sum integrability, plan-residual vanishing,
  population covering identity) is packaged in the repo structure TileLaneInputs, whose
  producer tileLaneInputs_of_laneData already discharges hgt (rfl), hExch (from the iid
  slot laws and pair independence: maskedEntryExchangeability_tileCostMatrix_forall) and
  hresv (from the scale bounds: tilePlanResidualVanishing_of_scaleBounds); hdecomp is
  discharged by tileLaneInputs_of_cellRefinement;
* the bounded probe base (Bp, hBp, hbase) and the per-tile linear-cost / probe / split /
  clipping / frozen integrabilities (hintC, hintP, hintLin, hintClip, hint) are packaged
  in PalmLLNAnalyticBundle; note that its hintLin is the same condition as the
  hlaw-consumer's hintLin;
* the clipping correction vanishing hclip is NOT a binder of the Palm sample-law route:
  it is derived from the retained-edge data hz0, hp, the bounded probe base and hε by
  tileFixedPairClippingCorrection_sceneCloud_tendsto_zero, and is used internally by
  lowerLaneRootedTileMeanLaw_of_palmSampleLaw (through the fixed-pair split).

Hence the only remaining explicit analytic side conditions of
lowerLaneRootedTileMeanLaw_of_palmSampleLaw are: hintEntry, hExch, hintCost, hintRes,
hresv, Bp, hBp, hbase, hintC, hintP, hintLin, hintClip, and the retained-edge/lane data
hε, hz0, hp.  They are packaged below in one typed structure.

## 2. The bundle

SceneCloudAnalyticLaneBundle collects exactly those conditions, at the concrete
instance sceneCloudSample / uniformTilePlan / normalizedProbe / tileScale.

## 3. The bundled consuming theorem

lowerLaneRootedTileMeanLaw_of_palmSampleLaw_and_bundle takes only the Palm sample law
family hlaw and the bundle, and returns LowerLaneRootedTileMeanLaw.  The residual list
is therefore: hlaw, the bundle (analytic side conditions) - nothing else.

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
/-- **The scene-cloud analytic lane bundle.**  One typed hypothesis packaging the
remaining analytic side conditions of the Palm sample-law route to
LowerLaneRootedTileMeanLaw: the entrywise/pair-sum integrabilities, the masked-entry
exchangeability, the plan-residual vanishing, the bounded probe base, the linear
cost/probe/split/clipping integrabilities, and the retained-edge window data. -/
structure SceneCloudAnalyticLaneBundle
    (T : D.TaylorTiles ε) {A B : Set M}
    (pcloud qcloud : ∀ n, Fin (n + 1) → M)
    (base : ∀ n, Fin (n + 1) → T.Index → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (G : ℕ → (ℚ → M) → ℝ) : Type _ where
  hintEntry : ∀ (f : (↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) (t : ℝ) (n : ℕ) (c : T.Index)
    (i j : Fin (n + 1)),
    Integrable (fun s ↦ T.tileCostMatrix f t (sceneCloudX pcloud) (sceneCloudY qcloud)
      tileScale (fun f t n s c' ↦ normalizedProbe (K := A ∪ B) base t n s c')
      n c s i j) (sceneCloudSample n)
  hExch : ∀ (f : (↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) (t : ℝ) (n : ℕ) (c : T.Index),
    MaskedEntryExchangeability (sceneCloudSample n)
      (T.tileCostMatrix f t (sceneCloudX pcloud) (sceneCloudY qcloud) tileScale
        (fun f t n s c' ↦ normalizedProbe (K := A ∪ B) base t n s c') n c)
  hintCost : ∀ (f : (↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) (t : ℝ) (n : ℕ) (c : T.Index),
    Integrable (fun s ↦ ∑ i, ∑ j,
      T.tileCostMatrix f t (sceneCloudX pcloud) (sceneCloudY qcloud) tileScale
        (fun f t n s c' ↦ normalizedProbe (K := A ∪ B) base t n s c') n c s i j)
      (sceneCloudSample n)
  hintRes : ∀ (f : (↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) (t : ℝ) (n : ℕ) (c : T.Index),
    Integrable (fun s ↦ ∑ i, ∑ j,
      (uniformTilePlan (fun n ↦ Fin (n + 1)) n s i j - 1 / ((n + 1 : ℕ) : ℝ)) *
        T.tileCostMatrix f t (sceneCloudX pcloud) (sceneCloudY qcloud) tileScale
          (fun f t n s c' ↦ normalizedProbe (K := A ∪ B) base t n s c') n c s i j)
      (sceneCloudSample n)
  hresv : T.TilePlanResidualVanishing sceneCloudSample
    (uniformTilePlan (fun n ↦ Fin (n + 1))) (sceneCloudX pcloud) (sceneCloudY qcloud)
    tileScale
    (fun (f : (↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) t n s c' ↦
      normalizedProbe (K := A ∪ B) base t n s c')
  Bp : ℝ
  hBp : 0 ≤ Bp
  hbase : ∀ (n : ℕ) (s : Fin (n + 1)) (c' : T.Index) (i j : Fin (n + 1)),
    |base n s c' i j| ≤ Bp
  hintC : ∀ (f : (↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) (t : ℝ) (n : ℕ) (c : T.Index),
    Integrable (T.tileLinearCostIntegrand (ε := ε) f t (sceneCloudX pcloud)
      (sceneCloudY qcloud) tileScale n c) (sceneCloudSample n)
  hintP : ∀ (f : (↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) (t : ℝ) (n : ℕ) (c : T.Index),
    Integrable (T.tileLinearProbeIntegrand f t (sceneCloudX pcloud)
      (sceneCloudY qcloud)
      (fun f t n s c' ↦ normalizedProbe (K := A ∪ B) base t n s c') n c)
      (sceneCloudSample n)
  hintLin : ∀ (f : (↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) (t : ℝ) (n : ℕ) (c : T.Index),
    Integrable (T.tileLinearIntegrand (ε := ε) f t (sceneCloudX pcloud)
      (sceneCloudY qcloud) tileScale
      (fun f t n s c' ↦ normalizedProbe (K := A ∪ B) base t n s c') n c)
      (sceneCloudSample n)
  hintClip : ∀ (f : (↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) (t : ℝ) (n : ℕ) (c : T.Index),
    Integrable (T.tileClippingIntegrand (ε := ε) f t (sceneCloudX pcloud)
      (sceneCloudY qcloud) tileScale
      (fun f t n s c' ↦ normalizedProbe (K := A ∪ B) base t n s c') n c)
      (sceneCloudSample n)
  hε : ε ≤ 1 / 2
  hz₀ : ∀ c : T.Index, T.reference c ∈ (T.cover c.1).centers
  hp : ∀ (c : T.Index) (n : ℕ) (s : Fin (n + 1)),
    (u ((sceneCloudX pcloud) n ⟨0, Nat.succ_pos n⟩ s),
      u ((sceneCloudY qcloud) n ⟨0, Nat.succ_pos n⟩ s)) ∈ (T.core c).window.region

/-- **LowerLaneRootedTileMeanLaw from the Palm sample law and ONE analytic bundle.**
All eleven analytic side-condition binders plus the retained-edge data are consumed as
one structure; the only probabilistic input is the tile Palm sample law family hlaw. -/
theorem lowerLaneRootedTileMeanLaw_of_palmSampleLaw_and_bundle
    (T : D.TaylorTiles ε) {A B : Set M}
    (pcloud qcloud : ∀ n, Fin (n + 1) → M)
    (base : ∀ n, Fin (n + 1) → T.Index → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (G : ℕ → (ℚ → M) → ℝ)
    (bundle : SceneCloudAnalyticLaneBundle (P := P) (a := a) (κ := κ) (lambda := lambda)
      (D := D) (ε := ε) (T := T) (A := A) (B := B) pcloud qcloud base G)
    (hlaw : ∀ (f : (↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) (t : ℝ) (c : T.Index),
      T.TilePalmSampleLaw (ε := ε) f t sceneCloudSample (sceneCloudX pcloud)
        (sceneCloudY qcloud) tileScale c
        (fun _ ↦ T.tilePopValue (P := P) (a := a) (κ := κ) (lambda := lambda) (q := q) G c)) :
    LowerLaneRootedTileMeanLaw (P := P) (a := a) (κ := κ) (lambda := lambda) (q := q)
      T (A := A) (B := B) pcloud qcloud base G :=
  lowerLaneRootedTileMeanLaw_of_palmSampleLaw (T := T) (A := A) (B := B)
    pcloud qcloud base G
    bundle.hintEntry bundle.hExch bundle.hintCost bundle.hintRes bundle.hresv
    bundle.hBp bundle.hbase bundle.hintC bundle.hintP bundle.hintLin bundle.hintClip
    bundle.hε bundle.hz₀ bundle.hp hlaw
