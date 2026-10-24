/-
# Analytic side conditions of the Palm-LLN lane, reduced to one typed bundle

This module reduces the analytic tile side conditions of the one remaining
probabilistic input of the lower endgame lane, PalmSideLowerLaneRootedTileMeanLaw (the
paper F16 Palm LLN), as delivered in FinslerOriginalTileCampbellMeanFromPalm.

## 1. The exact residual list of the Palm-LLN lane analytic hypotheses

Besides the Palm LLN itself the lane hId producer
(frozenCampbellMeanIdentification_sceneCloud_of_rootedTileMeanConvergencePalmSide) takes:

* the atlas readout family g, its piecewise-root identity hgt, the plan Assign,
  the population covering identity hdecomp, the masked-entry exchangeability
  hExch, the plan-residual vanishing hresv, and the entrywise / pair-sum /
  residual integrability hintEntry, hintCost, hintRes.  These nine items are
  exactly the fields of the repo structure TileLaneInputs;
* the bounded probe base: Bp >= 0 together with |base| <= Bp (hBp, hbase);
* per-tile integrability of the linear cost, probe, linear (split) and clipping
  integrands and of the frozen tile cost (hintC, hintP, hintLin, hintClip, hint);
* vanishing of the clipping correction (hclip).

## 2. What is discharged here

The structural fields hgt, hExch and hresv are already discharged by the repo
lane producer tileLaneInputs_of_laneData, and hdecomp by
tileLaneInputs_of_cellRefinement; the lane field of the bundle below is exactly
the output of those producers.  The clipping side condition hclip is proved
here in tileFixedPairClippingCorrection_sceneCloud_tendsto_zero from the repo
lemma tileFixedPairClippingCorrection_tendsto_zero_of_retainedEdge, the bounded
probe base (the normalized probe decays like 1/(n+1), lemma
normalizedProbe_abs_le), the clipping integrability, and the two retained-edge
window facts hz0 and hp.

## 3. The one typed bundle and the bundled lane

PalmLLNAnalyticBundle collects the nine lane fields and the six remaining
probe-base / integrability side conditions into one structure.  The bundled lane
endgameLowerFields_actual_lane_wired_of_palmLLNAnalyticBundle takes that bundle,
the two retained-edge window facts, the lane context and the Palm LLN as its only
probabilistic input, and returns the same EndgameLowerFields bundle as the wired
lane with both the frozen inputs and the hId identification derived.
-/

import OTSelector.Reconstruction.FinslerOriginalTileLaneInputs
import OTSelector.Reconstruction.FinslerOriginalTileBoundedCorrectionInsertion
import OTSelector.Reconstruction.FinslerOriginalEndgameLowerLaneWired

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


/-- **The one remaining probabilistic input: the Palm LLN (paper F16).**  The
rooted tile mean convergence of the counted per-tile frozen means towards the
population tile values, for the concrete scene-cloud lane. -/
def PalmSideLowerLaneRootedTileMeanLaw
    (T : D.TaylorTiles ε) {A B : Set M}
    (pcloud qcloud : ∀ n, Fin (n + 1) → M)
    (base : ∀ n, Fin (n + 1) → T.Index → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (G : ℕ → (ℚ → M) → ℝ) : Prop :=
  T.RootedTileMeanConvergence
    (fun (f : (↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) (t : ℝ) (c : T.Index) ↦
      T.tilePopValue (P := P) (a := a) (κ := κ) (lambda := lambda) (q := q) G c)
    sceneCloudSample (sceneCloudX pcloud) (sceneCloudY qcloud) tileScale
    (fun f t n s c' ↦ normalizedProbe (K := A ∪ B) base t n s c')
    (uniformTilePlan (fun n ↦ Fin (n + 1)))

/-! ## 2. The identification from the tile Palm sample law -/

/-- **The lane hId from the Palm LLN alone.**  The only probabilistic input is
PalmSideLowerLaneRootedTileMeanLaw, i.e. the rooted tile mean convergence
RootedTileMeanConvergence of the counted per-tile frozen means to the population
tile values (paper F16).  The TilePalmSampleLaw family is derived from it through
the fixed-pair transfer tileFixedPair_tendsto_of_rootedTileMeanConvergence
(via tilePalmSampleLaw_sceneCloud_of_rootedConvergence), and the identification
then follows from frozenCampbellMeanIdentification_of_palmSampleLaw. -/
theorem frozenCampbellMeanIdentification_sceneCloud_of_rootedTileMeanConvergencePalmSide
    (T : D.TaylorTiles ε) {A B : Set M}
    (pcloud qcloud : ∀ n, Fin (n + 1) → M)
    (base : ∀ n, Fin (n + 1) → T.Index → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    {Bp : ℝ} (hBp : 0 ≤ Bp)
    (hbase : ∀ (n : ℕ) (s : Fin (n + 1)) (c' : T.Index) (i j : Fin (n + 1)),
      |base n s c' i j| ≤ Bp)
    (hintC : ∀ (f : (↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) (t : ℝ) (n : ℕ) (c : T.Index), Integrable
      (T.tileLinearCostIntegrand (ε := ε) f t (sceneCloudX pcloud) (sceneCloudY qcloud) tileScale n c) (sceneCloudSample n))
    (hintP : ∀ (f : (↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) (t : ℝ) (n : ℕ) (c : T.Index), Integrable
      (T.tileLinearProbeIntegrand f t (sceneCloudX pcloud) (sceneCloudY qcloud)
        (fun (f : (↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) t n s c' ↦ normalizedProbe (K := A ∪ B) base t n s c') n c) (sceneCloudSample n))
    (hintLin : ∀ (f : (↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) (t : ℝ) (c : T.Index) (n : ℕ),
      Integrable (T.tileLinearIntegrand (ε := ε) f t (sceneCloudX pcloud) (sceneCloudY qcloud) tileScale
        (fun f t n s c' ↦ normalizedProbe (K := A ∪ B) base t n s c') n c) (sceneCloudSample n))
    (hintClip : ∀ (f : (↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) (t : ℝ) (n : ℕ) (c : T.Index), Integrable
      (T.tileClippingIntegrand (ε := ε) f t (sceneCloudX pcloud) (sceneCloudY qcloud) tileScale
        (fun (f : (↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) t n s c' ↦ normalizedProbe (K := A ∪ B) base t n s c') n c) (sceneCloudSample n))
    (hclip : ∀ (f : (↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) (t : ℝ) (c : T.Index),
      Tendsto (fun n ↦ T.tileFixedPairClippingCorrection f t sceneCloudSample (sceneCloudX pcloud) (sceneCloudY qcloud) tileScale
        (fun (f : (↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) t n s c' ↦ normalizedProbe (K := A ∪ B) base t n s c') n c)
        atTop (𝓝 0))
    (Assign : ∀ n, Fin (n + 1) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (hintEntry : ∀ (f : (↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) (t : ℝ) (n : ℕ) (c : T.Index)
      (i j : Fin (n + 1)),
      Integrable (fun s ↦ T.tileCostMatrix f t (sceneCloudX pcloud) (sceneCloudY qcloud) tileScale
        (fun (f : (↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) t n s c' ↦ normalizedProbe (K := A ∪ B) base t n s c') n c s i j)
        (sceneCloudSample n))
    (hExch : ∀ (f : (↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) (t : ℝ) (n : ℕ) (c : T.Index),
      MaskedEntryExchangeability (sceneCloudSample n) (T.tileCostMatrix f t (sceneCloudX pcloud) (sceneCloudY qcloud) tileScale
        (fun (f : (↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) t n s c' ↦ normalizedProbe (K := A ∪ B) base t n s c') n c))
    (hintCost : ∀ (f : (↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) (t : ℝ) (n : ℕ) (c : T.Index),
      Integrable (fun s ↦ ∑ i, ∑ j, T.tileCostMatrix f t (sceneCloudX pcloud) (sceneCloudY qcloud) tileScale
        (fun (f : (↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) t n s c' ↦ normalizedProbe (K := A ∪ B) base t n s c') n c s i j)
        (sceneCloudSample n))
    (hintRes : ∀ (f : (↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) (t : ℝ) (n : ℕ) (c : T.Index),
      Integrable (fun s ↦ ∑ i, ∑ j,
        (Assign n s i j - 1 / ((n + 1 : ℕ) : ℝ)) *
          T.tileCostMatrix f t (sceneCloudX pcloud) (sceneCloudY qcloud) tileScale
            (fun (f : (↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) t n s c' ↦ normalizedProbe (K := A ∪ B) base t n s c') n c s i j)
        (sceneCloudSample n))
    (hresv : T.TilePlanResidualVanishing sceneCloudSample Assign (sceneCloudX pcloud) (sceneCloudY qcloud) tileScale
      (fun (f : (↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) t n s c' ↦ normalizedProbe (K := A ∪ B) base t n s c'))
    (G : ℕ → (ℚ → M) → ℝ)
    (g : ((↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) → ℝ → (ℚ → M) → ℝ)
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _instTileCampbellFromPalmMetric : MetricSpace M := F.metricSpace;
      LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))
    (hint : ∀ (f : (↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) (t : ℝ) (n : ℕ) (c : T.Index),
      Integrable (T.tileFrozenCost (fun s i ↦ (sceneCloudX pcloud) n i s) (fun s i ↦ (sceneCloudY qcloud) n i s)
        (fun s c' ↦ normalizedProbe (K := A ∪ B) base t n s c')
        (Assign n) (tileScale n) t c) (sceneCloudSample n))
    (hgt : ∀ (f : (↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) (t : ℝ),
      g f t = atlasPiecewiseRoot P a κ lambda G)
    (hdecomp : ∀ (f : (↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) (t : ℝ),
      (∑' j, ∫ z in populationSeedRootPiece P a κ lambda j,
          populationAtlasTheta P a κ lambda j z ^ (-2 / q) * G j z ∂lambda) =
        (∑ c : T.Index, T.tilePopValue (P := P) (a := a) (κ := κ)
          (lambda := lambda) (q := q) G c))
    (hconv : PalmSideLowerLaneRootedTileMeanLaw (P := P) (a := a) (κ := κ)
      (lambda := lambda) (q := q) T (A := A) (B := B) pcloud qcloud base G) :
    RootedTileCampbellMeanIdentification P a κ lambda g q sceneCloudSample
      (hprobFrozenCostFamily (K := A ∪ B) T (sceneCloudX pcloud) (sceneCloudY qcloud)
        base Assign tileScale) T.Index := by
  have hPalm : ∀ (f : (↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) (t : ℝ) (c : T.Index),
      T.TilePalmSampleLaw (ε := ε) f t sceneCloudSample (sceneCloudX pcloud)
        (sceneCloudY qcloud) tileScale c
        (fun _ ↦ T.tilePopValue (P := P) (a := a) (κ := κ) (lambda := lambda) (q := q) G c) :=
    fun f t c ↦ T.tilePalmSampleLaw_sceneCloud_of_rootedConvergence f t pcloud qcloud base
      hBp hbase (hintLin f t c) (fun n ↦ hintClip f t n c) (fun n ↦ hintC f t n c)
      (fun n ↦ hintP f t n c) (hclip f t c) G
      (fun n c' i j ↦ hintEntry f t n c' i j) (fun n c' ↦ hExch f t n c') hconv
  exact rootedTileCampbellMeanIdentification_of_palmSampleLaw (T := T) sceneCloudSample G
    (sceneCloudX pcloud) (sceneCloudY qcloud) tileScale base hBp hbase hintC hintP
    hintClip hPalm hclip Assign hintEntry hExch hintCost hintRes hresv g hF
    hcomplete hu ha hinj hint hgt hdecomp

/-- **The one remaining analytic input bundle of the Palm-LLN lane.**  It packs
the repo tile lane structure (paper tile Campbell lane data: readout family, plan,
covering identity, masked-entry exchangeability, plan-residual vanishing and the
entrywise / pair-sum integrabilities), the bounded probe base, the per-tile
linear-cost / probe / split / clipping / frozen integrabilities into a single
typed hypothesis.  The clipping vanishing is not a field: it is derived from the
retained-edge window data in the bundled lane below. -/
structure PalmLLNAnalyticBundle
    (T : D.TaylorTiles ε) {A B : Set M}
    (pcloud qcloud : ∀ n, Fin (n + 1) → M)
    (base : ∀ n, Fin (n + 1) → T.Index → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (G : ℕ → (ℚ → M) → ℝ) : Type _ where
  lane : TileLaneInputs (P := P) (a := a) (κ := κ) (lambda := lambda) (D := D)
    (ε := ε) (K := A ∪ B) (q := q) (T := T) base sceneCloudSample
    (sceneCloudX pcloud) (sceneCloudY qcloud) tileScale G
  Bp : ℝ
  hBp : 0 ≤ Bp
  hbase : ∀ (n : ℕ) (s : Fin (n + 1)) (c' : T.Index) (i j : Fin (n + 1)),
    |base n s c' i j| ≤ Bp
  hintC : ∀ (f : (↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) (t : ℝ) (n : ℕ) (c : T.Index), Integrable
    (T.tileLinearCostIntegrand (ε := ε) f t (sceneCloudX pcloud) (sceneCloudY qcloud) tileScale n c) (sceneCloudSample n)
  hintP : ∀ (f : (↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) (t : ℝ) (n : ℕ) (c : T.Index), Integrable
    (T.tileLinearProbeIntegrand f t (sceneCloudX pcloud) (sceneCloudY qcloud)
      (fun (f : (↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) t n s c' ↦ normalizedProbe (K := A ∪ B) base t n s c') n c) (sceneCloudSample n)
  hintLin : ∀ (f : (↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) (t : ℝ) (c : T.Index) (n : ℕ),
    Integrable (T.tileLinearIntegrand (ε := ε) f t (sceneCloudX pcloud) (sceneCloudY qcloud) tileScale
      (fun f t n s c' ↦ normalizedProbe (K := A ∪ B) base t n s c') n c) (sceneCloudSample n)
  hintClip : ∀ (f : (↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) (t : ℝ) (n : ℕ) (c : T.Index), Integrable
    (T.tileClippingIntegrand (ε := ε) f t (sceneCloudX pcloud) (sceneCloudY qcloud) tileScale
      (fun (f : (↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) t n s c' ↦ normalizedProbe (K := A ∪ B) base t n s c') n c) (sceneCloudSample n)
  hint : ∀ (f : (↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) (t : ℝ) (n : ℕ) (c : T.Index),
    Integrable (T.tileFrozenCost (fun s i ↦ (sceneCloudX pcloud) n i s) (fun s i ↦ (sceneCloudY qcloud) n i s)
      (fun s c' ↦ normalizedProbe (K := A ∪ B) base t n s c')
      (lane.Assign n) (tileScale n) t c) (sceneCloudSample n)

/-- **Constructor of the bundle from the repo lane producer output.**  The nine
lane fields are supplied by the repo structure TileLaneInputs (the output of
tileLaneInputs_of_laneData / tileLaneInputs_of_cellRefinement, which already
discharge hgt, hExch, hresv and hdecomp); only the bounded probe base and the
per-tile integrability conditions remain explicit. -/
noncomputable def PalmLLNAnalyticBundle_of_tileLaneInputs
    (T : D.TaylorTiles ε) {A B : Set M}
    (pcloud qcloud : ∀ n, Fin (n + 1) → M)
    (base : ∀ n, Fin (n + 1) → T.Index → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (G : ℕ → (ℚ → M) → ℝ)
    {Bp : ℝ} (hBp : 0 ≤ Bp)
    (hbase : ∀ (n : ℕ) (s : Fin (n + 1)) (c' : T.Index) (i j : Fin (n + 1)),
      |base n s c' i j| ≤ Bp)
    (lane : TileLaneInputs (P := P) (a := a) (κ := κ) (lambda := lambda) (D := D)
      (ε := ε) (K := A ∪ B) (q := q) (T := T) base sceneCloudSample
      (sceneCloudX pcloud) (sceneCloudY qcloud) tileScale G)
    (hintC : ∀ (f : (↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) (t : ℝ) (n : ℕ) (c : T.Index), Integrable
      (T.tileLinearCostIntegrand (ε := ε) f t (sceneCloudX pcloud) (sceneCloudY qcloud) tileScale n c) (sceneCloudSample n))
    (hintP : ∀ (f : (↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) (t : ℝ) (n : ℕ) (c : T.Index), Integrable
      (T.tileLinearProbeIntegrand f t (sceneCloudX pcloud) (sceneCloudY qcloud)
        (fun (f : (↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) t n s c' ↦ normalizedProbe (K := A ∪ B) base t n s c') n c) (sceneCloudSample n))
    (hintLin : ∀ (f : (↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) (t : ℝ) (c : T.Index) (n : ℕ),
      Integrable (T.tileLinearIntegrand (ε := ε) f t (sceneCloudX pcloud) (sceneCloudY qcloud) tileScale
        (fun f t n s c' ↦ normalizedProbe (K := A ∪ B) base t n s c') n c) (sceneCloudSample n))
    (hintClip : ∀ (f : (↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) (t : ℝ) (n : ℕ) (c : T.Index), Integrable
      (T.tileClippingIntegrand (ε := ε) f t (sceneCloudX pcloud) (sceneCloudY qcloud) tileScale
        (fun (f : (↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) t n s c' ↦ normalizedProbe (K := A ∪ B) base t n s c') n c) (sceneCloudSample n))
    (hint : ∀ (f : (↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) (t : ℝ) (n : ℕ) (c : T.Index),
      Integrable (T.tileFrozenCost (fun s i ↦ (sceneCloudX pcloud) n i s) (fun s i ↦ (sceneCloudY qcloud) n i s)
        (fun s c' ↦ normalizedProbe (K := A ∪ B) base t n s c')
        (lane.Assign n) (tileScale n) t c) (sceneCloudSample n)) :
    PalmLLNAnalyticBundle (P := P) (a := a) (κ := κ) (lambda := lambda) (D := D)
      (ε := ε) (q := q) (T := T) (A := A) (B := B) pcloud qcloud base G :=
  { lane := lane
    Bp := Bp
    hBp := hBp
    hbase := hbase
    hintC := hintC
    hintP := hintP
    hintLin := hintLin
    hintClip := hintClip
    hint := hint }
/-- **The clipping correction vanishes on the scene-cloud lane.**  This discharges
the clipping side condition of the Palm-LLN lane from the retained-edge window
data, the bounded probe base (whose normalized form decays like 1/(n+1)) and the
clipping integrability. -/
theorem tileFixedPairClippingCorrection_sceneCloud_tendsto_zero
    (T : D.TaylorTiles ε) {A B : Set M}
    (pcloud qcloud : ∀ n, Fin (n + 1) → M)
    (base : ∀ n, Fin (n + 1) → T.Index → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    {Bp : ℝ} (hBp : 0 ≤ Bp)
    (hbase : ∀ (n : ℕ) (s : Fin (n + 1)) (c' : T.Index) (i j : Fin (n + 1)),
      |base n s c' i j| ≤ Bp)
    (hintClip : ∀ (f : (↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) (t : ℝ) (n : ℕ) (c : T.Index), Integrable
      (T.tileClippingIntegrand (ε := ε) f t (sceneCloudX pcloud) (sceneCloudY qcloud) tileScale
        (fun (f : (↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) t n s c' ↦ normalizedProbe (K := A ∪ B) base t n s c') n c) (sceneCloudSample n))
    (hε : ε ≤ 1 / 2)
    (hz₀ : ∀ c : T.Index, T.reference c ∈ (T.cover c.1).centers)
    (hp : ∀ (c : T.Index) (n : ℕ) (s : Fin (n + 1)),
      (u ((sceneCloudX pcloud) n ⟨0, Nat.succ_pos n⟩ s), u ((sceneCloudY qcloud) n ⟨0, Nat.succ_pos n⟩ s)) ∈
        (T.core c).window.region)
    (f : (↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) (t : ℝ) (c : T.Index) :
    Tendsto (fun n ↦ T.tileFixedPairClippingCorrection f t sceneCloudSample
      (sceneCloudX pcloud) (sceneCloudY qcloud) tileScale
      (fun (f : (↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) t n s c' ↦ normalizedProbe (K := A ∪ B) base t n s c') n c)
      atTop (𝓝 0) :=
  T.tileFixedPairClippingCorrection_tendsto_zero_of_retainedEdge sceneCloudSample f t
    (sceneCloudX pcloud) (sceneCloudY qcloud) tileScale
    (fun (f : (↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) t n s c' ↦ normalizedProbe (K := A ∪ B) base t n s c')
    c hε (fun n ↦ le_of_lt (by unfold tileScale; positivity)) (hz₀ c) (hp c) hBp
    (fun n s i j ↦ normalizedProbe_abs_le base hBp hbase t n s c i j)
    (fun n ↦ hintClip f t n c)

/-- **The Palm-LLN lower lane with the analytic side conditions bundled.**  The
same bundle as endgameLowerFields_actual_lane_wired, with both the frozen inputs
and the hId identification derived.  The only probabilistic input is the Palm LLN
hconv; its analytic side conditions are supplied by the single typed bundle
PalmLLNAnalyticBundle, together with the two retained-edge window facts hz0 and
hp from which the clipping vanishing is derived. -/
noncomputable def endgameLowerFields_actual_lane_wired_of_palmLLNAnalyticBundle
    (T : D.TaylorTiles ε)
    [PseudoMetricSpace M]
    (hdim : 6 ≤ Module.finrank ℝ E)
    (ωM : Measure M) (dens₀ dens₁ : M → ℝ)
    [IsProbabilityMeasure (ωM.withDensity (fun x ↦ ENNReal.ofReal (dens₀ x)))]
    [IsProbabilityMeasure (ωM.withDensity (fun x ↦ ENNReal.ofReal (dens₁ x)))]
    {A B : Set M} (hA : IsCompact A) (hB : IsCompact B)
    (hμA : ∀ᵐ x ∂(physicalSourceProbability ωM dens₀ : Measure M), x ∈ A)
    (hνB : ∀ᵐ y ∂(physicalTargetProbability ωM dens₁ : Measure M), y ∈ B)
    (pcloud qcloud : ∀ n, Fin (n + 1) → M)
    (hX : ∀ n i, Measurable ((sceneCloudX pcloud) n i))
    (hY : ∀ n i, Measurable ((sceneCloudY qcloud) n i))
    (hXi : ∀ n, iIndepFun ((sceneCloudX pcloud) n) (sceneCloudSample n))
    (hYi : ∀ n, iIndepFun ((sceneCloudY qcloud) n) (sceneCloudSample n))
    (hXlaw : ∀ n i, (sceneCloudSample n).map ((sceneCloudX pcloud) n i) =
      (physicalSourceProbability ωM dens₀ : Measure M))
    (hYlaw : ∀ n i, (sceneCloudSample n).map ((sceneCloudY qcloud) n i) =
      (physicalTargetProbability ωM dens₁ : Measure M))
    (hXY : ∀ n, IndepFun (fun s i ↦ (sceneCloudX pcloud) n i s)
      (fun s i ↦ (sceneCloudY qcloud) n i s) (sceneCloudSample n))
    (base : ∀ n, Fin (n + 1) → T.Index → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (G : ℕ → (ℚ → M) → ℝ)
    (S : PalmLLNAnalyticBundle (P := P) (a := a) (κ := κ) (lambda := lambda)
      (D := D) (ε := ε) (q := q) (T := T) (A := A) (B := B) pcloud qcloud base G)
    (hz₀ : ∀ c : T.Index, T.reference c ∈ (T.cover c.1).centers)
    (hp : ∀ (c : T.Index) (n : ℕ) (s : Fin (n + 1)),
      (u ((sceneCloudX pcloud) n ⟨0, Nat.succ_pos n⟩ s), u ((sceneCloudY qcloud) n ⟨0, Nat.succ_pos n⟩ s)) ∈
        (T.core c).window.region)
    (hconv : PalmSideLowerLaneRootedTileMeanLaw (P := P) (a := a) (κ := κ)
      (lambda := lambda) (q := q) T (A := A) (B := B) pcloud qcloud base G)
    {Bphys : ℝ} (hBphys : 0 ≤ Bphys)
    (hphys : ∀ (n : ℕ) (c : T.Index) (s : Fin (n + 1)) (i j : Fin (n + 1)),
      (T.core c).frozenPhysicalCost (T.reference c)
        ((sceneCloudX pcloud) n i s) ((sceneCloudY qcloud) n j s) ≤ Bphys)
    (hAssignDS : ∀ (n : ℕ) (s : Fin (n + 1)),
      S.lane.Assign n s ∈ doublyStochastic ℝ (Fin (n + 1)))
    (hmeas : ∀ (f : (↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) (t : ℝ) (n : ℕ) (c : T.Index),
      Measurable (fun s : Fin (n + 1) ↦
        T.tileFrozenCost (fun s' i ↦ (sceneCloudX pcloud) n i s')
          (fun s' i ↦ (sceneCloudY qcloud) n i s')
          (fun s' c' ↦ normalizedProbe (K := A ∪ B) base t n s' c')
          (S.lane.Assign n) (tileScale n) t c s))
    (hPopt : ∀ (f : (↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) (t : ℝ) (n : ℕ),
      ∀ᵐ s ∂sceneCloudSample n,
      OptimalFractionalAssignment (perturbedEdgeCost
        (fun i j ↦ (((n + 1 : ℕ) : ℝ) ^
            (2 / ((Module.finrank ℝ E : ℝ) - 1))) *
          distanceSlackEdgeCost (fun i ↦ (sceneCloudX pcloud) n i s)
            (fun i ↦ (sceneCloudY qcloud) n i s) u i j)
        (carrierProbeMatrix (physicalSourceProbability ωM dens₀)
          (physicalTargetProbability ωM dens₁) (A ∪ B) (hA.union hB).measurableSet
          (hμA.mono fun _ hx ↦ Or.inl hx) (hνB.mono fun _ hy ↦ Or.inr hy)
          (fun i ↦ (sceneCloudX pcloud) n i s) (fun i ↦ (sceneCloudY qcloud) n i s) f) t)
        (S.lane.Assign n s))
    (hgeom : ∀ (n : ℕ), ∀ᵐ s ∂sceneCloudSample n, ∀ (c : T.Index) (i j : Fin (n + 1)),
      (i, j) ∈ T.edgeEvent (fun i ↦ (sceneCloudX pcloud) n i s)
          (fun i ↦ (sceneCloudY qcloud) n i s) c →
      FrozenCoreEdgeGeometry (T.core c) (T.cover c.1)
        (fun _ _ ↦ T.reference c) (fun i ↦ (sceneCloudX pcloud) n i s)
        (fun i ↦ (sceneCloudY qcloud) n i s) i j)
    (hgh : ∀ (f : (↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) (t : ℝ) (n : ℕ),
      ∀ᵐ s ∂sceneCloudSample n, ∀ (c : T.Index) (i j : Fin (n + 1)),
      (i, j) ∈ T.edgeEvent (fun i ↦ (sceneCloudX pcloud) n i s)
          (fun i ↦ (sceneCloudY qcloud) n i s) c →
      |carrierProbeMatrix (physicalSourceProbability ωM dens₀)
          (physicalTargetProbability ωM dens₁) (A ∪ B) (hA.union hB).measurableSet
          (hμA.mono fun _ hx ↦ Or.inl hx) (hνB.mono fun _ hy ↦ Or.inr hy)
          (fun i ↦ (sceneCloudX pcloud) n i s) (fun i ↦ (sceneCloudY qcloud) n i s) f i j -
        normalizedProbe (K := A ∪ B) base t n s c i j| ≤ (‖f‖₊ : ℝ))
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _instEndgameLowerLaneWiredMetric : MetricSpace M := F.metricSpace
      LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))
    (hε : 0 ≤ ε) (hε1 : 2 * ε < 1)
    (hdist : ∀ x y : M, dist x y = (F.lengthEDist x y).toReal)
    (Ψ : ((↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) → ℝ → ℝ)
    (hread : frozenPressureLower P a κ lambda S.lane.g q = Ψ) :
    EndgameLowerFields F (physicalSourceProbability ωM dens₀)
      (physicalTargetProbability ωM dens₁) hA hB hμA hνB sceneCloudSample
      (sceneCloudX pcloud) (sceneCloudY qcloud) u := by
  have hε12 : ε ≤ 1 / 2 := by linarith
  exact endgameLowerFields_actual_lane_wired (T := T) hdim ωM dens₀ dens₁ hA hB
    hμA hνB pcloud qcloud hX hY hXi hYi hXlaw hYlaw hXY base S.hBp hBphys
    S.hbase hphys S.lane.Assign hAssignDS hmeas hPopt hgeom hgh hF hcomplete hu
    ha hinj hε hε1 hdist S.lane.g
    (hId := frozenCampbellMeanIdentification_sceneCloud_of_rootedTileMeanConvergencePalmSide
      (T := T) (A := A) (B := B) pcloud qcloud base S.hBp S.hbase S.hintC
      S.hintP S.hintLin S.hintClip
      (fun f t c ↦ tileFixedPairClippingCorrection_sceneCloud_tendsto_zero (T := T)
        (A := A) (B := B) pcloud qcloud base S.hBp S.hbase S.hintClip hε12 hz₀ hp
        f t c)
      S.lane.Assign S.lane.hintEntry S.lane.hExch S.lane.hintCost S.lane.hintRes
      S.lane.hresv G S.lane.g hF hcomplete hu ha hinj S.hint S.lane.hgt
      S.lane.hdecomp hconv)
    (hread := hread)

end OTSelector.Reconstruction
