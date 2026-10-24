import OTSelector.Reconstruction.FinslerOriginalCanonicalPalmLawTransfer
import OTSelector.Reconstruction.FinslerOriginalPalmSampleLawProof
import OTSelector.Reconstruction.FinslerOriginalPressureLowerReadout
import OTSelector.Reconstruction.FinslerOriginalTilePopValueIdentification
import OTSelector.Reconstruction.FinslerOriginalMaskCouplingLaw
import OTSelector.Reconstruction.FinslerOriginalTileMeanConvergence
import OTSelector.Reconstruction.FinslerOriginalTileCountingLaw
import OTSelector.Reconstruction.FinslerOriginalRootedTileSingleInstantiation
import OTSelector.Reconstruction.FinslerOriginalTileSingleConvergenceProof

/-!
# The Palm LLN read per probe and tilt: population families at the canonical root

FinslerOriginalCanonicalPalmLawTransfer proved the canonical Palm law from V7's
hlln + hpop binders read per (f,t), and reduced the canonical Palm LLN to a
per-(f,t) tile mean convergence family.  That module left the per-(f,t)
residuals explicit because the repo's TileMeanConvergence chain is stated at a
single fixed root family G.  This module removes those residuals as separate
inputs by packaging the V7 population data as families read at the canonical
root family fun j z => rootedFrozenIntegrand ... f t j z and by running the repo
chain pointwise in (f, t, c).

## The two population families

* PopulationPalmLLNFamily: the (f,t,c)-indexed version of V7's hlln + hpop read
  at the canonical family.  Its fields are
  - hlln: the empirical Palm LLN of the scene-cloud average against the
    population readout popReadout f t c;
  - hpop: the population normalization identity, whose target is the tile
    Campbell value of the canonical root family of the SAME probe and tilt.
* PopulationTileMeanFamily: the (f,t,c)-indexed version of the output of hpop:
  the per-tile iid LLN of the tile frozen means with population value
  T.tilePopValue of the canonical family at the same (f,t).

## Pointwise vs uniform

The fixed-G producers of the repo (tileMeanConvergence_of_palmSampleLaw etc.)
are stated uniformly over the probe and tilt, but their proofs are pointwise:
the only place the fixed root family G is used is the population value
T.tilePopValue G c, and every hypothesis they consume except the Palm law is
already (f,t,c)-indexed.  This module records that no (f,t)-uniformity is
genuinely needed for the Palm LLN: replacing the constant root family by the
(f,t)-dependent canonical family in the proof of
tileMeanConvergence_of_palmSampleLaw yields the family statement
tileMeanConvergenceFamily_of_palmSampleLawFamily, and the required
fixed-pair identification at each (f,t,c) is a single per-point application of
fixedPairMeanIdentification_of_palmSampleLaw.  The uniform statements of the
repo are therefore cosmetic, not a genuine (f,t)-uniformity hypothesis.

## What remains

The remaining inputs are exactly the analytic lane side conditions of the repo
(the base probe bound, the linear cost/probe/clipping integrability, the
fixed-pair clipping vanishing, the masked-entry exchangeability, the plan-cost
and plan-residual integrability, the plan-residual vanishing), plus the
population covering family of CanonicalPalmLawTransfer and the geometric lane
data hF hcomplete hu ha hinj.  No probabilistic input beyond
PopulationPalmLLNFamily occurs.

No sorry, admit or added axiom occurs.
-/

open Set Function Matrix Filter MeasureTheory ProbabilityTheory Manifold Module
  OTSelector.Probability
open OTSelector.Geometry
open OTSelector.PointProcess OTSelector.PointProcess.StationaryForwardMatching
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
open OTSelector.PointProcess OTSelector.PointProcess.StationaryForwardMatching
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
  {ε : ℝ} {A B : Set M}

/-! ## 1. The two (f,t,c)-indexed population families -/

/-- **The population Palm LLN family.**

The (f,t,c)-indexed version of V7's hlln + hpop binders, read at the canonical
root family fun j z => rootedFrozenIntegrand ... f t j z: the empirical Palm LLN
of the scene-cloud tile average against the population readout popReadout f t c,
and the population normalization identity whose target is the tile Campbell
value of the canonical family of the same probe f and tilt t. -/
structure PopulationPalmLLNFamily (T : D.TaylorTiles ε) {A B : Set M}
    (pcloud qcloud : ∀ n, Fin (n + 1) → M)
    (q : ℝ) (α β : Measure OTSelector.UnitMark)
    (coef : FinalProbeSpace A B → ℕ → (ℚ → M) → ℝ → ℝ → ℝ)
    (probeFam : FinalProbeSpace A B → ℕ → (ℚ → M) →
      MarkedCloudPoint → MarkedCloudPoint → ℝ)
    (Mst : FinalProbeSpace A B → ℝ → ℕ → (ℚ → M) →
      StationaryForwardMatching α β) : Type _ where
  popReadout : FinalProbeSpace A B → ℝ → T.Index → ℕ → ℝ
  hlln : ∀ (f : FinalProbeSpace A B) (t : ℝ) (c : T.Index),
    Tendsto (fun n ↦ T.sceneCloudAverage pcloud qcloud n c -
      popReadout f t c n) atTop (𝓝 0)
  hpop : ∀ (f : FinalProbeSpace A B) (t : ℝ) (c : T.Index),
    Tendsto (fun n ↦ (1 - 2 * ε) * (tileScale n * popReadout f t c n) -
      T.tilePopValue (P := P) (a := a) (κ := κ) (lambda := lambda) (q := q)
        (canonicalRootedIntegrand (A := A) (B := B) (P := P) (a := a)
          (κ := κ) (lambda := lambda) α β coef probeFam Mst q f t) c)
      atTop (𝓝 0)

/-- **The population tile mean family.**

The (f,t,c)-indexed version of the output of V7's hpop read at the canonical
family: the per-tile iid LLN TileMeanConvergence of the tile frozen means with
population value the tile Campbell value of the canonical root family of the
same probe and tilt. -/
def PopulationTileMeanFamily (T : D.TaylorTiles ε) {A B : Set M}
    (pcloud qcloud : ∀ n, Fin (n + 1) → M)
    (base : ∀ n, Fin (n + 1) → T.Index → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (q : ℝ) (α β : Measure OTSelector.UnitMark)
    (coef : FinalProbeSpace A B → ℕ → (ℚ → M) → ℝ → ℝ → ℝ)
    (probeFam : FinalProbeSpace A B → ℕ → (ℚ → M) →
      MarkedCloudPoint → MarkedCloudPoint → ℝ)
    (Mst : FinalProbeSpace A B → ℝ → ℕ → (ℚ → M) →
      StationaryForwardMatching α β) : Prop :=
  T.TileMeanConvergence (K := A ∪ B)
    (fun (f : FinalProbeSpace A B) (t : ℝ) (c : T.Index) ↦
      T.tilePopValue (P := P) (a := a) (κ := κ) (lambda := lambda) (q := q)
        (canonicalRootedIntegrand (A := A) (B := B) (P := P) (a := a)
          (κ := κ) (lambda := lambda) α β coef probeFam Mst q f t) c)
    sceneCloudSample (sceneCloudX pcloud) (sceneCloudY qcloud) tileScale
    (fun f t n s c' ↦ normalizedProbe (K := A ∪ B) base t n s c')
    (uniformTilePlan (fun n ↦ Fin (n + 1)))

/-! ## 2. The Palm law family from hlln + hpop, pointwise -/

/-- **The tile Palm sample law family from the hlln/hpop families.**

This is the repo's fixed-G producer tilePalmSampleLaw_sceneCloud_of_LLN applied
at each (f,t) with the root family canonicalRootedIntegrand ... f t: no (f,t)
uniformity is used, the producer is a per-point construction from the per-point
residuals hlln f t c and hpop f t c. -/
noncomputable def tilePalmSampleLawFamily_sceneCloud_of_LLNFamily
    (T : D.TaylorTiles ε) {A B : Set M}
    (pcloud qcloud : ∀ n, Fin (n + 1) → M)
    (q : ℝ) (α β : Measure OTSelector.UnitMark)
    (coef : FinalProbeSpace A B → ℕ → (ℚ → M) → ℝ → ℝ → ℝ)
    (probeFam : FinalProbeSpace A B → ℕ → (ℚ → M) →
      MarkedCloudPoint → MarkedCloudPoint → ℝ)
    (Mst : FinalProbeSpace A B → ℝ → ℕ → (ℚ → M) →
      StationaryForwardMatching α β)
    (popReadout : FinalProbeSpace A B → ℝ → T.Index → ℕ → ℝ)
    (hlln : ∀ (f : FinalProbeSpace A B) (t : ℝ) (c : T.Index),
      Tendsto (fun n ↦ T.sceneCloudAverage pcloud qcloud n c -
        popReadout f t c n) atTop (𝓝 0))
    (hpop : ∀ (f : FinalProbeSpace A B) (t : ℝ) (c : T.Index),
      Tendsto (fun n ↦ (1 - 2 * ε) * (tileScale n * popReadout f t c n) -
        T.tilePopValue (P := P) (a := a) (κ := κ) (lambda := lambda) (q := q)
          (canonicalRootedIntegrand (A := A) (B := B) (P := P) (a := a)
            (κ := κ) (lambda := lambda) α β coef probeFam Mst q f t) c)
        atTop (𝓝 0)) :
    ∀ (f : FinalProbeSpace A B) (t : ℝ) (c : T.Index),
      T.TilePalmSampleLaw (ε := ε) f t sceneCloudSample (sceneCloudX pcloud)
        (sceneCloudY qcloud) tileScale c
        (fun _ ↦ T.tilePopValue (P := P) (a := a) (κ := κ) (lambda := lambda)
          (q := q) (canonicalRootedIntegrand (A := A) (B := B) (P := P) (a := a)
            (κ := κ) (lambda := lambda) α β coef probeFam Mst q f t) c) :=
  fun f t c ↦ tilePalmSampleLaw_sceneCloud_of_LLN (T := T) (A := A) (B := B)
    pcloud qcloud f t c (popReadout f t c)
    (canonicalRootedIntegrand (A := A) (B := B) (P := P) (a := a) (κ := κ)
      (lambda := lambda) α β coef probeFam Mst q f t)
    (hlln f t c) (hpop f t c)

/-- **The canonical Palm law from the population Palm LLN family.** -/
noncomputable def canonicalRootedTilePalmLaw_of_populationPalmLLNFamily
    (T : D.TaylorTiles ε) {A B : Set M}
    (pcloud qcloud : ∀ n, Fin (n + 1) → M)
    (base : ∀ n, Fin (n + 1) → T.Index → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (q : ℝ) (α β : Measure OTSelector.UnitMark)
    (coef : FinalProbeSpace A B → ℕ → (ℚ → M) → ℝ → ℝ → ℝ)
    (probeFam : FinalProbeSpace A B → ℕ → (ℚ → M) →
      MarkedCloudPoint → MarkedCloudPoint → ℝ)
    (Mst : FinalProbeSpace A B → ℝ → ℕ → (ℚ → M) →
      StationaryForwardMatching α β)
    (h : PopulationPalmLLNFamily (A := A) (B := B) T pcloud qcloud q α β coef
      probeFam Mst) :
    CanonicalRootedTilePalmLaw (A := A) (B := B) T pcloud qcloud base q
      α β coef probeFam Mst :=
  tilePalmSampleLawFamily_sceneCloud_of_LLNFamily (A := A) (B := B) T pcloud
    qcloud q α β coef probeFam Mst h.popReadout h.hlln h.hpop

/-! ## 3. The tile mean family from the Palm law family, pointwise -/

/-- **The population tile mean family from the Palm law family.**

The repo's chain TileMeanConvergence <- UniformTileAverageConvergence <-
PlanFreeTileMeanIdentification <- TilePalmSampleLaw is re-run pointwise in
(f,t,c).  At each point the root family is fixed to canonicalRootedIntegrand ...
f t, and the fixed-pair identification is the per-point application of
fixedPairMeanIdentification_of_palmSampleLaw with G := canonicalRootedIntegrand
... f t.  The uniform statements of the repo are never used, only their
pointwise content, so no (f,t)-uniformity beyond the given per-point side
conditions is needed. -/
theorem tileMeanConvergenceFamily_of_palmSampleLawFamily
    (T : D.TaylorTiles ε) {A B : Set M}
    (pcloud qcloud : ∀ n, Fin (n + 1) → M)
    (base : ∀ n, Fin (n + 1) → T.Index → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (q : ℝ) (α β : Measure OTSelector.UnitMark)
    (coef : FinalProbeSpace A B → ℕ → (ℚ → M) → ℝ → ℝ → ℝ)
    (probeFam : FinalProbeSpace A B → ℕ → (ℚ → M) →
      MarkedCloudPoint → MarkedCloudPoint → ℝ)
    (Mst : FinalProbeSpace A B → ℝ → ℕ → (ℚ → M) →
      StationaryForwardMatching α β)
    (hlaw : ∀ (f : FinalProbeSpace A B) (t : ℝ) (c : T.Index),
      T.TilePalmSampleLaw (ε := ε) f t sceneCloudSample (sceneCloudX pcloud)
        (sceneCloudY qcloud) tileScale c
        (fun _ ↦ T.tilePopValue (P := P) (a := a) (κ := κ) (lambda := lambda)
          (q := q) (canonicalRootedIntegrand (A := A) (B := B) (P := P) (a := a)
            (κ := κ) (lambda := lambda) α β coef probeFam Mst q f t) c))
    {Bp : ℝ} (hBp : 0 ≤ Bp)
    (hbase : ∀ (n : ℕ) (s : Fin (n + 1)) (c' : T.Index) (i j : Fin (n + 1)),
      |base n s c' i j| ≤ Bp)
    (hintC : ∀ (f : FinalProbeSpace A B) (t : ℝ) (n : ℕ) (c : T.Index),
      Integrable (T.tileLinearCostIntegrand (ε := ε) f t (sceneCloudX pcloud)
        (sceneCloudY qcloud) tileScale n c) (sceneCloudSample n))
    (hintP : ∀ (f : FinalProbeSpace A B) (t : ℝ) (n : ℕ) (c : T.Index),
      Integrable (T.tileLinearProbeIntegrand f t (sceneCloudX pcloud)
        (sceneCloudY qcloud)
        (fun f t n s c' ↦ normalizedProbe (K := A ∪ B) base t n s c') n c)
        (sceneCloudSample n))
    (hintClip : ∀ (f : FinalProbeSpace A B) (t : ℝ) (n : ℕ) (c : T.Index),
      Integrable (T.tileClippingIntegrand (ε := ε) f t (sceneCloudX pcloud)
        (sceneCloudY qcloud) tileScale
        (fun f t n s c' ↦ normalizedProbe (K := A ∪ B) base t n s c') n c)
        (sceneCloudSample n))
    (hclip : ∀ (f : FinalProbeSpace A B) (t : ℝ) (c : T.Index),
      Tendsto (fun n ↦ T.tileFixedPairClippingCorrection f t sceneCloudSample
        (sceneCloudX pcloud) (sceneCloudY qcloud) tileScale
        (fun f t n s c' ↦ normalizedProbe (K := A ∪ B) base t n s c') n c)
        atTop (𝓝 0))
    (hintEntry : ∀ (f : FinalProbeSpace A B) (t : ℝ) (n : ℕ) (c : T.Index)
      (i j : Fin (n + 1)),
      Integrable (fun s ↦ T.tileCostMatrix f t (sceneCloudX pcloud)
        (sceneCloudY qcloud) tileScale
        (fun f t n s c' ↦ normalizedProbe (K := A ∪ B) base t n s c') n c s i j)
        (sceneCloudSample n))
    (hExch : ∀ (f : FinalProbeSpace A B) (t : ℝ) (n : ℕ) (c : T.Index),
      MaskedEntryExchangeability (sceneCloudSample n)
        (T.tileCostMatrix f t (sceneCloudX pcloud) (sceneCloudY qcloud) tileScale
          (fun f t n s c' ↦ normalizedProbe (K := A ∪ B) base t n s c') n c))
    (hintCost : ∀ (f : FinalProbeSpace A B) (t : ℝ) (n : ℕ) (c : T.Index),
      Integrable (fun s ↦ ∑ i, ∑ j,
        T.tileCostMatrix f t (sceneCloudX pcloud) (sceneCloudY qcloud) tileScale
          (fun f t n s c' ↦ normalizedProbe (K := A ∪ B) base t n s c') n c s i j)
        (sceneCloudSample n))
    (hintRes : ∀ (f : FinalProbeSpace A B) (t : ℝ) (n : ℕ) (c : T.Index),
      Integrable (fun s ↦ ∑ i, ∑ j,
        (uniformTilePlan (fun n ↦ Fin (n + 1)) n s i j -
          1 / ((n + 1 : ℕ) : ℝ)) *
          T.tileCostMatrix f t (sceneCloudX pcloud) (sceneCloudY qcloud) tileScale
            (fun f t n s c' ↦ normalizedProbe (K := A ∪ B) base t n s c') n c s i j)
        (sceneCloudSample n))
    (hresv : T.TilePlanResidualVanishing (K := A ∪ B) sceneCloudSample
      (uniformTilePlan (fun n ↦ Fin (n + 1))) (sceneCloudX pcloud)
      (sceneCloudY qcloud) tileScale
      (fun f t n s c' ↦ normalizedProbe (K := A ∪ B) base t n s c')) :
    PopulationTileMeanFamily (A := A) (B := B) T pcloud qcloud base q α β coef
      probeFam Mst := by
  have huni : T.UniformTileAverageConvergence (K := A ∪ B)
      (fun (f : FinalProbeSpace A B) (t : ℝ) (c : T.Index) ↦
        T.tilePopValue (P := P) (a := a) (κ := κ) (lambda := lambda) (q := q)
          (canonicalRootedIntegrand (A := A) (B := B) (P := P) (a := a)
            (κ := κ) (lambda := lambda) α β coef probeFam Mst q f t) c)
      sceneCloudSample (sceneCloudX pcloud) (sceneCloudY qcloud) tileScale
      (fun f t n s c' ↦ normalizedProbe (K := A ∪ B) base t n s c') := by
    intro f t c
    have hid : PlanFreeTileMeanIdentification
        (fun n ↦ T.tileFixedPair f t sceneCloudSample (sceneCloudX pcloud)
          (sceneCloudY qcloud) tileScale
          (fun f t n s c' ↦ normalizedProbe (K := A ∪ B) base t n s c') n c)
        (fun _ ↦ T.tilePopValue (P := P) (a := a) (κ := κ) (lambda := lambda)
          (q := q) (canonicalRootedIntegrand (A := A) (B := B) (P := P) (a := a)
            (κ := κ) (lambda := lambda) α β coef probeFam Mst q f t) c) :=
      T.fixedPairMeanIdentification_of_palmSampleLaw (K := A ∪ B)
        sceneCloudSample f t (sceneCloudX pcloud) (sceneCloudY qcloud) c
        tileScale base
        hBp hbase (fun n ↦ hintC f t n c) (fun n ↦ hintP f t n c)
        (fun n ↦ hintClip f t n c)
        (canonicalRootedIntegrand (A := A) (B := B) (P := P) (a := a)
          (κ := κ) (lambda := lambda) α β coef probeFam Mst q f t)
        (hlaw f t c) (hclip f t c)
    have hmean : ∀ n, (1 / ((n + 1 : ℕ) : ℝ)) *
        ((1 / ((n + 1 : ℕ) : ℝ)) *
          T.uniformTilePart f t sceneCloudSample (sceneCloudX pcloud)
            (sceneCloudY qcloud) tileScale
            (fun f t n s c' ↦ normalizedProbe (K := A ∪ B) base t n s c') n c) =
        T.tileFixedPair f t sceneCloudSample (sceneCloudX pcloud)
          (sceneCloudY qcloud) tileScale
          (fun f t n s c' ↦ normalizedProbe (K := A ∪ B) base t n s c') n c :=
      fun n ↦ T.uniformTilePart_eq_fixedPair sceneCloudSample f t
        (sceneCloudX pcloud) (sceneCloudY qcloud) tileScale
        (fun f t n s c' ↦ normalizedProbe (K := A ∪ B) base t n s c') n c
        (hintEntry f t n c) (hExch f t n c)
    have hpp := planFreeTileLLN_of_fixedPairIdentification
      (fun n ↦ (1 / ((n + 1 : ℕ) : ℝ)) *
        ((1 / ((n + 1 : ℕ) : ℝ)) *
          T.uniformTilePart f t sceneCloudSample (sceneCloudX pcloud)
            (sceneCloudY qcloud) tileScale
            (fun f t n s c' ↦ normalizedProbe (K := A ∪ B) base t n s c') n c))
      (fun n ↦ T.tileFixedPair f t sceneCloudSample (sceneCloudX pcloud)
        (sceneCloudY qcloud) tileScale
        (fun f t n s c' ↦ normalizedProbe (K := A ∪ B) base t n s c') n c)
      (fun _ ↦ T.tilePopValue (P := P) (a := a) (κ := κ) (lambda := lambda)
        (q := q) (canonicalRootedIntegrand (A := A) (B := B) (P := P) (a := a)
          (κ := κ) (lambda := lambda) α β coef probeFam Mst q f t) c)
      hmean hid
    have hadd := hpp.add (tendsto_const_nhds :
      Tendsto (fun _ : ℕ ↦ T.tilePopValue (P := P) (a := a) (κ := κ)
        (lambda := lambda) (q := q)
        (canonicalRootedIntegrand (A := A) (B := B) (P := P) (a := a)
          (κ := κ) (lambda := lambda) α β coef probeFam Mst q f t) c) atTop
        (𝓝 (T.tilePopValue (P := P) (a := a) (κ := κ) (lambda := lambda)
          (q := q) (canonicalRootedIntegrand (A := A) (B := B) (P := P) (a := a)
            (κ := κ) (lambda := lambda) α β coef probeFam Mst q f t) c)))
    simpa [sub_add_cancel, zero_add] using hadd
  have hconv := T.tendsto_tileEmpiricalMean_of_uniform_and_residual
    (K := A ∪ B) sceneCloudSample (sceneCloudX pcloud) (sceneCloudY qcloud)
    tileScale (fun f t n s c' ↦ normalizedProbe (K := A ∪ B) base t n s c')
    (uniformTilePlan (fun n ↦ Fin (n + 1)))
    (fun (f : FinalProbeSpace A B) (t : ℝ) (c : T.Index) ↦
      T.tilePopValue (P := P) (a := a) (κ := κ) (lambda := lambda) (q := q)
        (canonicalRootedIntegrand (A := A) (B := B) (P := P) (a := a)
          (κ := κ) (lambda := lambda) α β coef probeFam Mst q f t) c)
    hintCost hintRes huni hresv
  exact fun f t c ↦ (hconv f t c).congr' (Eventually.of_forall fun n ↦
    tileEmpiricalMeanProb_eq_integral_tileValue (T := T) f t sceneCloudSample
      (sceneCloudX pcloud) (sceneCloudY qcloud) tileScale
      (fun f t n s c' ↦ normalizedProbe (K := A ∪ B) base t n s c')
      (uniformTilePlan (fun n ↦ Fin (n + 1))) n c)

/-! ## 4. The canonical Palm LLN from the tile mean family -/

/-- **The canonical Palm LLN from the population tile mean family.**

The population tile mean family is exactly the canonical TileMeanConvergence, so
the generic-population chain of the repo
(rootedTileSingleConvergenceInProbability_of_tileMeanConvergence,
rootedTileSingleConvergence_of_inProbability, rootedTileMeanConvergence_of_single)
produces the canonical Palm LLN. -/
theorem canonicalRootedTileMeanLaw_of_populationTileMeanFamily
    (T : D.TaylorTiles ε) {A B : Set M}
    (pcloud qcloud : ∀ n, Fin (n + 1) → M)
    (base : ∀ n, Fin (n + 1) → T.Index → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (q : ℝ) (α β : Measure OTSelector.UnitMark)
    (coef : FinalProbeSpace A B → ℕ → (ℚ → M) → ℝ → ℝ → ℝ)
    (probeFam : FinalProbeSpace A B → ℕ → (ℚ → M) →
      MarkedCloudPoint → MarkedCloudPoint → ℝ)
    (Mst : FinalProbeSpace A B → ℝ → ℕ → (ℚ → M) →
      StationaryForwardMatching α β)
    (hmean : PopulationTileMeanFamily (A := A) (B := B) T pcloud qcloud base q
      α β coef probeFam Mst) :
    CanonicalRootedTileMeanLaw (A := A) (B := B) T pcloud qcloud base q
      α β coef probeFam Mst :=
  T.rootedTileMeanConvergence_of_single (K := A ∪ B)
    (fun (f : FinalProbeSpace A B) (t : ℝ) (c : T.Index) ↦
      T.tilePopValue (P := P) (a := a) (κ := κ) (lambda := lambda) (q := q)
        (canonicalRootedIntegrand (A := A) (B := B) (P := P) (a := a)
          (κ := κ) (lambda := lambda) α β coef probeFam Mst q f t) c)
    sceneCloudSample (sceneCloudX pcloud) (sceneCloudY qcloud) tileScale
    (fun f t n s c' ↦ normalizedProbe (K := A ∪ B) base t n s c')
    (uniformTilePlan (fun n ↦ Fin (n + 1)))
    (T.rootedTileSingleConvergence_of_inProbability (K := A ∪ B)
      (fun (f : FinalProbeSpace A B) (t : ℝ) (c : T.Index) ↦
        T.tilePopValue (P := P) (a := a) (κ := κ) (lambda := lambda) (q := q)
          (canonicalRootedIntegrand (A := A) (B := B) (P := P) (a := a)
            (κ := κ) (lambda := lambda) α β coef probeFam Mst q f t) c)
      sceneCloudSample (sceneCloudX pcloud) (sceneCloudY qcloud) tileScale
      (fun f t n s c' ↦ normalizedProbe (K := A ∪ B) base t n s c')
      (uniformTilePlan (fun n ↦ Fin (n + 1)))
      (T.rootedTileSingleConvergenceInProbability_of_tileMeanConvergence
        (K := A ∪ B)
        (fun (f : FinalProbeSpace A B) (t : ℝ) (c : T.Index) ↦
          T.tilePopValue (P := P) (a := a) (κ := κ) (lambda := lambda) (q := q)
            (canonicalRootedIntegrand (A := A) (B := B) (P := P) (a := a)
              (κ := κ) (lambda := lambda) α β coef probeFam Mst q f t) c)
        sceneCloudSample (sceneCloudX pcloud) (sceneCloudY qcloud) tileScale
        (fun f t n s c' ↦ normalizedProbe (K := A ∪ B) base t n s c')
        (uniformTilePlan (fun n ↦ Fin (n + 1))) hmean))

/-! ## 5. The lane hId from the population families -/

/-- **The lane hId from the population families and the covering family.**

Minimal remaining input list: the population covering family at the canonical
family, the population Palm LLN family (V7 hlln + hpop read per probe and tilt),
the analytic lane side conditions, and the geometric lane data.  No atlas root
family Groot and no gluing binder hgt occurs; the Palm law and tile mean
families are produced from the V7 data by the pointwise transfers above, and the
frozen-cost integrability is discharged by integrable_sceneCloudSample. -/
theorem frozenCampbellMeanIdentification_sceneCloud_of_canonicalPopulationInputsFamily
    (T : D.TaylorTiles ε) {A B : Set M}
    (pcloud qcloud : ∀ n, Fin (n + 1) → M)
    (base : ∀ n, Fin (n + 1) → T.Index → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (q : ℝ) (α β : Measure OTSelector.UnitMark)
    (coef : FinalProbeSpace A B → ℕ → (ℚ → M) → ℝ → ℝ → ℝ)
    (probeFam : FinalProbeSpace A B → ℕ → (ℚ → M) →
      MarkedCloudPoint → MarkedCloudPoint → ℝ)
    (Mst : FinalProbeSpace A B → ℝ → ℕ → (ℚ → M) →
      StationaryForwardMatching α β)
    (hcover : ∀ (f : FinalProbeSpace A B) (t : ℝ),
      PopulationAtlasCovering (P := P) (a := a) (κ := κ) (lambda := lambda)
        T q (canonicalRootedIntegrand (A := A) (B := B) (P := P) (a := a)
          (κ := κ) (lambda := lambda) α β coef probeFam Mst q f t))
    (hPalmFam : PopulationPalmLLNFamily (A := A) (B := B) T pcloud qcloud q
      α β coef probeFam Mst)
    {Bp : ℝ} (hBp : 0 ≤ Bp)
    (hbase : ∀ (n : ℕ) (s : Fin (n + 1)) (c' : T.Index) (i j : Fin (n + 1)),
      |base n s c' i j| ≤ Bp)
    (hintC : ∀ (f : FinalProbeSpace A B) (t : ℝ) (n : ℕ) (c : T.Index),
      Integrable (T.tileLinearCostIntegrand (ε := ε) f t (sceneCloudX pcloud)
        (sceneCloudY qcloud) tileScale n c) (sceneCloudSample n))
    (hintP : ∀ (f : FinalProbeSpace A B) (t : ℝ) (n : ℕ) (c : T.Index),
      Integrable (T.tileLinearProbeIntegrand f t (sceneCloudX pcloud)
        (sceneCloudY qcloud)
        (fun f t n s c' ↦ normalizedProbe (K := A ∪ B) base t n s c') n c)
        (sceneCloudSample n))
    (hintClip : ∀ (f : FinalProbeSpace A B) (t : ℝ) (n : ℕ) (c : T.Index),
      Integrable (T.tileClippingIntegrand (ε := ε) f t (sceneCloudX pcloud)
        (sceneCloudY qcloud) tileScale
        (fun f t n s c' ↦ normalizedProbe (K := A ∪ B) base t n s c') n c)
        (sceneCloudSample n))
    (hclip : ∀ (f : FinalProbeSpace A B) (t : ℝ) (c : T.Index),
      Tendsto (fun n ↦ T.tileFixedPairClippingCorrection f t sceneCloudSample
        (sceneCloudX pcloud) (sceneCloudY qcloud) tileScale
        (fun f t n s c' ↦ normalizedProbe (K := A ∪ B) base t n s c') n c)
        atTop (𝓝 0))
    (hintEntry : ∀ (f : FinalProbeSpace A B) (t : ℝ) (n : ℕ) (c : T.Index)
      (i j : Fin (n + 1)),
      Integrable (fun s ↦ T.tileCostMatrix f t (sceneCloudX pcloud)
        (sceneCloudY qcloud) tileScale
        (fun f t n s c' ↦ normalizedProbe (K := A ∪ B) base t n s c') n c s i j)
        (sceneCloudSample n))
    (hExch : ∀ (f : FinalProbeSpace A B) (t : ℝ) (n : ℕ) (c : T.Index),
      MaskedEntryExchangeability (sceneCloudSample n)
        (T.tileCostMatrix f t (sceneCloudX pcloud) (sceneCloudY qcloud) tileScale
          (fun f t n s c' ↦ normalizedProbe (K := A ∪ B) base t n s c') n c))
    (hintCost : ∀ (f : FinalProbeSpace A B) (t : ℝ) (n : ℕ) (c : T.Index),
      Integrable (fun s ↦ ∑ i, ∑ j,
        T.tileCostMatrix f t (sceneCloudX pcloud) (sceneCloudY qcloud) tileScale
          (fun f t n s c' ↦ normalizedProbe (K := A ∪ B) base t n s c') n c s i j)
        (sceneCloudSample n))
    (hintRes : ∀ (f : FinalProbeSpace A B) (t : ℝ) (n : ℕ) (c : T.Index),
      Integrable (fun s ↦ ∑ i, ∑ j,
        (uniformTilePlan (fun n ↦ Fin (n + 1)) n s i j -
          1 / ((n + 1 : ℕ) : ℝ)) *
          T.tileCostMatrix f t (sceneCloudX pcloud) (sceneCloudY qcloud) tileScale
            (fun f t n s c' ↦ normalizedProbe (K := A ∪ B) base t n s c') n c s i j)
        (sceneCloudSample n))
    (hresv : T.TilePlanResidualVanishing (K := A ∪ B) sceneCloudSample
      (uniformTilePlan (fun n ↦ Fin (n + 1))) (sceneCloudX pcloud)
      (sceneCloudY qcloud) tileScale
      (fun f t n s c' ↦ normalizedProbe (K := A ∪ B) base t n s c'))
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _instPalmLLNPerProbeTiltMetric : MetricSpace M := F.metricSpace;
      LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val))) :
    RootedTileCampbellMeanIdentification (K := A ∪ B) P a κ lambda
      (frozenRootedCostReadout (F := F) (u := u) (Seed := P) (a := a)
        (κ := κ) (lambda := lambda) (Z := ℚ → M) (A := A) (B := B)
        α β coef probeFam Mst q) q sceneCloudSample
      (hprobFrozenCostFamily (K := A ∪ B) (T := T) (sceneCloudX pcloud)
        (sceneCloudY qcloud) base (uniformTilePlan (fun n ↦ Fin (n + 1)))
        tileScale) T.Index :=
  frozenCampbellMeanIdentification_sceneCloud_of_canonicalRootedIntegrand
    (A := A) (B := B) T pcloud qcloud base q α β coef probeFam Mst
    (canonicalRootedCovering_of_populationAtlasCovering (A := A) (B := B) T q
      α β coef probeFam Mst hcover)
    (canonicalRootedTileMeanLaw_of_populationTileMeanFamily (A := A) (B := B) T
      pcloud qcloud base q α β coef probeFam Mst
      (tileMeanConvergenceFamily_of_palmSampleLawFamily (A := A) (B := B) T
        pcloud qcloud base q α β coef probeFam Mst
        (tilePalmSampleLawFamily_sceneCloud_of_LLNFamily (A := A) (B := B) T
          pcloud qcloud q α β coef probeFam Mst hPalmFam.popReadout
          hPalmFam.hlln hPalmFam.hpop)
        hBp hbase hintC hintP hintClip hclip hintEntry hExch hintCost hintRes
        hresv))
    hF hcomplete hu ha hinj

end OTSelector.Reconstruction
