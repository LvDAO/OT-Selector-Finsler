import OTSelector.Reconstruction.FinslerOriginalPalmLLNPerProbeTilt
import OTSelector.Reconstruction.FinslerOriginalPalmSampleLawProof
import OTSelector.Reconstruction.FinslerOriginalPalmReadoutFromLaneProducer

/-!
# The canonical Palm law from a SINGLE family reading

FinslerOriginalPalmLLNPerProbeTilt proved the canonical Palm law and the canonical
Palm LLN from the (f,t,c)-indexed population families, with the two V7 fields
hlln and hpop read per (f,t,c) as bare Tendsto statements.  The question left
open there was whether the papers' SINGLE family input can be stated directly,
with no (f,t)-uniformity anywhere.  This module answers it affirmatively.

## The single family input

The papers state the two probabilistic inputs as conditions on one population
readout function of (f,t,c,n):

* the empirical Palm LLN: for every (f,t,c), the scene-cloud average against
  popReadout f t c converges to zero (PalmReadoutIdentification);
* the population bias identity: for every (f,t,c), the normalized population
  readout converges to the tile Campbell value of the canonical root family
  rootedFrozenIntegrand ... f t (PalmPopulationReadoutIdentification).

Both are stated pointwise in (f,t): they are properties of the single function
popReadout and of the single canonical family function
fun f t => canonicalRootedIntegrand ... f t.  There is no quantifier over a
uniform (f,t)-family of independent inputs, no interchange of limits, and no
compactness or continuity requirement in (f,t).

## Producer pointwise

The repo producer tilePalmSampleLaw_sceneCloud_of_LLN is already pointwise: its
arguments f t c popReadout G and its two hypothesis hLLN hBias refer to one point
(f,t,c) only (the root family G is an arbitrary single family).  Therefore
canonicalRootedTilePalmLaw_of_singleFamilyReading is a pure reindexing: apply the
producer at each (f,t,c) with G := canonicalRootedIntegrand ... f t.  No
uniformity is lost or needed.

## Residuals

The canonical lane residual list is: the single family reading (popReadout +
hLLN + hBias), the analytic lane side conditions (hBp/hbase, hintC/hintP/
hintClip, hclip, hintEntry, hExch, hintCost/hintRes, hresv), the population
covering family, and the geometric lane data hF/hcomplete/hu/ha/hinj.  No Groot
and no hgt occurs.

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

/-! ## 1. The single family reading -/

/-- **The papers' single family input.**

One population readout function of (f,t,c,n) together with the two pointwise
probabilistic conditions: the empirical Palm LLN and the population bias
identity, each stated at every (f,t,c) against the canonical root family of the
SAME probe and tilt.  No (f,t)-uniformity is part of this input. -/
structure SinglePalmFamilyReading (T : D.TaylorTiles ε) {A B : Set M}
    (pcloud qcloud : ∀ n, Fin (n + 1) → M)
    (q : ℝ) (α β : Measure OTSelector.UnitMark)
    (coef : FinalProbeSpace A B → ℕ → (ℚ → M) → ℝ → ℝ → ℝ)
    (probeFam : FinalProbeSpace A B → ℕ → (ℚ → M) →
      MarkedCloudPoint → MarkedCloudPoint → ℝ)
    (Mst : FinalProbeSpace A B → ℝ → ℕ → (ℚ → M) →
      StationaryForwardMatching α β) : Type _ where
  popReadout : FinalProbeSpace A B → ℝ → T.Index → ℕ → ℝ
  hLLN : ∀ (f : FinalProbeSpace A B) (t : ℝ) (c : T.Index),
    PalmReadoutIdentification (T := T) pcloud qcloud c (popReadout f t c)
  hBias : ∀ (f : FinalProbeSpace A B) (t : ℝ) (c : T.Index),
    PalmPopulationReadoutIdentification (T := T)
      (G := canonicalRootedIntegrand (A := A) (B := B) (P := P) (a := a)
        (κ := κ) (lambda := lambda) α β coef probeFam Mst q f t)
      (c := c) (popReadout := popReadout f t c) (q := q) (P := P) (a := a)
      (κ := κ) (lambda := lambda) (ε := ε)

/-! ## 2. The Palm law from the single family, pointwise -/

/-- **The tile Palm sample law family is the producer applied pointwise.**

The repo producer tilePalmSampleLaw_sceneCloud_of_LLN is already pointwise in
(f,t,c); this family function is exactly its per-point application with the
canonical root family of each point.  No (f,t)-uniformity is introduced. -/
noncomputable def tilePalmSampleLawFamily_of_singleFamilyReading
    (T : D.TaylorTiles ε) {A B : Set M}
    (pcloud qcloud : ∀ n, Fin (n + 1) → M)
    (q : ℝ) (α β : Measure OTSelector.UnitMark)
    (coef : FinalProbeSpace A B → ℕ → (ℚ → M) → ℝ → ℝ → ℝ)
    (probeFam : FinalProbeSpace A B → ℕ → (ℚ → M) →
      MarkedCloudPoint → MarkedCloudPoint → ℝ)
    (Mst : FinalProbeSpace A B → ℝ → ℕ → (ℚ → M) →
      StationaryForwardMatching α β)
    (h : SinglePalmFamilyReading (A := A) (B := B) T pcloud qcloud q α β coef
      probeFam Mst) :
    ∀ (f : FinalProbeSpace A B) (t : ℝ) (c : T.Index),
      T.TilePalmSampleLaw (ε := ε) f t sceneCloudSample (sceneCloudX pcloud)
        (sceneCloudY qcloud) tileScale c
        (fun _ ↦ T.tilePopValue (P := P) (a := a) (κ := κ) (lambda := lambda)
          (q := q) (canonicalRootedIntegrand (A := A) (B := B) (P := P) (a := a)
            (κ := κ) (lambda := lambda) α β coef probeFam Mst q f t) c) :=
  fun f t c ↦ tilePalmSampleLaw_sceneCloud_of_LLN (T := T) (A := A) (B := B)
    pcloud qcloud f t c (h.popReadout f t c)
    (canonicalRootedIntegrand (A := A) (B := B) (P := P) (a := a) (κ := κ)
      (lambda := lambda) α β coef probeFam Mst q f t)
    (h.hLLN f t c) (h.hBias f t c)

/-- **The canonical Palm law from the single family reading.**

Pure reindexing: CanonicalRootedTilePalmLaw is definitionally the (f,t,c)-indexed
TilePalmSampleLaw family, and tilePalmSampleLawFamily_of_singleFamilyReading is
that family obtained by the pointwise producer. -/
noncomputable def canonicalRootedTilePalmLaw_of_singleFamilyReading
    (T : D.TaylorTiles ε) {A B : Set M}
    (pcloud qcloud : ∀ n, Fin (n + 1) → M)
    (base : ∀ n, Fin (n + 1) → T.Index → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (q : ℝ) (α β : Measure OTSelector.UnitMark)
    (coef : FinalProbeSpace A B → ℕ → (ℚ → M) → ℝ → ℝ → ℝ)
    (probeFam : FinalProbeSpace A B → ℕ → (ℚ → M) →
      MarkedCloudPoint → MarkedCloudPoint → ℝ)
    (Mst : FinalProbeSpace A B → ℝ → ℕ → (ℚ → M) →
      StationaryForwardMatching α β)
    (h : SinglePalmFamilyReading (A := A) (B := B) T pcloud qcloud q α β coef
      probeFam Mst) :
    CanonicalRootedTilePalmLaw (A := A) (B := B) T pcloud qcloud base q
      α β coef probeFam Mst :=
  tilePalmSampleLawFamily_of_singleFamilyReading (A := A) (B := B) T pcloud
    qcloud q α β coef probeFam Mst h

/-! ## 3. The mean law from the single family, pointwise -/

/-- **The canonical Palm LLN from the single family reading.**

The single family reading yields the per-point Palm sample laws; the pointwise
chain of FinslerOriginalPalmLLNPerProbeTilt (with the same analytic lane side
conditions, which are already (f,t,c)-indexed) then yields the canonical mean
law.  No (f,t)-uniformity occurs at any step. -/
theorem canonicalRootedTileMeanLaw_of_singleFamilyReading
    (T : D.TaylorTiles ε) {A B : Set M}
    (pcloud qcloud : ∀ n, Fin (n + 1) → M)
    (base : ∀ n, Fin (n + 1) → T.Index → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (q : ℝ) (α β : Measure OTSelector.UnitMark)
    (coef : FinalProbeSpace A B → ℕ → (ℚ → M) → ℝ → ℝ → ℝ)
    (probeFam : FinalProbeSpace A B → ℕ → (ℚ → M) →
      MarkedCloudPoint → MarkedCloudPoint → ℝ)
    (Mst : FinalProbeSpace A B → ℝ → ℕ → (ℚ → M) →
      StationaryForwardMatching α β)
    (h : SinglePalmFamilyReading (A := A) (B := B) T pcloud qcloud q α β coef
      probeFam Mst)
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
    CanonicalRootedTileMeanLaw (A := A) (B := B) T pcloud qcloud base q
      α β coef probeFam Mst :=
  canonicalRootedTileMeanLaw_of_populationTileMeanFamily (A := A) (B := B) T
    pcloud qcloud base q α β coef probeFam Mst
    (tileMeanConvergenceFamily_of_palmSampleLawFamily (A := A) (B := B) T
      pcloud qcloud base q α β coef probeFam Mst
      (tilePalmSampleLawFamily_of_singleFamilyReading (A := A) (B := B) T
        pcloud qcloud q α β coef probeFam Mst h)
      hBp hbase hintC hintP hintClip hclip hintEntry hExch hintCost hintRes hresv)

/-! ## 4. The lane hId from the single family reading -/

/-- **The lane hId from the single family input.**

Minimal binder list: the population covering family at the canonical family, the
single family reading (one popReadout + the pointwise hLLN and hBias), the
analytic lane side conditions, and the geometric lane data.  The Palm law and
the canonical mean law are produced by the pointwise transfers above; the
frozen-cost integrability is discharged by the scene-cloud readout, so no atlas
root family Groot and no gluing binder hgt occurs. -/
theorem frozenCampbellMeanIdentification_sceneCloud_of_singleFamilyInputs
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
    (h : SinglePalmFamilyReading (A := A) (B := B) T pcloud qcloud q α β coef
      probeFam Mst)
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
    (hu : let _instSingleFamilyMetric : MetricSpace M := F.metricSpace;
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
    (canonicalRootedTileMeanLaw_of_singleFamilyReading (A := A) (B := B) T
      pcloud qcloud base q α β coef probeFam Mst h hBp hbase hintC hintP
      hintClip hclip hintEntry hExch hintCost hintRes hresv)
    hF hcomplete hu ha hinj

end OTSelector.Reconstruction
