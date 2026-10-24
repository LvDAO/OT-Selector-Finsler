import OTSelector.Reconstruction.FinslerOriginalPlanFreeLLNReduction
import OTSelector.Reconstruction.FinslerOriginalPalmLLNAnalyticSideConditions
import OTSelector.Reconstruction.FinslerOriginalTileIntegralSplit
import OTSelector.Reconstruction.FinslerOriginalLinearPalmIdentification

/-!
# The fixed-pair identification: linear Palm part plus clipping correction

This module discharges the fixed-pair identification residue of the lower lane,
PlanFreeTileMeanIdentification (tileFixedPair ...) (fun _ => tilePopValue ... G c),
using the repo split FinslerOriginalTileIntegralSplit.

## 1. The exact split statement

The fixed-pair masked expectation splits exactly (theorem
tileFixedPair_eq_linear_add_clipping, FinslerOriginalTileIntegralSplit) into

  T.tileFixedPair f t sample X Y scale hprobe n c =
    T.tileFixedPairLinearPart f t sample X Y scale hprobe n c
    + T.tileFixedPairClippingCorrection f t sample X Y scale hprobe n c,

where tileFixedPairLinearPart is the integral of the masked linear term
(1 - 2 eps) * scale * frozenPhysicalCost + t * probe at the distinguished pair and
tileFixedPairClippingCorrection is the integral of the clipped negative part
max (-linearTerm) 0, provided the linear and clipping integrands are integrable.

## 2. Clipping vanishing and the linear Palm reduction

* The clipping correction vanishes on the scene-cloud lane by
  tileFixedPairClippingCorrection_sceneCloud_tendsto_zero
  (FinslerOriginalPalmLLNAnalyticSideConditions), itself from the repo retained-edge
  clipping lemma and the decay of the normalized probe; it is reused here.

* The linear Palm identification reduces to the frozen-cost Palm identification:
  the repo theorem tileLinearPalmIdentification_of_costPalm
  (FinslerOriginalLinearPalmIdentification) splits the linear part into the cost
  integral and the probe integral (tileFixedPairLinearPart_eq_cost_add_probe) and
  proves the probe contribution vanishes (tileLinearProbePart_tendsto_zero).  Hence
  the sharpest single remaining convergence is

  TileCostPalmIdentification (fun n => integral of tileLinearCostIntegrand at scale
    tileScale) (fun _ => tilePopValue ... G c),

  i.e. Tendsto (fun n => the cost integral minus tilePopValue) atTop (neighborhood 0).

## 3. Instantiation

lowerLaneRootedTileMeanLaw_of_costPalm instantiates LowerLaneRootedTileMeanLaw
(FinslerOriginalTileCampbellMeanFromPalm) from that single cost Palm identification
plus the existing analytic lane fields (exchangeability, integrabilities, plan
residual vanishing, probe base bound, retained-edge window facts).

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

/-! ## 1. The split at the scene-cloud instance -/

/-- **Fixed-pair identification from the linear Palm part and clipping vanishing.**
The exact integral split of the fixed-pair masked expectation
(tileFixedPair_eq_linear_add_clipping) with the linear Palm identification and the
vanishing of the clipping correction gives the fixed-pair identification. -/
theorem planFreeTileMeanIdentification_sceneCloud_of_linearPalm
    (T : D.TaylorTiles ε) {A B : Set M}
    (pcloud qcloud : ∀ n, Fin (n + 1) → M)
    (base : ∀ n, Fin (n + 1) → T.Index → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (G : ℕ → (ℚ → M) → ℝ)
    (f : (↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) (t : ℝ) (c : T.Index)
    (hintLin : ∀ (n : ℕ), Integrable (T.tileLinearIntegrand (ε := ε) f t
      (sceneCloudX pcloud) (sceneCloudY qcloud) tileScale
      (fun f t n s c' ↦ normalizedProbe (K := A ∪ B) base t n s c') n c)
      (sceneCloudSample n))
    (hintClip : ∀ (n : ℕ), Integrable (T.tileClippingIntegrand (ε := ε) f t
      (sceneCloudX pcloud) (sceneCloudY qcloud) tileScale
      (fun f t n s c' ↦ normalizedProbe (K := A ∪ B) base t n s c') n c)
      (sceneCloudSample n))
    (hlin : PlanFreeTileMeanIdentification
      (fun n ↦ T.tileFixedPairLinearPart f t sceneCloudSample (sceneCloudX pcloud)
        (sceneCloudY qcloud) tileScale
        (fun f t n s c' ↦ normalizedProbe (K := A ∪ B) base t n s c') n c)
      (fun _ ↦ T.tilePopValue (P := P) (a := a) (κ := κ) (lambda := lambda) (q := q) G c))
    (hclip : Tendsto (fun n ↦ T.tileFixedPairClippingCorrection f t sceneCloudSample
      (sceneCloudX pcloud) (sceneCloudY qcloud) tileScale
      (fun f t n s c' ↦ normalizedProbe (K := A ∪ B) base t n s c') n c) atTop (𝓝 0)) :
    PlanFreeTileMeanIdentification
      (fun n ↦ T.tileFixedPair f t sceneCloudSample (sceneCloudX pcloud)
        (sceneCloudY qcloud) tileScale
        (fun f t n s c' ↦ normalizedProbe (K := A ∪ B) base t n s c') n c)
      (fun _ ↦ T.tilePopValue (P := P) (a := a) (κ := κ) (lambda := lambda) (q := q) G c) :=
  planFreeTileMeanIdentification_of_tileSplit
    (fun n ↦ T.tileFixedPair f t sceneCloudSample (sceneCloudX pcloud)
      (sceneCloudY qcloud) tileScale
      (fun f t n s c' ↦ normalizedProbe (K := A ∪ B) base t n s c') n c)
    (fun n ↦ T.tileFixedPairLinearPart f t sceneCloudSample (sceneCloudX pcloud)
      (sceneCloudY qcloud) tileScale
      (fun f t n s c' ↦ normalizedProbe (K := A ∪ B) base t n s c') n c)
    (fun n ↦ T.tileFixedPairClippingCorrection f t sceneCloudSample (sceneCloudX pcloud)
      (sceneCloudY qcloud) tileScale
      (fun f t n s c' ↦ normalizedProbe (K := A ∪ B) base t n s c') n c)
    (fun _ ↦ T.tilePopValue (P := P) (a := a) (κ := κ) (lambda := lambda) (q := q) G c)
    (fun n ↦ tileFixedPair_eq_linear_add_clipping (T := T) sceneCloudSample f t
      (sceneCloudX pcloud) (sceneCloudY qcloud) tileScale
      (fun f t n s c' ↦ normalizedProbe (K := A ∪ B) base t n s c') n c
      (hintLin n) (hintClip n))
    hlin hclip

/-! ## 2. The sharpest single convergence: the frozen-cost Palm identification -/

/-- **Fixed-pair identification from the frozen-cost Palm identification.**  The
linear Palm part is split into the frozen-cost integral and the probe integral; the
probe contribution vanishes (repo tileLinearProbePart_tendsto_zero), so the linear
Palm identification follows from the cost identification
tileLinearPalmIdentification_of_costPalm; the clipping correction vanishes on the
scene-cloud lane (repo retained-edge clipping lemma).  Hence the only remaining
convergence is the frozen-cost Palm identification. -/
theorem planFreeTileMeanIdentification_sceneCloud_of_costPalm
    (T : D.TaylorTiles ε) {A B : Set M}
    (pcloud qcloud : ∀ n, Fin (n + 1) → M)
    (base : ∀ n, Fin (n + 1) → T.Index → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (G : ℕ → (ℚ → M) → ℝ)
    (f : (↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) (t : ℝ) (c : T.Index)
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
    (hcost : Tendsto (fun n ↦ ∫ s, T.tileLinearCostIntegrand (ε := ε) f t
        (sceneCloudX pcloud) (sceneCloudY qcloud) tileScale n c s ∂sceneCloudSample n -
        T.tilePopValue (P := P) (a := a) (κ := κ) (lambda := lambda) (q := q) G c)
      atTop (𝓝 0)) :
    PlanFreeTileMeanIdentification
      (fun n ↦ T.tileFixedPair f t sceneCloudSample (sceneCloudX pcloud)
        (sceneCloudY qcloud) tileScale
        (fun f t n s c' ↦ normalizedProbe (K := A ∪ B) base t n s c') n c)
      (fun _ ↦ T.tilePopValue (P := P) (a := a) (κ := κ) (lambda := lambda) (q := q) G c) :=
  planFreeTileMeanIdentification_sceneCloud_of_linearPalm (T := T) (A := A) (B := B)
    pcloud qcloud base G f t c (fun n ↦ hintLin f t n c) (fun n ↦ hintClip f t n c)
    (tileLinearPalmIdentification_of_costPalm (K := A ∪ B) (T := T) (ε := ε)
      sceneCloudSample f t (sceneCloudX pcloud) (sceneCloudY qcloud) c base hBp hbase
      (fun n ↦ hintC f t n c) (fun n ↦ hintP f t n c) G hcost)
    (tileFixedPairClippingCorrection_sceneCloud_tendsto_zero (T := T) (A := A) (B := B)
      pcloud qcloud base hBp hbase hintClip hε hz₀ hp f t c)


/-! ## 3. The Palm tile mean law from the frozen-cost Palm identification -/

/-- **LowerLaneRootedTileMeanLaw from the frozen-cost Palm identification.**  The
fixed-pair identification is derived from the exact integral split, the vanishing of
the clipping correction (repo retained-edge clipping lemma) and the linear Palm
identification, which is in turn reduced to the frozen-cost Palm identification (the
probe contribution vanishes).  Combined with the plan-free reduction
(lowerLaneRootedTileMeanLaw_of_fixedPairIdentification), the Palm tile mean law of
the lower lane follows from the single convergence hcost plus the existing analytic
lane fields. -/
theorem lowerLaneRootedTileMeanLaw_of_costPalm
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
    (hcost : ∀ (f : (↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) (t : ℝ) (c : T.Index),
      Tendsto (fun n ↦ ∫ s, T.tileLinearCostIntegrand (ε := ε) f t
        (sceneCloudX pcloud) (sceneCloudY qcloud) tileScale n c s ∂sceneCloudSample n -
        T.tilePopValue (P := P) (a := a) (κ := κ) (lambda := lambda) (q := q) G c)
        atTop (𝓝 0)) :
    LowerLaneRootedTileMeanLaw (P := P) (a := a) (κ := κ) (lambda := lambda) (q := q)
      T (A := A) (B := B) pcloud qcloud base G :=
  lowerLaneRootedTileMeanLaw_of_fixedPairIdentification (T := T) (A := A) (B := B)
    pcloud qcloud base G hintEntry hExch
    (fun f t c ↦
      planFreeTileMeanIdentification_sceneCloud_of_costPalm (T := T) (A := A) (B := B)
        pcloud qcloud base G f t c hBp hbase hintC hintP hintLin hintClip hε hz₀ hp
        (hcost f t c))
    hintCost hintRes hresv
