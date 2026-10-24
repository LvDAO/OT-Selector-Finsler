import OTSelector.Reconstruction.FinslerOriginalCostPalmFromFrozenFamily
import OTSelector.Reconstruction.FinslerOriginalCloudReadoutConvergence
import OTSelector.Reconstruction.FinslerOriginalTaylorSlackRate

/-!
# The last Palm residual: hmean from the lane producer, hreadout from the frozen readout

FinslerOriginalCostPalmFromFrozenFamily (batch105) reduced LowerLaneRootedTileMeanLaw
to the frozen cost family readout list

  hmean :   masked frozen cost sample mean = palmCostMean,
  hreadout : (1 - 2 eps) * (scale n * palmCostMean n) -> tilePopValue.

This module closes that residual.

## 1. hmean

hmean is discharged by the lane producer tilePalmSampleLaw_sceneCloud: its field (a)
is the cloud-average computation tileMaskedFrozenCostMean_sceneCloud (hence
tileMaskedFrozenCostMean_sceneCloud_eq_average), which identifies the masked frozen
cost sample mean with the explicit finite average T.sceneCloudAverage.  The general
interface lemma tileMaskedFrozenCostMean_eq_of_tilePalmSampleLaw reads field (a) off
any TilePalmSampleLaw.

## 2. hreadout

hreadout is the frozen family readout (1 - 2 eps) * (scale n * cloud average) ->
tilePopValue.  It is reduced to the single empirical readout identification
(hP1-type, with exact type)

  PalmReadoutIdentification:   T.sceneCloudAverage n c - popReadout n -> 0,

plus the population normalization identification

  PalmPopulationReadoutIdentification:
    (1 - 2 eps) * (scale n * popReadout n) - tilePopValue -> 0,

and the paper multiplier bound |(1 - 2 eps) * tileScale n| <= |1 - 2 eps|, proved
here from the concrete scale 0 < tileScale n <= 1.  This is exactly the repo route of
sceneCloudReadout_tendsto_popValue (FinslerOriginalCloudReadoutConvergence), so the
lane producer tilePalmSampleLaw_sceneCloud_of_palmReadout is also produced with both
fields discharged.

## 3. Instantiation

lowerLaneRootedTileMeanLaw_of_palmReadout instantiates LowerLaneRootedTileMeanLaw
from the shortened residual list: hlln, hpop, eps <= 1/2 and the analytic lane fields.

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

/-! ## 0. The multiplier bound at the concrete lane -/

/-- **The paper multiplier bound.**  The product (1 - 2 eps) * tileScale n is bounded
by the constant |1 - 2 eps|, uniformly in n. -/
theorem abs_one_sub_two_mul_tileScale_le (n : ℕ) :
    |(1 - 2 * ε) * tileScale n| ≤ |1 - 2 * ε| := by
  have hspos : 0 < tileScale n := tileScale_pos n
  rw [abs_mul, abs_of_pos hspos]
  calc |1 - 2 * ε| * tileScale n ≤ |1 - 2 * ε| * 1 :=
        mul_le_mul_of_nonneg_left (tileScale_le_one n) (abs_nonneg _)
    _ = |1 - 2 * ε| := mul_one _

/-! ## 1. The readout identification types (the hP1-type inputs, exact types) -/

/-- **The empirical cloud readout identification** (the hP1-type input): the finite
cloud average of the masked frozen cost converges to the population readout. -/
def PalmReadoutIdentification
    (T : D.TaylorTiles ε)
    (pcloud qcloud : ∀ n, Fin (n + 1) → M)
    (c : T.Index) (popReadout : ℕ → ℝ) : Prop :=
  Tendsto (fun n ↦ T.sceneCloudAverage pcloud qcloud n c - popReadout n) atTop (𝓝 0)

/-- **The population normalization identification**: the normalized population
readout converges to the population tile value. -/
def PalmPopulationReadoutIdentification
    (T : D.TaylorTiles ε) (G : ℕ → (ℚ → M) → ℝ) (c : T.Index)
    (popReadout : ℕ → ℝ) : Prop :=
  Tendsto (fun n ↦ (1 - 2 * ε) * (tileScale n * popReadout n) -
    T.tilePopValue (P := P) (a := a) (κ := κ) (lambda := lambda) (q := q) G c)
    atTop (𝓝 0)

/-! ## 2. hmean: the masked frozen cost sample mean from the lane producer -/

/-- **Field (a) of any tile Palm sample law**: the masked frozen cost sample mean is
the law's population Palm readout.  In particular the lane producer
tilePalmSampleLaw_sceneCloud (and tilePalmSampleLaw_sceneCloud_of_palmReadout)
discharges hmean this way. -/
theorem tileMaskedFrozenCostMean_eq_of_tilePalmSampleLaw
    (T : D.TaylorTiles ε) {A B : Set M}
    (pcloud qcloud : ∀ n, Fin (n + 1) → M)
    (f : (↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) (t : ℝ) (c : T.Index) (popVal : ℕ → ℝ)
    (law : T.TilePalmSampleLaw (ε := ε) f t sceneCloudSample (sceneCloudX pcloud)
      (sceneCloudY qcloud) tileScale c popVal) :
    ∀ (n : ℕ), T.tileMaskedFrozenCostMean sceneCloudSample (sceneCloudX pcloud)
      (sceneCloudY qcloud) n c = law.palmCostMean n :=
  law.maskedMean_eq

/-! ## 3. hreadout from the single readout identification -/

/-- **The frozen family readout from the single empirical readout identification.**
Given the hP1-type identification, the population normalization identification and
eps <= 1/2, the normalized frozen readout converges to the population tile value. -/
theorem sceneCloudReadout_tendsto_of_palmReadout
    (T : D.TaylorTiles ε) {A B : Set M}
    (pcloud qcloud : ∀ n, Fin (n + 1) → M) (c : T.Index)
    (popReadout : ℕ → ℝ) (G : ℕ → (ℚ → M) → ℝ)
    (hlln : Tendsto (fun n ↦ T.sceneCloudAverage pcloud qcloud n c - popReadout n)
      atTop (𝓝 0))
    (hpop : Tendsto (fun n ↦ (1 - 2 * ε) * (tileScale n * popReadout n) -
      T.tilePopValue (P := P) (a := a) (κ := κ) (lambda := lambda) (q := q) G c)
      atTop (𝓝 0)) :
    Tendsto (fun n ↦
      (1 - 2 * ε) * (tileScale n * T.sceneCloudAverage pcloud qcloud n c) -
        T.tilePopValue (P := P) (a := a) (κ := κ) (lambda := lambda) (q := q) G c)
      atTop (𝓝 0) :=
  T.sceneCloudReadout_tendsto_popValue pcloud qcloud tileScale c popReadout G
    (fun n ↦ abs_one_sub_two_mul_tileScale_le n) hlln hpop

/-- **The lane producer with both fields discharged.**  From the empirical readout
identification and the population normalization identification, the tile Palm sample
law of the concrete lane holds (field (a) by the cloud-average computation, field (b)
by sceneCloudReadout_tendsto_of_palmReadout). -/
noncomputable def tilePalmSampleLaw_sceneCloud_of_palmReadout
    (T : D.TaylorTiles ε) {A B : Set M}
    (pcloud qcloud : ∀ n, Fin (n + 1) → M)
    (f : (↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) (t : ℝ) (c : T.Index)
    (popReadout : ℕ → ℝ) (G : ℕ → (ℚ → M) → ℝ)
    (hlln : Tendsto (fun n ↦ T.sceneCloudAverage pcloud qcloud n c - popReadout n)
      atTop (𝓝 0))
    (hpop : Tendsto (fun n ↦ (1 - 2 * ε) * (tileScale n * popReadout n) -
      T.tilePopValue (P := P) (a := a) (κ := κ) (lambda := lambda) (q := q) G c)
      atTop (𝓝 0)) :
    T.TilePalmSampleLaw (ε := ε) f t sceneCloudSample (sceneCloudX pcloud)
      (sceneCloudY qcloud) tileScale c
      (fun _ ↦ T.tilePopValue (P := P) (a := a) (κ := κ) (lambda := lambda) (q := q) G c) :=
  T.tilePalmSampleLaw_sceneCloud_of_countingConvergence f t pcloud qcloud tileScale c
    popReadout G (fun n ↦ abs_one_sub_two_mul_tileScale_le n) hlln hpop

/-! ## 4. The shortened residual list -/

/-- **LowerLaneRootedTileMeanLaw from the shortened residual list.**  Both frozen
readout fields are discharged: hmean by the lane producer's field (a) (the cloud
average identity), hreadout by the single hP1-type empirical readout identification
plus the population normalization identification (and eps <= 1/2 for the multiplier
bound).  All remaining inputs are the analytic lane fields. -/
theorem lowerLaneRootedTileMeanLaw_of_palmReadout
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
  lowerLaneRootedTileMeanLaw_of_frozenCostReadout (T := T) (A := A) (B := B)
    pcloud qcloud base G hintEntry hExch hintCost hintRes hresv hBp hbase
    hintC hintP hintLin hintClip hε hz₀ hp
    (fun f t c n ↦ T.sceneCloudAverage pcloud qcloud n c)
    (fun f t c n ↦ T.tileMaskedFrozenCostMean_sceneCloud_eq_average pcloud qcloud n c)
    (fun f t c ↦
      sceneCloudReadout_tendsto_of_palmReadout (T := T) (A := A) (B := B)
        pcloud qcloud c (popReadout f t c) G (hlln f t c) (hpop f t c))
