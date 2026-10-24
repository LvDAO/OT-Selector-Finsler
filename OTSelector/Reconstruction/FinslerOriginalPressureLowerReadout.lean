import OTSelector.Reconstruction.FinslerOriginalTilePalmSampleLaw
import OTSelector.Reconstruction.FinslerOriginalTileSingleConvergenceProof
import OTSelector.Reconstruction.FinslerOriginalTileIntegralSplit
import OTSelector.Reconstruction.FinslerOriginalFixedPairLinearIdentification

/-!
# Pressure-lower readout data assembly from the tile Palm sample law

This module assembles the hreadout data of the pressure-lower lane: the input
data consumed by the two-sided readout identification pressureLower = Psi, as
documented at the end of

* FinslerOriginalTileMeanConvergenceInstantiation.pressureLower_eq_sceneReadout_of_rootedTileSingleConvergence
  (remaining lane inputs: hsingle, hint, hgt, hdecomp, hlim, hread), and
* FinslerOriginalTilePopValueIdentification.pressureLower_eq_sceneReadout_of_fixedPair_and_residual
  (remaining lane inputs: masked-entry exchangeability, the fixed-pair linear
  identification, tile integrability, plan-residual vanishing, and the deep
  context inputs hF hcomplete hu ha hinj hint hgt hdecomp hlim hread).

The fixed-pair linear identification is now reduced to the fields of the tile
Palm sample law (FinslerOriginalTilePalmSampleLaw.TilePalmSampleLaw):

* field maskedMean_eq: the sample mean of the masked frozen cost is the
  population Palm readout palmCostMean (the sample law is the scene Palm law);
* field palm_readout: the normalized readout converges to the tile population
  value tilePopValue.

## What is discharged here

* tileFixedPairLinearPart_palmIdentification_of_palmSampleLaw: the linear
  (cost + probe) part of the fixed-pair masked expectation converges to
  tilePopValue.  This is exactly the analytic content of the tile mean
  identification, now produced from the Palm sample law fields instead of being
  assumed.
* fixedPairMeanIdentification_of_palmSampleLaw: the full fixed-pair masked
  expectation converges to tilePopValue, using the exact integral split
  tileFixedPair = linear + clipping and the clipping-correction vanishing.
* uniformTileAverageConvergence_of_palmSampleLaw: the plan-free per-tile iid LLN
  content (UniformTileAverageConvergence) for the tile population values.
* tileMeanConvergence_of_palmSampleLaw: the per-tile iid LLN
  (TileMeanConvergence) from the plan-free average and plan-residual vanishing.
* rootedTileSingleConvergence_of_palmSampleLaw: the deterministic single-tile
  counting law RootedTileSingleConvergence (hsingle), i.e. the single-tile
  convergence item of the hreadout data.
* rootedTileCampbellMeanIdentification_of_palmSampleLaw: the named lower
  limit-law content RootedTileCampbellMeanIdentification, i.e. the lower
  population mean bound item.
* camFrozenMeanUpperBound_of_palmSampleLaw: the matching upper population mean
  bound item.
* pressureLower_eq_sceneReadout_of_palmSampleLaw: THE MAIN ASSEMBLY: given the
  tile Palm sample law fields and the remaining named inputs, the pressure-lower
  readout coincides with the assembled Palm readout Psi.

## Exact remaining inputs (all explicit, none hidden)

The one main theorem takes exactly the following inputs beyond the lane data
(physical manifold/Finsler hypotheses hF hcomplete hu ha hinj, the samples
sample with probability laws, the iid-position maps X Y, the scale, the frozen
readout family g, the population root data P a kappa lambda G q, the optimal
plans A and the tile cover T):

1. hPalm: the TilePalmSampleLaw fields for every probe f, tilt t and retained
   tile c.  These are paper data: the sample law is the scene Palm product law
   (field maskedMean_eq) and the Campbell/normalization identity
   (1-2 eps) * (scale * palmCostMean) -> tilePopValue (field palm_readout).
2. base and its normalization: the base probe matrix and its uniform bound
   |base| <= Bp; the probe of the tile matrix is the concrete normalized probe
   normalizedProbe base, so this is the source of the probe matrix.
3. hintC hintP hintClip: integrability of the linear cost, linear probe and
   clipping integrands of the tile lane.
4. hclip: vanishing of the fixed-pair clipping correction.  This is the only
   clipping input; it is fully wired for the actual lane by
   FinslerOriginalTileFrozenBoundWiring.tileFixedPairClipping_tendsto_zero_of_tileLane
   from the retained-edge geometric data, the frozen physical cost bound and the
   concrete probe decay, so no analytic gap remains on the clipping side.
5. hExch, hintEntry, hintCost, hintRes, hresv: masked-entry exchangeability of
   the tile matrix, entrywise and pair-sum integrability, and plan-residual
   vanishing (optimal-plan stability).  The first is the permutation invariance
   of the iid sample law; the last is the vanishing covariance estimate.
6. hint: integrability of the per-tile frozen cost of the frozen core functional
   (the frozen core decomposition is the exact identity
   integral_originalFrozenCoreCost_eq_sum_tiles).
7. hgt: the frozen readout family is the atlas piecewise root readout,
   g f t = atlasPiecewiseRoot P a kappa lambda G.
8. hdecomp: the frozen core decomposition of the Campbell-averaged frozen cost
   into the tile population values,
   sum_j integral theta^(-2/q) G = sum_c tilePopValue G c.
9. hlim: the empirical frozen pressure means converge to pressureLower.
10. hread: the readout identification frozenPressureLower P a kappa lambda g q = Psi.
    This is discharged from the frozen-data hypotheses by
    FinslerOriginalScenePressureWiring.frozenPressureLower_eq_sceneReadout_of_frozenData
    (joint frozen-data measurability, uniform probe bound, finite weighted
    kinetic classes, a.e. coverage and unit density, frozen gluing and Palm
    readout constancy); it is kept as a named input here so that this module
    stays independent of the frozen-data lane.

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

namespace OTSelector.Reconstruction

open OTSelector.Geometry

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
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
  {ε : ℝ} (T : D.TaylorTiles ε)
  {K : Set M} {q : ℝ}
  {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]

namespace PopulationLocalPressureCore.TaylorTiles

open OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

/-! ## The linear Palm identification from the Palm sample law fields -/

/-- **The linear Palm identification from the tile Palm sample law.**  The cost
part of the fixed-pair linear part converges to the tile population value by the
Palm sample law fields; the probe part vanishes by the normalized probe decay.
Together the linear (cost + probe) part of the fixed-pair masked expectation
converges to tilePopValue: this is the analytic content of the tile mean
identification, no longer assumed. -/
theorem tileFixedPairLinearPart_palmIdentification_of_palmSampleLaw
    (sample : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (sample n)]
    (f : (K × K) →ᵇ ℝ) (t : ℝ)
    (X Y : ∀ n, Fin (n + 1) → Ω n → M)
    (c : T.Index) (scale : ℕ → ℝ)
    (base : ∀ n, Ω n → T.Index → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    {Bp : ℝ} (hBp : 0 ≤ Bp)
    (hbase : ∀ (n : ℕ) (s : Ω n) (c' : T.Index) (i j : Fin (n + 1)),
      |base n s c' i j| ≤ Bp)
    (hintC : ∀ n, Integrable
      (T.tileLinearCostIntegrand (ε := ε) f t X Y scale n c) (sample n))
    (hintP : ∀ n, Integrable (T.tileLinearProbeIntegrand f t X Y
      (fun (f : (K × K) →ᵇ ℝ) t n s c' ↦ normalizedProbe (K := K) base t n s c') n c) (sample n))
    (G : ℕ → (ℚ → M) → ℝ)
    (hPalm : T.TilePalmSampleLaw f t sample X Y scale c
      (fun _ ↦ T.tilePopValue (P := P) (a := a) (κ := κ) (lambda := lambda)
        (q := q) G c)) :
    PlanFreeTileMeanIdentification
      (fun n ↦ T.tileFixedPairLinearPart f t sample X Y scale
        (fun (f : (K × K) →ᵇ ℝ) t n s c' ↦ normalizedProbe (K := K) base t n s c') n c)
      (fun _ ↦ T.tilePopValue (P := P) (a := a) (κ := κ) (lambda := lambda)
        (q := q) G c) := by
  have hcost := T.tileCostPalmIdentification_of_palmSampleLaw f t sample X Y scale c
    (fun _ ↦ T.tilePopValue (P := P) (a := a) (κ := κ) (lambda := lambda)
      (q := q) G c) hPalm
  exact linearPalmIdentification_of_cost
    (fun n ↦ T.tileFixedPairLinearPart f t sample X Y scale
      (fun (f : (K × K) →ᵇ ℝ) t n s c' ↦ normalizedProbe (K := K) base t n s c') n c)
    (fun n ↦ ∫ s, T.tileLinearCostIntegrand (ε := ε) f t X Y scale n c s ∂sample n)
    (fun n ↦ ∫ s, T.tileLinearProbeIntegrand f t X Y
      (fun (f : (K × K) →ᵇ ℝ) t n s c' ↦ normalizedProbe (K := K) base t n s c') n c s ∂sample n)
    (fun _ ↦ T.tilePopValue (P := P) (a := a) (κ := κ) (lambda := lambda)
      (q := q) G c)
    (fun n ↦ T.tileFixedPairLinearPart_eq_cost_add_probe sample f t X Y scale
      (fun (f : (K × K) →ᵇ ℝ) t n s c' ↦ normalizedProbe (K := K) base t n s c') n c
      (hintC n) (hintP n))
    hcost
    (T.tileLinearProbePart_tendsto_zero sample f t X Y c base hBp hbase hintP)

/-- **The fixed-pair masked identification from the Palm sample law fields.**
The fixed-pair masked expectation splits exactly into its linear part and the
clipping correction; the linear part converges to tilePopValue by the Palm sample
law, and the clipping correction vanishes.  Hence the fixed-pair masked
expectation converges to tilePopValue: the fixed-pair identification item is
discharged from the Palm sample law fields. -/
theorem fixedPairMeanIdentification_of_palmSampleLaw
    (sample : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (sample n)]
    (f : (K × K) →ᵇ ℝ) (t : ℝ)
    (X Y : ∀ n, Fin (n + 1) → Ω n → M)
    (c : T.Index) (scale : ℕ → ℝ)
    (base : ∀ n, Ω n → T.Index → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    {Bp : ℝ} (hBp : 0 ≤ Bp)
    (hbase : ∀ (n : ℕ) (s : Ω n) (c' : T.Index) (i j : Fin (n + 1)),
      |base n s c' i j| ≤ Bp)
    (hintC : ∀ n, Integrable
      (T.tileLinearCostIntegrand (ε := ε) f t X Y scale n c) (sample n))
    (hintP : ∀ n, Integrable (T.tileLinearProbeIntegrand f t X Y
      (fun (f : (K × K) →ᵇ ℝ) t n s c' ↦ normalizedProbe (K := K) base t n s c') n c) (sample n))
    (hintClip : ∀ n, Integrable (T.tileClippingIntegrand (ε := ε) f t X Y scale
      (fun (f : (K × K) →ᵇ ℝ) t n s c' ↦ normalizedProbe (K := K) base t n s c') n c) (sample n))
    (G : ℕ → (ℚ → M) → ℝ)
    (hPalm : T.TilePalmSampleLaw f t sample X Y scale c
      (fun _ ↦ T.tilePopValue (P := P) (a := a) (κ := κ) (lambda := lambda)
        (q := q) G c))
    (hclip : Tendsto (fun n ↦
      T.tileFixedPairClippingCorrection f t sample X Y scale
        (fun (f : (K × K) →ᵇ ℝ) t n s c' ↦ normalizedProbe (K := K) base t n s c') n c)
      atTop (𝓝 0)) :
    PlanFreeTileMeanIdentification
      (fun n ↦ T.tileFixedPair f t sample X Y scale
        (fun (f : (K × K) →ᵇ ℝ) t n s c' ↦ normalizedProbe (K := K) base t n s c') n c)
      (fun _ ↦ T.tilePopValue (P := P) (a := a) (κ := κ) (lambda := lambda)
        (q := q) G c) := by
  have hlin := T.tileFixedPairLinearPart_palmIdentification_of_palmSampleLaw
    sample f t X Y c scale base hBp hbase hintC hintP G hPalm
  have hsplit : ∀ n, T.tileFixedPair f t sample X Y scale
      (fun (f : (K × K) →ᵇ ℝ) t n s c' ↦ normalizedProbe (K := K) base t n s c') n c =
      T.tileFixedPairLinearPart f t sample X Y scale
        (fun (f : (K × K) →ᵇ ℝ) t n s c' ↦ normalizedProbe (K := K) base t n s c') n c +
      T.tileFixedPairClippingCorrection f t sample X Y scale
        (fun (f : (K × K) →ᵇ ℝ) t n s c' ↦ normalizedProbe (K := K) base t n s c') n c := by
    intro n
    have h1 : Integrable (T.tileLinearIntegrand (ε := ε) f t X Y scale
        (fun (f : (K × K) →ᵇ ℝ) t n s c' ↦ normalizedProbe (K := K) base t n s c') n c) (sample n) := by
      have hfun : T.tileLinearIntegrand (ε := ε) f t X Y scale
          (fun (f : (K × K) →ᵇ ℝ) t n s c' ↦ normalizedProbe (K := K) base t n s c') n c =
          (fun s ↦ T.tileLinearCostIntegrand (ε := ε) f t X Y scale n c s +
            T.tileLinearProbeIntegrand f t X Y
              (fun (f : (K × K) →ᵇ ℝ) t n s c' ↦ normalizedProbe (K := K) base t n s c') n c s) :=
        funext fun s ↦ T.tileLinearIntegrand_eq_cost_add_probe f t X Y scale
          (fun (f : (K × K) →ᵇ ℝ) t n s c' ↦ normalizedProbe (K := K) base t n s c') n c s
      rw [hfun]
      exact (hintC n).add (hintP n)
    exact T.tileFixedPair_eq_linear_add_clipping sample f t X Y scale
      (fun (f : (K × K) →ᵇ ℝ) t n s c' ↦ normalizedProbe (K := K) base t n s c') n c h1 (hintClip n)
  exact planFreeTileMeanIdentification_of_palm_and_clipping
    (fun n ↦ T.tileFixedPair f t sample X Y scale
      (fun (f : (K × K) →ᵇ ℝ) t n s c' ↦ normalizedProbe (K := K) base t n s c') n c)
    (fun n ↦ T.tileFixedPairLinearPart f t sample X Y scale
      (fun (f : (K × K) →ᵇ ℝ) t n s c' ↦ normalizedProbe (K := K) base t n s c') n c)
    (fun n ↦ T.tileFixedPairClippingCorrection f t sample X Y scale
      (fun (f : (K × K) →ᵇ ℝ) t n s c' ↦ normalizedProbe (K := K) base t n s c') n c)
    (fun _ ↦ T.tilePopValue (P := P) (a := a) (κ := κ) (lambda := lambda)
      (q := q) G c) hsplit hlin hclip

/-! ## The plan-free tile LLN and the per-tile iid LLN from the Palm sample law -/

/-- **The plan-free per-tile iid LLN from the Palm sample law fields.**  The
normalized plan-free tile average converges to the tile population value: the
Palm sample law supplies the fixed-pair masked identification, masked-entry
exchangeability turns the plan-free average into the fixed-pair expectation. -/
theorem uniformTileAverageConvergence_of_palmSampleLaw
    (sample : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (sample n)]
    (G : ℕ → (ℚ → M) → ℝ)
    (X Y : ∀ n, Fin (n + 1) → Ω n → M)
    (scale : ℕ → ℝ)
    (base : ∀ n, Ω n → T.Index → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    {Bp : ℝ} (hBp : 0 ≤ Bp)
    (hbase : ∀ (n : ℕ) (s : Ω n) (c' : T.Index) (i j : Fin (n + 1)),
      |base n s c' i j| ≤ Bp)
    (hintC : ∀ (f : (K × K) →ᵇ ℝ) (t : ℝ) (n : ℕ) (c : T.Index), Integrable
      (T.tileLinearCostIntegrand (ε := ε) f t X Y scale n c) (sample n))
    (hintP : ∀ (f : (K × K) →ᵇ ℝ) (t : ℝ) (n : ℕ) (c : T.Index), Integrable
      (T.tileLinearProbeIntegrand f t X Y
        (fun (f : (K × K) →ᵇ ℝ) t n s c' ↦ normalizedProbe (K := K) base t n s c') n c) (sample n))
    (hintClip : ∀ (f : (K × K) →ᵇ ℝ) (t : ℝ) (n : ℕ) (c : T.Index), Integrable
      (T.tileClippingIntegrand (ε := ε) f t X Y scale
        (fun (f : (K × K) →ᵇ ℝ) t n s c' ↦ normalizedProbe (K := K) base t n s c') n c) (sample n))
    (hPalm : ∀ (f : (K × K) →ᵇ ℝ) (t : ℝ) (c : T.Index),
      T.TilePalmSampleLaw f t sample X Y scale c
        (fun _ ↦ T.tilePopValue (P := P) (a := a) (κ := κ) (lambda := lambda)
          (q := q) G c))
    (hclip : ∀ (f : (K × K) →ᵇ ℝ) (t : ℝ) (c : T.Index),
      Tendsto (fun n ↦ T.tileFixedPairClippingCorrection f t sample X Y scale
        (fun (f : (K × K) →ᵇ ℝ) t n s c' ↦ normalizedProbe (K := K) base t n s c') n c)
        atTop (𝓝 0))
    (hintEntry : ∀ (f : (K × K) →ᵇ ℝ) (t : ℝ) (n : ℕ) (c : T.Index)
      (i j : Fin (n + 1)),
      Integrable (fun s ↦ T.tileCostMatrix f t X Y scale
        (fun (f : (K × K) →ᵇ ℝ) t n s c' ↦ normalizedProbe (K := K) base t n s c') n c s i j)
        (sample n))
    (hExch : ∀ (f : (K × K) →ᵇ ℝ) (t : ℝ) (n : ℕ) (c : T.Index),
      MaskedEntryExchangeability (sample n) (T.tileCostMatrix f t X Y scale
        (fun (f : (K × K) →ᵇ ℝ) t n s c' ↦ normalizedProbe (K := K) base t n s c') n c)) :
    T.UniformTileAverageConvergence
      (fun _ _ c ↦ T.tilePopValue (P := P) (a := a) (κ := κ) (lambda := lambda)
        (q := q) G c) sample X Y scale
      (fun (f : (K × K) →ᵇ ℝ) t n s c' ↦ normalizedProbe (K := K) base t n s c') :=
  uniformTileAverageConvergence_of_fixedPairIdentification (T := T) sample G X Y
    scale (fun (f : (K × K) →ᵇ ℝ) t n s c' ↦ normalizedProbe (K := K) base t n s c')
    hintEntry hExch
    (fun f t c ↦ T.fixedPairMeanIdentification_of_palmSampleLaw sample f t X Y c
      scale base hBp hbase (fun n ↦ hintC f t n c) (fun n ↦ hintP f t n c) (fun n ↦ hintClip f t n c) G
      (hPalm f t c) (hclip f t c))

/-- **The per-tile iid LLN from the Palm sample law fields.**  Combining the
plan-free average convergence with the plan-residual vanishing gives
TileMeanConvergence: the empirical per-tile frozen means converge to the tile
population values. -/
theorem tileMeanConvergence_of_palmSampleLaw
    (sample : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (sample n)]
    (G : ℕ → (ℚ → M) → ℝ)
    (X Y : ∀ n, Fin (n + 1) → Ω n → M)
    (scale : ℕ → ℝ)
    (base : ∀ n, Ω n → T.Index → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    {Bp : ℝ} (hBp : 0 ≤ Bp)
    (hbase : ∀ (n : ℕ) (s : Ω n) (c' : T.Index) (i j : Fin (n + 1)),
      |base n s c' i j| ≤ Bp)
    (hintC : ∀ (f : (K × K) →ᵇ ℝ) (t : ℝ) (n : ℕ) (c : T.Index), Integrable
      (T.tileLinearCostIntegrand (ε := ε) f t X Y scale n c) (sample n))
    (hintP : ∀ (f : (K × K) →ᵇ ℝ) (t : ℝ) (n : ℕ) (c : T.Index), Integrable
      (T.tileLinearProbeIntegrand f t X Y
        (fun (f : (K × K) →ᵇ ℝ) t n s c' ↦ normalizedProbe (K := K) base t n s c') n c) (sample n))
    (hintClip : ∀ (f : (K × K) →ᵇ ℝ) (t : ℝ) (n : ℕ) (c : T.Index), Integrable
      (T.tileClippingIntegrand (ε := ε) f t X Y scale
        (fun (f : (K × K) →ᵇ ℝ) t n s c' ↦ normalizedProbe (K := K) base t n s c') n c) (sample n))
    (hPalm : ∀ (f : (K × K) →ᵇ ℝ) (t : ℝ) (c : T.Index),
      T.TilePalmSampleLaw f t sample X Y scale c
        (fun _ ↦ T.tilePopValue (P := P) (a := a) (κ := κ) (lambda := lambda)
          (q := q) G c))
    (hclip : ∀ (f : (K × K) →ᵇ ℝ) (t : ℝ) (c : T.Index),
      Tendsto (fun n ↦ T.tileFixedPairClippingCorrection f t sample X Y scale
        (fun (f : (K × K) →ᵇ ℝ) t n s c' ↦ normalizedProbe (K := K) base t n s c') n c)
        atTop (𝓝 0))
    (A : ∀ n, Ω n → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (hintEntry : ∀ (f : (K × K) →ᵇ ℝ) (t : ℝ) (n : ℕ) (c : T.Index)
      (i j : Fin (n + 1)),
      Integrable (fun s ↦ T.tileCostMatrix f t X Y scale
        (fun (f : (K × K) →ᵇ ℝ) t n s c' ↦ normalizedProbe (K := K) base t n s c') n c s i j)
        (sample n))
    (hExch : ∀ (f : (K × K) →ᵇ ℝ) (t : ℝ) (n : ℕ) (c : T.Index),
      MaskedEntryExchangeability (sample n) (T.tileCostMatrix f t X Y scale
        (fun (f : (K × K) →ᵇ ℝ) t n s c' ↦ normalizedProbe (K := K) base t n s c') n c))
    (hintCost : ∀ (f : (K × K) →ᵇ ℝ) (t : ℝ) (n : ℕ) (c : T.Index),
      Integrable (fun s ↦ ∑ i, ∑ j, T.tileCostMatrix f t X Y scale
        (fun (f : (K × K) →ᵇ ℝ) t n s c' ↦ normalizedProbe (K := K) base t n s c') n c s i j)
        (sample n))
    (hintRes : ∀ (f : (K × K) →ᵇ ℝ) (t : ℝ) (n : ℕ) (c : T.Index),
      Integrable (fun s ↦ ∑ i, ∑ j,
        (A n s i j - 1 / ((n + 1 : ℕ) : ℝ)) *
          T.tileCostMatrix f t X Y scale
            (fun (f : (K × K) →ᵇ ℝ) t n s c' ↦ normalizedProbe (K := K) base t n s c') n c s i j)
        (sample n))
    (hresv : T.TilePlanResidualVanishing sample A X Y scale
      (fun (f : (K × K) →ᵇ ℝ) t n s c' ↦ normalizedProbe (K := K) base t n s c')) :
    T.TileMeanConvergence
      (fun _ _ c ↦ T.tilePopValue (P := P) (a := a) (κ := κ) (lambda := lambda)
        (q := q) G c) sample X Y scale
      (fun (f : (K × K) →ᵇ ℝ) t n s c' ↦ normalizedProbe (K := K) base t n s c') A :=
  tileMeanConvergence_of_uniform_and_residual (T := T) sample G X Y scale
    (fun (f : (K × K) →ᵇ ℝ) t n s c' ↦ normalizedProbe (K := K) base t n s c') A hintCost hintRes
    (uniformTileAverageConvergence_of_palmSampleLaw (T := T) sample G X Y scale base
      hBp hbase hintC hintP hintClip hPalm hclip hintEntry hExch)
    hresv

/-- **The deterministic single-tile counting law from the Palm sample law.**  The
single-tile convergence item hsingle of the hreadout data: for every fixed
retained tile the empirical frozen tile mean converges to the tile population
value. -/
theorem rootedTileSingleConvergence_of_palmSampleLaw
    (sample : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (sample n)]
    (G : ℕ → (ℚ → M) → ℝ)
    (X Y : ∀ n, Fin (n + 1) → Ω n → M)
    (scale : ℕ → ℝ)
    (base : ∀ n, Ω n → T.Index → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    {Bp : ℝ} (hBp : 0 ≤ Bp)
    (hbase : ∀ (n : ℕ) (s : Ω n) (c' : T.Index) (i j : Fin (n + 1)),
      |base n s c' i j| ≤ Bp)
    (hintC : ∀ (f : (K × K) →ᵇ ℝ) (t : ℝ) (n : ℕ) (c : T.Index), Integrable
      (T.tileLinearCostIntegrand (ε := ε) f t X Y scale n c) (sample n))
    (hintP : ∀ (f : (K × K) →ᵇ ℝ) (t : ℝ) (n : ℕ) (c : T.Index), Integrable
      (T.tileLinearProbeIntegrand f t X Y
        (fun (f : (K × K) →ᵇ ℝ) t n s c' ↦ normalizedProbe (K := K) base t n s c') n c) (sample n))
    (hintClip : ∀ (f : (K × K) →ᵇ ℝ) (t : ℝ) (n : ℕ) (c : T.Index), Integrable
      (T.tileClippingIntegrand (ε := ε) f t X Y scale
        (fun (f : (K × K) →ᵇ ℝ) t n s c' ↦ normalizedProbe (K := K) base t n s c') n c) (sample n))
    (hPalm : ∀ (f : (K × K) →ᵇ ℝ) (t : ℝ) (c : T.Index),
      T.TilePalmSampleLaw f t sample X Y scale c
        (fun _ ↦ T.tilePopValue (P := P) (a := a) (κ := κ) (lambda := lambda)
          (q := q) G c))
    (hclip : ∀ (f : (K × K) →ᵇ ℝ) (t : ℝ) (c : T.Index),
      Tendsto (fun n ↦ T.tileFixedPairClippingCorrection f t sample X Y scale
        (fun (f : (K × K) →ᵇ ℝ) t n s c' ↦ normalizedProbe (K := K) base t n s c') n c)
        atTop (𝓝 0))
    (A : ∀ n, Ω n → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (hintEntry : ∀ (f : (K × K) →ᵇ ℝ) (t : ℝ) (n : ℕ) (c : T.Index)
      (i j : Fin (n + 1)),
      Integrable (fun s ↦ T.tileCostMatrix f t X Y scale
        (fun (f : (K × K) →ᵇ ℝ) t n s c' ↦ normalizedProbe (K := K) base t n s c') n c s i j)
        (sample n))
    (hExch : ∀ (f : (K × K) →ᵇ ℝ) (t : ℝ) (n : ℕ) (c : T.Index),
      MaskedEntryExchangeability (sample n) (T.tileCostMatrix f t X Y scale
        (fun (f : (K × K) →ᵇ ℝ) t n s c' ↦ normalizedProbe (K := K) base t n s c') n c))
    (hintCost : ∀ (f : (K × K) →ᵇ ℝ) (t : ℝ) (n : ℕ) (c : T.Index),
      Integrable (fun s ↦ ∑ i, ∑ j, T.tileCostMatrix f t X Y scale
        (fun (f : (K × K) →ᵇ ℝ) t n s c' ↦ normalizedProbe (K := K) base t n s c') n c s i j)
        (sample n))
    (hintRes : ∀ (f : (K × K) →ᵇ ℝ) (t : ℝ) (n : ℕ) (c : T.Index),
      Integrable (fun s ↦ ∑ i, ∑ j,
        (A n s i j - 1 / ((n + 1 : ℕ) : ℝ)) *
          T.tileCostMatrix f t X Y scale
            (fun (f : (K × K) →ᵇ ℝ) t n s c' ↦ normalizedProbe (K := K) base t n s c') n c s i j)
        (sample n))
    (hresv : T.TilePlanResidualVanishing sample A X Y scale
      (fun (f : (K × K) →ᵇ ℝ) t n s c' ↦ normalizedProbe (K := K) base t n s c')) :
    T.RootedTileSingleConvergence
      (fun _ _ c ↦ T.tilePopValue (P := P) (a := a) (κ := κ) (lambda := lambda)
        (q := q) G c) sample X Y scale
      (fun (f : (K × K) →ᵇ ℝ) t n s c' ↦ normalizedProbe (K := K) base t n s c') A :=
  rootedTileSingleConvergence_of_inProbability (T := T)
    (fun _ _ c ↦ T.tilePopValue (P := P) (a := a) (κ := κ) (lambda := lambda)
      (q := q) G c) sample X Y scale
    (fun (f : (K × K) →ᵇ ℝ) t n s c' ↦ normalizedProbe (K := K) base t n s c') A
    (rootedTileSingleConvergenceInProbability_of_tileMeanConvergence (T := T)
      (fun _ _ c ↦ T.tilePopValue (P := P) (a := a) (κ := κ) (lambda := lambda)
        (q := q) G c) sample X Y scale
      (fun (f : (K × K) →ᵇ ℝ) t n s c' ↦ normalizedProbe (K := K) base t n s c') A
      (tileMeanConvergence_of_palmSampleLaw (T := T) sample G X Y scale base hBp
        hbase hintC hintP hintClip hPalm hclip A hintEntry hExch hintCost hintRes
        hresv))

/-! ## The named hreadout data from the Palm sample law fields -/

/-- **The named lower limit-law content from the Palm sample law.**  The lower
population mean bound RootedTileCampbellMeanIdentification (item hint of the
hreadout data) for the frozen core functional of the original empirical optimal
face, with the single-tile and per-tile mean content produced from the Palm
sample law fields. -/
theorem rootedTileCampbellMeanIdentification_of_palmSampleLaw
    (sample : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (sample n)]
    (G : ℕ → (ℚ → M) → ℝ)
    (X Y : ∀ n, Fin (n + 1) → Ω n → M)
    (scale : ℕ → ℝ)
    (base : ∀ n, Ω n → T.Index → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    {Bp : ℝ} (hBp : 0 ≤ Bp)
    (hbase : ∀ (n : ℕ) (s : Ω n) (c' : T.Index) (i j : Fin (n + 1)),
      |base n s c' i j| ≤ Bp)
    (hintC : ∀ (f : (K × K) →ᵇ ℝ) (t : ℝ) (n : ℕ) (c : T.Index), Integrable
      (T.tileLinearCostIntegrand (ε := ε) f t X Y scale n c) (sample n))
    (hintP : ∀ (f : (K × K) →ᵇ ℝ) (t : ℝ) (n : ℕ) (c : T.Index), Integrable
      (T.tileLinearProbeIntegrand f t X Y
        (fun (f : (K × K) →ᵇ ℝ) t n s c' ↦ normalizedProbe (K := K) base t n s c') n c) (sample n))
    (hintClip : ∀ (f : (K × K) →ᵇ ℝ) (t : ℝ) (n : ℕ) (c : T.Index), Integrable
      (T.tileClippingIntegrand (ε := ε) f t X Y scale
        (fun (f : (K × K) →ᵇ ℝ) t n s c' ↦ normalizedProbe (K := K) base t n s c') n c) (sample n))
    (hPalm : ∀ (f : (K × K) →ᵇ ℝ) (t : ℝ) (c : T.Index),
      T.TilePalmSampleLaw f t sample X Y scale c
        (fun _ ↦ T.tilePopValue (P := P) (a := a) (κ := κ) (lambda := lambda)
          (q := q) G c))
    (hclip : ∀ (f : (K × K) →ᵇ ℝ) (t : ℝ) (c : T.Index),
      Tendsto (fun n ↦ T.tileFixedPairClippingCorrection f t sample X Y scale
        (fun (f : (K × K) →ᵇ ℝ) t n s c' ↦ normalizedProbe (K := K) base t n s c') n c)
        atTop (𝓝 0))
    (A : ∀ n, Ω n → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (hintEntry : ∀ (f : (K × K) →ᵇ ℝ) (t : ℝ) (n : ℕ) (c : T.Index)
      (i j : Fin (n + 1)),
      Integrable (fun s ↦ T.tileCostMatrix f t X Y scale
        (fun (f : (K × K) →ᵇ ℝ) t n s c' ↦ normalizedProbe (K := K) base t n s c') n c s i j)
        (sample n))
    (hExch : ∀ (f : (K × K) →ᵇ ℝ) (t : ℝ) (n : ℕ) (c : T.Index),
      MaskedEntryExchangeability (sample n) (T.tileCostMatrix f t X Y scale
        (fun (f : (K × K) →ᵇ ℝ) t n s c' ↦ normalizedProbe (K := K) base t n s c') n c))
    (hintCost : ∀ (f : (K × K) →ᵇ ℝ) (t : ℝ) (n : ℕ) (c : T.Index),
      Integrable (fun s ↦ ∑ i, ∑ j, T.tileCostMatrix f t X Y scale
        (fun (f : (K × K) →ᵇ ℝ) t n s c' ↦ normalizedProbe (K := K) base t n s c') n c s i j)
        (sample n))
    (hintRes : ∀ (f : (K × K) →ᵇ ℝ) (t : ℝ) (n : ℕ) (c : T.Index),
      Integrable (fun s ↦ ∑ i, ∑ j,
        (A n s i j - 1 / ((n + 1 : ℕ) : ℝ)) *
          T.tileCostMatrix f t X Y scale
            (fun (f : (K × K) →ᵇ ℝ) t n s c' ↦ normalizedProbe (K := K) base t n s c') n c s i j)
        (sample n))
    (hresv : T.TilePlanResidualVanishing sample A X Y scale
      (fun (f : (K × K) →ᵇ ℝ) t n s c' ↦ normalizedProbe (K := K) base t n s c'))
    (g : ((K × K) →ᵇ ℝ) → ℝ → (ℚ → M) → ℝ)
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _instTileMeanProofMetric : MetricSpace M := F.metricSpace;
      LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))
    (hint : ∀ (f : (K × K) →ᵇ ℝ) (t : ℝ) (n : ℕ) (c : T.Index),
      Integrable (T.tileFrozenCost (fun s i ↦ X n i s) (fun s i ↦ Y n i s)
        (fun s c' ↦ normalizedProbe (K := K) base t n s c')
        (A n) (scale n) t c) (sample n))
    (hgt : ∀ (f : (K × K) →ᵇ ℝ) (t : ℝ),
      g f t = atlasPiecewiseRoot P a κ lambda G)
    (hdecomp : ∀ (f : (K × K) →ᵇ ℝ) (t : ℝ),
      (∑' j, ∫ z in populationSeedRootPiece P a κ lambda j,
          populationAtlasTheta P a κ lambda j z ^ (-2 / q) * G j z ∂lambda) =
        (∑ c : T.Index, T.tilePopValue (P := P) (a := a) (κ := κ)
          (lambda := lambda) (q := q) G c))
    :
    RootedTileCampbellMeanIdentification P a κ lambda g q sample
      (fun f t n s ↦ fractionalAssignmentCost
        (T.originalFrozenCoreMatrix (fun i ↦ X n i s) (fun i ↦ Y n i s)
          (scale n) t ((fun (f : (K × K) →ᵇ ℝ) t n s c' ↦ normalizedProbe (K := K) base t n s c') f t n s)) (A n s) / ((n + 1 : ℕ) : ℝ)) T.Index :=
  rootedTileCampbellMeanIdentification_of_tileMeanConvergence (T := T) sample G g
    X Y scale (fun (f : (K × K) →ᵇ ℝ) t n s c' ↦ normalizedProbe (K := K) base t n s c') A hF hcomplete hu ha hinj hint hgt hdecomp
    (tileMeanConvergence_of_palmSampleLaw (T := T) sample G X Y scale base hBp hbase hintC hintP hintClip hPalm hclip A hintEntry hExch hintCost hintRes hresv)

/-- **The matching upper population mean bound from the Palm sample law.**  The
upper mean bound item of the hreadout data: the expected normalized frozen core
pressure is asymptotically at most the Campbell-averaged frozen cost. -/
theorem camFrozenMeanUpperBound_of_palmSampleLaw
    (sample : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (sample n)]
    (G : ℕ → (ℚ → M) → ℝ)
    (X Y : ∀ n, Fin (n + 1) → Ω n → M)
    (scale : ℕ → ℝ)
    (base : ∀ n, Ω n → T.Index → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    {Bp : ℝ} (hBp : 0 ≤ Bp)
    (hbase : ∀ (n : ℕ) (s : Ω n) (c' : T.Index) (i j : Fin (n + 1)),
      |base n s c' i j| ≤ Bp)
    (hintC : ∀ (f : (K × K) →ᵇ ℝ) (t : ℝ) (n : ℕ) (c : T.Index), Integrable
      (T.tileLinearCostIntegrand (ε := ε) f t X Y scale n c) (sample n))
    (hintP : ∀ (f : (K × K) →ᵇ ℝ) (t : ℝ) (n : ℕ) (c : T.Index), Integrable
      (T.tileLinearProbeIntegrand f t X Y
        (fun (f : (K × K) →ᵇ ℝ) t n s c' ↦ normalizedProbe (K := K) base t n s c') n c) (sample n))
    (hintClip : ∀ (f : (K × K) →ᵇ ℝ) (t : ℝ) (n : ℕ) (c : T.Index), Integrable
      (T.tileClippingIntegrand (ε := ε) f t X Y scale
        (fun (f : (K × K) →ᵇ ℝ) t n s c' ↦ normalizedProbe (K := K) base t n s c') n c) (sample n))
    (hPalm : ∀ (f : (K × K) →ᵇ ℝ) (t : ℝ) (c : T.Index),
      T.TilePalmSampleLaw f t sample X Y scale c
        (fun _ ↦ T.tilePopValue (P := P) (a := a) (κ := κ) (lambda := lambda)
          (q := q) G c))
    (hclip : ∀ (f : (K × K) →ᵇ ℝ) (t : ℝ) (c : T.Index),
      Tendsto (fun n ↦ T.tileFixedPairClippingCorrection f t sample X Y scale
        (fun (f : (K × K) →ᵇ ℝ) t n s c' ↦ normalizedProbe (K := K) base t n s c') n c)
        atTop (𝓝 0))
    (A : ∀ n, Ω n → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (hintEntry : ∀ (f : (K × K) →ᵇ ℝ) (t : ℝ) (n : ℕ) (c : T.Index)
      (i j : Fin (n + 1)),
      Integrable (fun s ↦ T.tileCostMatrix f t X Y scale
        (fun (f : (K × K) →ᵇ ℝ) t n s c' ↦ normalizedProbe (K := K) base t n s c') n c s i j)
        (sample n))
    (hExch : ∀ (f : (K × K) →ᵇ ℝ) (t : ℝ) (n : ℕ) (c : T.Index),
      MaskedEntryExchangeability (sample n) (T.tileCostMatrix f t X Y scale
        (fun (f : (K × K) →ᵇ ℝ) t n s c' ↦ normalizedProbe (K := K) base t n s c') n c))
    (hintCost : ∀ (f : (K × K) →ᵇ ℝ) (t : ℝ) (n : ℕ) (c : T.Index),
      Integrable (fun s ↦ ∑ i, ∑ j, T.tileCostMatrix f t X Y scale
        (fun (f : (K × K) →ᵇ ℝ) t n s c' ↦ normalizedProbe (K := K) base t n s c') n c s i j)
        (sample n))
    (hintRes : ∀ (f : (K × K) →ᵇ ℝ) (t : ℝ) (n : ℕ) (c : T.Index),
      Integrable (fun s ↦ ∑ i, ∑ j,
        (A n s i j - 1 / ((n + 1 : ℕ) : ℝ)) *
          T.tileCostMatrix f t X Y scale
            (fun (f : (K × K) →ᵇ ℝ) t n s c' ↦ normalizedProbe (K := K) base t n s c') n c s i j)
        (sample n))
    (hresv : T.TilePlanResidualVanishing sample A X Y scale
      (fun (f : (K × K) →ᵇ ℝ) t n s c' ↦ normalizedProbe (K := K) base t n s c'))
    (g : ((K × K) →ᵇ ℝ) → ℝ → (ℚ → M) → ℝ)
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _instTileMeanProofMetric : MetricSpace M := F.metricSpace;
      LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))
    (hint : ∀ (f : (K × K) →ᵇ ℝ) (t : ℝ) (n : ℕ) (c : T.Index),
      Integrable (T.tileFrozenCost (fun s i ↦ X n i s) (fun s i ↦ Y n i s)
        (fun s c' ↦ normalizedProbe (K := K) base t n s c')
        (A n) (scale n) t c) (sample n))
    (hgt : ∀ (f : (K × K) →ᵇ ℝ) (t : ℝ),
      g f t = atlasPiecewiseRoot P a κ lambda G)
    (hdecomp : ∀ (f : (K × K) →ᵇ ℝ) (t : ℝ),
      (∑' j, ∫ z in populationSeedRootPiece P a κ lambda j,
          populationAtlasTheta P a κ lambda j z ^ (-2 / q) * G j z ∂lambda) =
        (∑ c : T.Index, T.tilePopValue (P := P) (a := a) (κ := κ)
          (lambda := lambda) (q := q) G c))
    :
    ∀ (f : (K × K) →ᵇ ℝ) (t ε : ℝ), 0 < ε → ∀ᶠ n in atTop,
      ∫ s, fractionalAssignmentCost
        (T.originalFrozenCoreMatrix (fun i ↦ X n i s) (fun i ↦ Y n i s)
          (scale n) t ((fun (f : (K × K) →ᵇ ℝ) t n s c' ↦ normalizedProbe (K := K) base t n s c') f t n s)) (A n s) / ((n + 1 : ℕ) : ℝ) ∂sample n ≤
        campbellAveragedFrozenCost P a κ lambda (g f t) q + ε :=
  camFrozenMeanUpperBound_of_tileMeanConvergence (T := T) sample G g X Y scale
    (fun (f : (K × K) →ᵇ ℝ) t n s c' ↦ normalizedProbe (K := K) base t n s c') A hF hcomplete hu ha hinj hint hgt hdecomp
    (tileMeanConvergence_of_palmSampleLaw (T := T) sample G X Y scale base hBp hbase hintC hintP hintClip hPalm hclip A hintEntry hExch hintCost hintRes hresv)

/-- **THE PRESSURE-LOWER READOUT ASSEMBLY.**  Given the tile Palm sample law
fields and the remaining named inputs, the pressure-lower input of the final
assembly equals the assembled Palm readout Psi.  The single-tile counting law,
the per-tile iid LLN, the plan-free tile average, the lower population mean
bound and the upper population mean bound are all produced internally; the
remaining inputs are exactly those documented in the module header (Palm sample
law fields, probe base normalization and integrability, clipping vanishing,
masked-entry exchangeability, tile integrability, plan-residual vanishing, the
frozen readout family identification, the frozen core decomposition, the
fractional limit identification and the readout identification). -/
theorem pressureLower_eq_sceneReadout_of_palmSampleLaw
    (sample : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (sample n)]
    (G : ℕ → (ℚ → M) → ℝ)
    (X Y : ∀ n, Fin (n + 1) → Ω n → M)
    (scale : ℕ → ℝ)
    (base : ∀ n, Ω n → T.Index → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    {Bp : ℝ} (hBp : 0 ≤ Bp)
    (hbase : ∀ (n : ℕ) (s : Ω n) (c' : T.Index) (i j : Fin (n + 1)),
      |base n s c' i j| ≤ Bp)
    (hintC : ∀ (f : (K × K) →ᵇ ℝ) (t : ℝ) (n : ℕ) (c : T.Index), Integrable
      (T.tileLinearCostIntegrand (ε := ε) f t X Y scale n c) (sample n))
    (hintP : ∀ (f : (K × K) →ᵇ ℝ) (t : ℝ) (n : ℕ) (c : T.Index), Integrable
      (T.tileLinearProbeIntegrand f t X Y
        (fun (f : (K × K) →ᵇ ℝ) t n s c' ↦ normalizedProbe (K := K) base t n s c') n c) (sample n))
    (hintClip : ∀ (f : (K × K) →ᵇ ℝ) (t : ℝ) (n : ℕ) (c : T.Index), Integrable
      (T.tileClippingIntegrand (ε := ε) f t X Y scale
        (fun (f : (K × K) →ᵇ ℝ) t n s c' ↦ normalizedProbe (K := K) base t n s c') n c) (sample n))
    (hPalm : ∀ (f : (K × K) →ᵇ ℝ) (t : ℝ) (c : T.Index),
      T.TilePalmSampleLaw f t sample X Y scale c
        (fun _ ↦ T.tilePopValue (P := P) (a := a) (κ := κ) (lambda := lambda)
          (q := q) G c))
    (hclip : ∀ (f : (K × K) →ᵇ ℝ) (t : ℝ) (c : T.Index),
      Tendsto (fun n ↦ T.tileFixedPairClippingCorrection f t sample X Y scale
        (fun (f : (K × K) →ᵇ ℝ) t n s c' ↦ normalizedProbe (K := K) base t n s c') n c)
        atTop (𝓝 0))
    (A : ∀ n, Ω n → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (hintEntry : ∀ (f : (K × K) →ᵇ ℝ) (t : ℝ) (n : ℕ) (c : T.Index)
      (i j : Fin (n + 1)),
      Integrable (fun s ↦ T.tileCostMatrix f t X Y scale
        (fun (f : (K × K) →ᵇ ℝ) t n s c' ↦ normalizedProbe (K := K) base t n s c') n c s i j)
        (sample n))
    (hExch : ∀ (f : (K × K) →ᵇ ℝ) (t : ℝ) (n : ℕ) (c : T.Index),
      MaskedEntryExchangeability (sample n) (T.tileCostMatrix f t X Y scale
        (fun (f : (K × K) →ᵇ ℝ) t n s c' ↦ normalizedProbe (K := K) base t n s c') n c))
    (hintCost : ∀ (f : (K × K) →ᵇ ℝ) (t : ℝ) (n : ℕ) (c : T.Index),
      Integrable (fun s ↦ ∑ i, ∑ j, T.tileCostMatrix f t X Y scale
        (fun (f : (K × K) →ᵇ ℝ) t n s c' ↦ normalizedProbe (K := K) base t n s c') n c s i j)
        (sample n))
    (hintRes : ∀ (f : (K × K) →ᵇ ℝ) (t : ℝ) (n : ℕ) (c : T.Index),
      Integrable (fun s ↦ ∑ i, ∑ j,
        (A n s i j - 1 / ((n + 1 : ℕ) : ℝ)) *
          T.tileCostMatrix f t X Y scale
            (fun (f : (K × K) →ᵇ ℝ) t n s c' ↦ normalizedProbe (K := K) base t n s c') n c s i j)
        (sample n))
    (hresv : T.TilePlanResidualVanishing sample A X Y scale
      (fun (f : (K × K) →ᵇ ℝ) t n s c' ↦ normalizedProbe (K := K) base t n s c'))
    (g : ((K × K) →ᵇ ℝ) → ℝ → (ℚ → M) → ℝ)
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _instTileMeanProofMetric : MetricSpace M := F.metricSpace;
      LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))
    (hint : ∀ (f : (K × K) →ᵇ ℝ) (t : ℝ) (n : ℕ) (c : T.Index),
      Integrable (T.tileFrozenCost (fun s i ↦ X n i s) (fun s i ↦ Y n i s)
        (fun s c' ↦ normalizedProbe (K := K) base t n s c')
        (A n) (scale n) t c) (sample n))
    (hgt : ∀ (f : (K × K) →ᵇ ℝ) (t : ℝ),
      g f t = atlasPiecewiseRoot P a κ lambda G)
    (hdecomp : ∀ (f : (K × K) →ᵇ ℝ) (t : ℝ),
      (∑' j, ∫ z in populationSeedRootPiece P a κ lambda j,
          populationAtlasTheta P a κ lambda j z ^ (-2 / q) * G j z ∂lambda) =
        (∑ c : T.Index, T.tilePopValue (P := P) (a := a) (κ := κ)
          (lambda := lambda) (q := q) G c))
    (pressureLower : ((K × K) →ᵇ ℝ) → ℝ → ℝ)
    (hlim : ∀ (f : (K × K) →ᵇ ℝ) (t : ℝ),
      Tendsto (fun n ↦ ∫ s, fractionalAssignmentCost
        (T.originalFrozenCoreMatrix (fun i ↦ X n i s) (fun i ↦ Y n i s)
          (scale n) t ((fun (f : (K × K) →ᵇ ℝ) t n s c' ↦ normalizedProbe (K := K) base t n s c') f t n s)) (A n s) / ((n + 1 : ℕ) : ℝ) ∂sample n)
        atTop (𝓝 (pressureLower f t)))
    (Ψ : ((K × K) →ᵇ ℝ) → ℝ → ℝ)
    (hread : frozenPressureLower P a κ lambda g q = Ψ) :
    pressureLower = Ψ :=
  pressureLower_eq_sceneReadout_of_tileMeanConvergence (T := T) sample G g X Y
    scale (fun (f : (K × K) →ᵇ ℝ) t n s c' ↦ normalizedProbe (K := K) base t n s c') A hF hcomplete hu ha hinj hint hgt hdecomp
    (tileMeanConvergence_of_palmSampleLaw (T := T) sample G X Y scale base hBp hbase hintC hintP hintClip hPalm hclip A hintEntry hExch hintCost hintRes hresv) pressureLower hlim Ψ hread

end PopulationLocalPressureCore.TaylorTiles

end OTSelector.Reconstruction

