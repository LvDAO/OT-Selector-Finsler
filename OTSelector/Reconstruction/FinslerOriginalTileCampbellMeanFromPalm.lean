import OTSelector.Reconstruction.FinslerOriginalEndgameLowerLaneWired

/-!
# The endgame lower lane hId from the tile Palm sample law and the Palm LLN

The endgame lower lane bundle endgameLowerFields_actual_lane_wired
(FinslerOriginalEndgameLowerLaneWired) consumes, besides the geometric lane data,
exactly one probabilistic input: its hId binder

  RootedTileCampbellMeanIdentification P a kappa lambda g q sceneCloudSample
    (hprobFrozenCostFamily (K := A union B) T (sceneCloudX pcloud)
      (sceneCloudY qcloud) base Assign tileScale) T.Index,

the rooted tile Campbell mean identification of the lane's frozen core cost
family hprobFrozenCostFamily (the hprob frozen core cost written as the
fractional assignment cost of the simultaneous original frozen core matrix).

This module names that exact type as a standalone Prop and proves it from the
repo's tile Palm sample-law lane.  The composition traced and formalized is:

1. rootedTileCampbellMeanIdentification_of_palmSampleLaw
   (FinslerOriginalPressureLowerReadout): the identification of
   hprobFrozenCostFamily from the TilePalmSampleLaw family plus the lane's
   integrability, exchangeability, clipping-vanishing and plan-residual inputs.
   This is the composition that uses the fixed-pair transfer internally.
2. tilePalmSampleLaw_sceneCloud_of_rootedConvergence
   (FinslerOriginalFixedPairIdentificationClosed): the TilePalmSampleLaw family
   of the concrete scene-cloud lane from the single probabilistic input
   RootedTileMeanConvergence (the paper's Palm LLN, F16), through the fixed-pair
   transfer tileFixedPair_tendsto_of_rootedTileMeanConvergence.

Hence the identification closes with RootedTileMeanConvergence as the only
remaining probabilistic input; no other probabilistic hypothesis is needed.
The residual side conditions are exactly the analytic tile inputs already
consumed by the repo's reduced lower lane
(endgameLowerFields_actual_lane_reduced, FinslerOriginalEndgameLowerLaneInputsActual):
the per-tile integrability of the linear cost/probe and clipping integrands,
of the cost matrix entries and of the frozen tile cost, the masked-entry
exchangeability, the plan-residual vanishing, the clipping-correction vanishing,
and the context inputs G, hgt, hdecomp, hF, hcomplete, hu, ha, hinj.

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

/-! ## 1. The exact type of the lane hId binder, as a named Prop -/

/-- **The rooted tile Campbell mean identification of the hprob frozen core cost
family (the lane hId type).**  This is the named Prop whose instance is the hId
binder of endgameLowerFields_actual_lane_wired
(FinslerOriginalEndgameLowerLaneWired), at the concrete scene-cloud lane and with
the frozenCost specialized to hprobFrozenCostFamily (K := A union B). -/
def FrozenCampbellMeanIdentification
    (T : D.TaylorTiles ε) {A B : Set M}
    (Ω : ℕ → Type*) [∀ n, MeasurableSpace (Ω n)]
    (sample : ∀ n, Measure (Ω n))
    (X Y : ∀ n, Fin (n + 1) → Ω n → M) (scale : ℕ → ℝ)
    (base : ∀ n, Ω n → T.Index → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (Assign : ∀ n, Ω n → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (g : ((↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) → ℝ → (ℚ → M) → ℝ) : Prop :=
  RootedTileCampbellMeanIdentification P a κ lambda g q sample
    (hprobFrozenCostFamily (K := A ∪ B) T X Y base Assign scale) T.Index

/-- **The exact type of the lower lane's hId binder** (at the concrete
scene-cloud presentation), stated directly as the rooted tile Campbell mean
identification of hprobFrozenCostFamily. -/
def LowerLaneCampbellMeanIdentification
    (T : D.TaylorTiles ε) {A B : Set M}
    (pcloud qcloud : ∀ n, Fin (n + 1) → M)
    (base : ∀ n, Fin (n + 1) → T.Index → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (Assign : ∀ n, Fin (n + 1) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (g : ((↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) → ℝ → (ℚ → M) → ℝ) : Prop :=
  RootedTileCampbellMeanIdentification P a κ lambda g q sceneCloudSample
    (hprobFrozenCostFamily (K := A ∪ B) T (sceneCloudX pcloud) (sceneCloudY qcloud)
      base Assign tileScale) T.Index

/-- **The one remaining probabilistic input: the Palm LLN (paper F16).**  The
rooted tile mean convergence of the counted per-tile frozen means towards the
population tile values, for the concrete scene-cloud lane. -/
def LowerLaneRootedTileMeanLaw
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

/-- **The lane hId from the tile Palm sample law.**  This is the repo composition
of rootedTileCampbellMeanIdentification_of_palmSampleLaw
(FinslerOriginalPressureLowerReadout), restated with the frozenCost written as the
named family hprobFrozenCostFamily: the fixed-pair transfer is used inside that
producer, and every other input is an analytic lane side condition. -/
theorem frozenCampbellMeanIdentification_of_palmSampleLaw
    (T : D.TaylorTiles ε) {A B : Set M}
    (Ω : ℕ → Type*) [∀ n, MeasurableSpace (Ω n)]
    (sample : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (sample n)]
    (G : ℕ → (ℚ → M) → ℝ)
    (X Y : ∀ n, Fin (n + 1) → Ω n → M)
    (scale : ℕ → ℝ)
    (base : ∀ n, Ω n → T.Index → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    {Bp : ℝ} (hBp : 0 ≤ Bp)
    (hbase : ∀ (n : ℕ) (s : Ω n) (c' : T.Index) (i j : Fin (n + 1)),
      |base n s c' i j| ≤ Bp)
    (hintC : ∀ (f : (↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) (t : ℝ) (n : ℕ) (c : T.Index), Integrable
      (T.tileLinearCostIntegrand (ε := ε) f t X Y scale n c) (sample n))
    (hintP : ∀ (f : (↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) (t : ℝ) (n : ℕ) (c : T.Index), Integrable
      (T.tileLinearProbeIntegrand f t X Y
        (fun (f : (↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) t n s c' ↦ normalizedProbe (K := A ∪ B) base t n s c') n c) (sample n))
    (hintClip : ∀ (f : (↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) (t : ℝ) (n : ℕ) (c : T.Index), Integrable
      (T.tileClippingIntegrand (ε := ε) f t X Y scale
        (fun (f : (↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) t n s c' ↦ normalizedProbe (K := A ∪ B) base t n s c') n c) (sample n))
    (hPalm : ∀ (f : (↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) (t : ℝ) (c : T.Index),
      T.TilePalmSampleLaw f t sample X Y scale c
        (fun _ ↦ T.tilePopValue (P := P) (a := a) (κ := κ) (lambda := lambda)
          (q := q) G c))
    (hclip : ∀ (f : (↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) (t : ℝ) (c : T.Index),
      Tendsto (fun n ↦ T.tileFixedPairClippingCorrection f t sample X Y scale
        (fun (f : (↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) t n s c' ↦ normalizedProbe (K := A ∪ B) base t n s c') n c)
        atTop (𝓝 0))
    (Assign : ∀ n, Ω n → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (hintEntry : ∀ (f : (↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) (t : ℝ) (n : ℕ) (c : T.Index)
      (i j : Fin (n + 1)),
      Integrable (fun s ↦ T.tileCostMatrix f t X Y scale
        (fun (f : (↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) t n s c' ↦ normalizedProbe (K := A ∪ B) base t n s c') n c s i j)
        (sample n))
    (hExch : ∀ (f : (↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) (t : ℝ) (n : ℕ) (c : T.Index),
      MaskedEntryExchangeability (sample n) (T.tileCostMatrix f t X Y scale
        (fun (f : (↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) t n s c' ↦ normalizedProbe (K := A ∪ B) base t n s c') n c))
    (hintCost : ∀ (f : (↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) (t : ℝ) (n : ℕ) (c : T.Index),
      Integrable (fun s ↦ ∑ i, ∑ j, T.tileCostMatrix f t X Y scale
        (fun (f : (↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) t n s c' ↦ normalizedProbe (K := A ∪ B) base t n s c') n c s i j)
        (sample n))
    (hintRes : ∀ (f : (↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) (t : ℝ) (n : ℕ) (c : T.Index),
      Integrable (fun s ↦ ∑ i, ∑ j,
        (Assign n s i j - 1 / ((n + 1 : ℕ) : ℝ)) *
          T.tileCostMatrix f t X Y scale
            (fun (f : (↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) t n s c' ↦ normalizedProbe (K := A ∪ B) base t n s c') n c s i j)
        (sample n))
    (hresv : T.TilePlanResidualVanishing sample Assign X Y scale
      (fun (f : (↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) t n s c' ↦ normalizedProbe (K := A ∪ B) base t n s c'))
    (g : ((↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) → ℝ → (ℚ → M) → ℝ)
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _instTileCampbellFromPalmMetric : MetricSpace M := F.metricSpace;
      LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))
    (hint : ∀ (f : (↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) (t : ℝ) (n : ℕ) (c : T.Index),
      Integrable (T.tileFrozenCost (fun s i ↦ X n i s) (fun s i ↦ Y n i s)
        (fun s c' ↦ normalizedProbe (K := A ∪ B) base t n s c')
        (Assign n) (scale n) t c) (sample n))
    (hgt : ∀ (f : (↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) (t : ℝ),
      g f t = atlasPiecewiseRoot P a κ lambda G)
    (hdecomp : ∀ (f : (↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) (t : ℝ),
      (∑' j, ∫ z in populationSeedRootPiece P a κ lambda j,
          populationAtlasTheta P a κ lambda j z ^ (-2 / q) * G j z ∂lambda) =
        (∑ c : T.Index, T.tilePopValue (P := P) (a := a) (κ := κ)
          (lambda := lambda) (q := q) G c)) :
    FrozenCampbellMeanIdentification (P := P) (a := a) (κ := κ)
      (lambda := lambda) (q := q) T (A := A) (B := B) Ω sample X Y scale base
      Assign g := by
  show RootedTileCampbellMeanIdentification P a κ lambda g q sample
    (hprobFrozenCostFamily (K := A ∪ B) T X Y base Assign scale) T.Index
  exact rootedTileCampbellMeanIdentification_of_palmSampleLaw (T := T) sample G X Y
    scale base hBp hbase hintC hintP hintClip hPalm hclip Assign hintEntry hExch
    hintCost hintRes hresv g hF hcomplete hu ha hinj hint hgt hdecomp

/-! ## 3. The identification from the Palm LLN (RootedTileMeanConvergence) -/

/-- **The lane hId from the Palm LLN alone.**  The only probabilistic input is
LowerLaneRootedTileMeanLaw, i.e. the rooted tile mean convergence
RootedTileMeanConvergence of the counted per-tile frozen means to the population
tile values (paper F16).  The TilePalmSampleLaw family is derived from it through
the fixed-pair transfer tileFixedPair_tendsto_of_rootedTileMeanConvergence
(via tilePalmSampleLaw_sceneCloud_of_rootedConvergence), and the identification
then follows from frozenCampbellMeanIdentification_of_palmSampleLaw. -/
theorem frozenCampbellMeanIdentification_sceneCloud_of_rootedTileMeanConvergence
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
    (hconv : LowerLaneRootedTileMeanLaw (P := P) (a := a) (κ := κ)
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

/-- **The endgame lower lane with BOTH the derived frozen inputs and the hId binder.**

The same bundle as endgameLowerFields_actual_lane_wired, but its hId input is
produced from the Palm LLN (LowerLaneRootedTileMeanLaw) through
frozenCampbellMeanIdentification_sceneCloud_of_rootedTileMeanConvergence: the
TilePalmSampleLaw family is derived from RootedTileMeanConvergence by
tilePalmSampleLaw_sceneCloud_of_rootedConvergence (fixed-pair transfer), and the
identification of the hprob frozen core cost family follows from
rootedTileCampbellMeanIdentification_of_palmSampleLaw.  Thus the lower lane loses
the hId binder; the remaining inputs are the analytic core, the physical
population data, the sampling law, the geometric lane data, the readout
identification hread, and the tile integrability/exchangeability/clipping
side conditions together with the Palm LLN hconv. -/
noncomputable def endgameLowerFields_actual_lane_wired_of_rootedTileMeanConvergence
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
    {Bp Bphys : ℝ} (hBp : 0 ≤ Bp) (hBphys : 0 ≤ Bphys)
    (hbase : ∀ (n : ℕ) (s : Fin (n + 1)) (c' : T.Index) (i j : Fin (n + 1)),
      |base n s c' i j| ≤ Bp)
    (hphys : ∀ (n : ℕ) (c : T.Index) (s : Fin (n + 1)) (i j : Fin (n + 1)),
      (T.core c).frozenPhysicalCost (T.reference c)
        ((sceneCloudX pcloud) n i s) ((sceneCloudY qcloud) n j s) ≤ Bphys)
    (Assign : ∀ n, Fin (n + 1) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (hAssignDS : ∀ (n : ℕ) (s : Fin (n + 1)),
      Assign n s ∈ doublyStochastic ℝ (Fin (n + 1)))
    (hmeas : ∀ (f : (↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) (t : ℝ) (n : ℕ) (c : T.Index),
      Measurable (fun s : Fin (n + 1) ↦
        T.tileFrozenCost (fun s' i ↦ (sceneCloudX pcloud) n i s')
          (fun s' i ↦ (sceneCloudY qcloud) n i s')
          (fun s' c' ↦ normalizedProbe (K := A ∪ B) base t n s' c')
          (Assign n) (tileScale n) t c s))
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
        (Assign n s))
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
    (g : ((↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) → ℝ → (ℚ → M) → ℝ)
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
    (hconv : LowerLaneRootedTileMeanLaw (P := P) (a := a) (κ := κ)
      (lambda := lambda) (q := q) T (A := A) (B := B) pcloud qcloud base G)
    (Ψ : ((↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) → ℝ → ℝ)
    (hread : frozenPressureLower P a κ lambda g q = Ψ) :
    EndgameLowerFields F (physicalSourceProbability ωM dens₀)
      (physicalTargetProbability ωM dens₁) hA hB hμA hνB sceneCloudSample
      (sceneCloudX pcloud) (sceneCloudY qcloud) u := by
  exact endgameLowerFields_actual_lane_wired (T := T) hdim ωM dens₀ dens₁ hA hB
    hμA hνB pcloud qcloud hX hY hXi hYi hXlaw hYlaw hXY base hBp hBphys hbase
    hphys Assign hAssignDS hmeas hPopt hgeom hgh hF hcomplete hu ha hinj hε hε1
    hdist g (hId := frozenCampbellMeanIdentification_sceneCloud_of_rootedTileMeanConvergence
      (T := T) pcloud qcloud base hBp hbase hintC hintP hintLin hintClip hclip
      Assign hintEntry hExch hintCost hintRes hresv G g hF hcomplete hu ha hinj
      hint hgt hdecomp hconv) (hread := hread)

end OTSelector.Reconstruction
