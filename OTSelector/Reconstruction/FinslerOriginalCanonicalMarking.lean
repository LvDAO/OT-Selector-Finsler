import OTSelector.Reconstruction.FinslerOriginalBaseFromProbeFam
import OTSelector.Reconstruction.FinslerOriginalAtlasSceneBridge

/-!
# The canonical marking: removing the marking input from the base-from-probeFam route

## The repository's canonical marking

The repo recodes every physical clock of the limiting rooted scene as the marked
cloud point `(height, bridgeUnitMarkZero)`:

* `bridgeUnitMarkZero : UnitMark` is the canonical zero mark
  (FinslerOriginalAtlasSceneBridge.lean:102), "the zero mark of the abstract marked
  cloud carrier (the two clocks of a physical Palm pair are recoded with this mark)";
* `rootedSceneFrozenEdge` and the rooted-edge measurability chain
  (FinslerOriginalRootedEdgeMeasurability, FinslerOriginalRootedDataMeasurability)
  evaluate every probe on `MarkedCloudPoint` pairs `(height, bridgeUnitMarkZero)`.

Hence the canonical marking of a physical point is

  canonicalMarking u x = (u x, bridgeUnitMarkZero) : MarkedCloudPoint = R x UnitMark.

## Measurability is derived, not assumed

  measurable_canonicalMarking          : Measurable u -> Measurable (canonicalMarking u)
  measurable_canonicalMarking_of_lipschitz :
      (LipschitzWith 1 u) -> Measurable (canonicalMarking u)

the second from the repo lemma `measurable_u_of_lipschitz`
(FinslerOriginalTilePairRegularity) applied to the lane's height Lipschitz binder.

## The four probe-kernel hypotheses at the canonical marking

Instantiated from FinslerOriginalBaseFromProbeFam with marking := canonicalMarking u:

  canonicalProbeKernel_hprobePair : rfl;
  canonicalProbeKernel_hΨ         : from hprobe + derived marking measurability;
  canonicalProbeKernel_hΨb        : from hprobe_bound.

Hence the four probe-kernel hypotheses of V17 (probeKernel, hprobePair, hΨ, hΨb) are
consequences of probeFam, hprobe, hprobe_bound (and the geometric binders already in
V17), with the probe choice probeOfTile : T.Index -> FinalProbeSpace A B as data.
The 6-field bundle, the hId and the lower-lane mean law are re-derived with the
marking derived rather than bound.

## V18 canonical-base signature

V18 = V17 with the binder row

  (probeKernel : ...) (hprobePair) (hΨ) (hΨb)

replaced by

  (probeOfTile : T.Index -> FinalProbeSpace A B),

the abstract `base` fixed to `canonicalBase u T probeFam probeOfTile pcloud qcloud`,
and the lane's probe-kernel data supplied by canonicalProbeKernel_hprobePair /
canonicalProbeKernel_hΨ / canonicalProbeKernel_hΨb (or directly by
frozenCampbellMeanIdentification_sceneCloud_of_canonicalMarking).

No sorry, admit or added axiom occurs.
-/

open Set Function Matrix Filter MeasureTheory ProbabilityTheory Manifold Module
  OTSelector.Probability
open OTSelector.PointProcess
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

/-! ## 1. The canonical marking and its measurability -/

/-- The canonical marking of a physical point: its height and the canonical zero mark
of the abstract marked cloud carrier (repo convention `bridgeUnitMarkZero`). -/
def canonicalMarking (u : M → ℝ) : M → MarkedCloudPoint :=
  fun x ↦ (u x, bridgeUnitMarkZero)

/-- Measurability of the canonical marking from measurability of the height. -/
theorem measurable_canonicalMarking {u : M → ℝ} (hu : Measurable u) :
    Measurable (canonicalMarking u) :=
  hu.prodMk measurable_const

/-- **Measurability of the canonical marking derived from the repo height lemma**
`measurable_u_of_lipschitz`. -/
theorem measurable_canonicalMarking_of_lipschitz
    (hu : let _instTileCampbellFromPalmMetric : MetricSpace M := F.metricSpace;
      LipschitzWith 1 u) :
    Measurable (canonicalMarking u) :=
  measurable_canonicalMarking (measurable_u_of_lipschitz hu)

/-- Pair measurability of the canonical marking. -/
theorem measurable_canonicalMarking_pair {u : M → ℝ} (hu : Measurable u) :
    Measurable (fun p : M × M ↦ (canonicalMarking u p.1, canonicalMarking u p.2)) :=
  ((measurable_canonicalMarking hu).comp measurable_fst).prodMk
    ((measurable_canonicalMarking hu).comp measurable_snd)

/-! ## 2. The canonical base and probe kernel -/

/-- The canonical lane base at the canonical marking. -/
noncomputable def canonicalBase (u : M → ℝ) (T : D.TaylorTiles ε) {A B : Set M}
    (probeFam : FinalProbeSpace A B → ℕ → (ℚ → M) →
      MarkedCloudPoint → MarkedCloudPoint → ℝ)
    (probeOfTile : T.Index → FinalProbeSpace A B)
    (pcloud qcloud : ∀ n, Fin (n + 1) → M) :
    ∀ n, Fin (n + 1) → T.Index → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
  baseOfProbeFam (T := T) probeFam probeOfTile (canonicalMarking u) pcloud qcloud

/-- The canonical probe kernel at the canonical marking. -/
noncomputable def canonicalProbeKernel (u : M → ℝ) (T : D.TaylorTiles ε) {A B : Set M}
    (probeFam : FinalProbeSpace A B → ℕ → (ℚ → M) →
      MarkedCloudPoint → MarkedCloudPoint → ℝ)
    (probeOfTile : T.Index → FinalProbeSpace A B) :
    ((↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) → ℝ → ℕ → T.Index → M × M → ℝ :=
  probeKernelOfProbeFam (T := T) probeFam probeOfTile (canonicalMarking u)

/-- **hprobePair at the canonical marking, by rfl.** -/
theorem canonicalProbeKernel_hprobePair (T : D.TaylorTiles ε) {A B : Set M}
    (probeFam : FinalProbeSpace A B → ℕ → (ℚ → M) →
      MarkedCloudPoint → MarkedCloudPoint → ℝ)
    (probeOfTile : T.Index → FinalProbeSpace A B)
    (pcloud qcloud : ∀ n, Fin (n + 1) → M) :
    ∀ (f : (↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) (t : ℝ) (n : ℕ) (c : T.Index)
      (s : Fin (n + 1)) (i j : Fin (n + 1)),
      normalizedProbe (K := A ∪ B)
          (canonicalBase u T probeFam probeOfTile pcloud qcloud) t n s c i j =
        canonicalProbeKernel u T probeFam probeOfTile f t n c
          ((sceneCloudX pcloud) n i s, (sceneCloudY qcloud) n j s) :=
  probeKernelOfProbeFam_hprobePair (T := T) probeFam probeOfTile (canonicalMarking u)
    pcloud qcloud

/-- **hΨ at the canonical marking**, from hprobe and the derived marking measurability. -/
theorem canonicalProbeKernel_hΨ (T : D.TaylorTiles ε) {A B : Set M}
    (probeFam : FinalProbeSpace A B → ℕ → (ℚ → M) →
      MarkedCloudPoint → MarkedCloudPoint → ℝ)
    (probeOfTile : T.Index → FinalProbeSpace A B)
    (hprobe : ∀ (φ : FinalProbeSpace A B) (j : ℕ) (z : ℚ → M),
      Measurable (fun p : MarkedCloudPoint × MarkedCloudPoint => probeFam φ j z p.1 p.2))
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _instTileCampbellFromPalmMetric : MetricSpace M := F.metricSpace;
      LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))
    (f : (↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) (t : ℝ) (n : ℕ) (c : T.Index) :
    Measurable (T.tilePairKernel c (tileScale n) t
      (canonicalProbeKernel u T probeFam probeOfTile f t n c)) :=
  probeKernelOfProbeFam_hΨ (T := T) probeFam probeOfTile (canonicalMarking u)
    (measurable_canonicalMarking_of_lipschitz hu) hprobe hF hcomplete hu ha hinj f t n c

/-- **hΨb at the canonical marking**, from hprobe_bound. -/
theorem canonicalProbeKernel_hΨb (T : D.TaylorTiles ε) {A B : Set M}
    (probeFam : FinalProbeSpace A B → ℕ → (ℚ → M) →
      MarkedCloudPoint → MarkedCloudPoint → ℝ)
    (probeOfTile : T.Index → FinalProbeSpace A B)
    (hprobe_bound : ∃ Gc : ℝ, ∀ (φ : FinalProbeSpace A B) (j : ℕ) (z : ℚ → M)
      (x y : MarkedCloudPoint), |probeFam φ j z x y| ≤ Gc)
    (f : (↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) (t : ℝ) (n : ℕ) (c : T.Index) :
    ∃ B : ℝ, ∀ p : M × M,
      |T.tilePairKernel c (tileScale n) t
        (canonicalProbeKernel u T probeFam probeOfTile f t n c) p| ≤ B :=
  probeKernelOfProbeFam_hΨb (T := T) probeFam probeOfTile (canonicalMarking u)
    (Gc := Classical.choose hprobe_bound) (Classical.choose_spec hprobe_bound) f t n c

/-! ## 3. The bundles and bridges at the canonical marking -/

/-- The canonical-base version of the probe-kernel bundle. -/
noncomputable def sceneCloudProbeKernelLaneBundle_of_canonicalBase
    (T : D.TaylorTiles ε) {A B : Set M}
    (pcloud qcloud : ∀ n, Fin (n + 1) → M)
    (G : ℕ → (ℚ → M) → ℝ)
    (probeFam : FinalProbeSpace A B → ℕ → (ℚ → M) →
      MarkedCloudPoint → MarkedCloudPoint → ℝ)
    (probeOfTile : T.Index → FinalProbeSpace A B)
    (bundle : SceneCloudThreeFieldLaneBundle (P := P) (a := a) (κ := κ)
      (lambda := lambda) (D := D) (ε := ε) (T := T) (A := A) (B := B)
      pcloud qcloud
      (canonicalBase u T probeFam probeOfTile pcloud qcloud) G) :
    SceneCloudProbeKernelLaneBundle (P := P) (a := a) (κ := κ) (lambda := lambda)
      (D := D) (ε := ε) (T := T) (A := A) (B := B) pcloud qcloud
      (canonicalBase u T probeFam probeOfTile pcloud qcloud) G :=
  sceneCloudProbeKernelLaneBundle_of_threeFieldLane (T := T) (A := A) (B := B)
    pcloud qcloud (canonicalBase u T probeFam probeOfTile pcloud qcloud) G bundle

/-- **The 6-field bundle from the 3-field bundle at the canonical base**, with the
marking and its measurability derived (no marking binder). -/
noncomputable def sceneCloudHz0FreeLaneBundle_of_canonicalMarking
    (T : D.TaylorTiles ε) {A B : Set M}
    (pcloud qcloud : ∀ n, Fin (n + 1) → M)
    (G : ℕ → (ℚ → M) → ℝ)
    (probeFam : FinalProbeSpace A B → ℕ → (ℚ → M) →
      MarkedCloudPoint → MarkedCloudPoint → ℝ)
    (probeOfTile : T.Index → FinalProbeSpace A B)
    (bundle : SceneCloudThreeFieldLaneBundle (P := P) (a := a) (κ := κ)
      (lambda := lambda) (D := D) (ε := ε) (T := T) (A := A) (B := B)
      pcloud qcloud
      (canonicalBase u T probeFam probeOfTile pcloud qcloud) G)
    (hprobe : ∀ (φ : FinalProbeSpace A B) (j : ℕ) (z : ℚ → M),
      Measurable (fun p : MarkedCloudPoint × MarkedCloudPoint => probeFam φ j z p.1 p.2))
    (hprobe_bound : ∃ Gc : ℝ, ∀ (φ : FinalProbeSpace A B) (j : ℕ) (z : ℚ → M)
      (x y : MarkedCloudPoint), |probeFam φ j z x y| ≤ Gc)
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _instTileCampbellFromPalmMetric : MetricSpace M := F.metricSpace;
      LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))
    {μ ν : ℕ → Measure M} [∀ n, IsProbabilityMeasure (μ n)]
    [∀ n, IsProbabilityMeasure (ν n)]
    (hXi : ∀ n, iIndepFun ((sceneCloudX pcloud) n) (sceneCloudSample n))
    (hYi : ∀ n, iIndepFun ((sceneCloudY qcloud) n) (sceneCloudSample n))
    (hXlaw : ∀ (n : ℕ) (i : Fin (n + 1)),
      (sceneCloudSample n).map ((sceneCloudX pcloud) n i) = μ n)
    (hYlaw : ∀ (n : ℕ) (j : Fin (n + 1)),
      (sceneCloudSample n).map ((sceneCloudY qcloud) n j) = ν n)
    (hXY : ∀ n, IndepFun (fun ξ i ↦ (sceneCloudX pcloud) n i ξ)
      (fun ξ j ↦ (sceneCloudY qcloud) n j ξ) (sceneCloudSample n)) :
    SceneCloudHz0FreeLaneBundle (P := P) (a := a) (κ := κ) (lambda := lambda)
      (D := D) (ε := ε) (T := T) (A := A) (B := B) pcloud qcloud
      (canonicalBase u T probeFam probeOfTile pcloud qcloud) G :=
  sceneCloudHz0FreeLaneBundle_of_endgameProbe (T := T) (A := A) (B := B)
    pcloud qcloud G probeFam probeOfTile (canonicalMarking u) bundle
    (measurable_canonicalMarking_of_lipschitz hu) hprobe hprobe_bound
    hF hcomplete hu ha hinj hXi hYi hXlaw hYlaw hXY

/-- **The lane hId at the canonical marking** (marking derived; V18 shape). -/
theorem frozenCampbellMeanIdentification_sceneCloud_of_canonicalMarking
    (T : D.TaylorTiles ε) {A B : Set M}
    (pcloud qcloud : ∀ n, Fin (n + 1) → M)
    (G : ℕ → (ℚ → M) → ℝ)
    (probeFam : FinalProbeSpace A B → ℕ → (ℚ → M) →
      MarkedCloudPoint → MarkedCloudPoint → ℝ)
    (probeOfTile : T.Index → FinalProbeSpace A B)
    (bundle : SceneCloudThreeFieldLaneBundle (P := P) (a := a) (κ := κ)
      (lambda := lambda) (D := D) (ε := ε) (T := T) (A := A) (B := B)
      pcloud qcloud
      (canonicalBase u T probeFam probeOfTile pcloud qcloud) G)
    (hprobe : ∀ (φ : FinalProbeSpace A B) (j : ℕ) (z : ℚ → M),
      Measurable (fun p : MarkedCloudPoint × MarkedCloudPoint => probeFam φ j z p.1 p.2))
    (hprobe_bound : ∃ Gc : ℝ, ∀ (φ : FinalProbeSpace A B) (j : ℕ) (z : ℚ → M)
      (x y : MarkedCloudPoint), |probeFam φ j z x y| ≤ Gc)
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _instTileCampbellFromPalmMetric : MetricSpace M := F.metricSpace;
      LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))
    {μ ν : ℕ → Measure M} [∀ n, IsProbabilityMeasure (μ n)]
    [∀ n, IsProbabilityMeasure (ν n)]
    (hXi : ∀ n, iIndepFun ((sceneCloudX pcloud) n) (sceneCloudSample n))
    (hYi : ∀ n, iIndepFun ((sceneCloudY qcloud) n) (sceneCloudSample n))
    (hXlaw : ∀ (n : ℕ) (i : Fin (n + 1)),
      (sceneCloudSample n).map ((sceneCloudX pcloud) n i) = μ n)
    (hYlaw : ∀ (n : ℕ) (j : Fin (n + 1)),
      (sceneCloudSample n).map ((sceneCloudY qcloud) n j) = ν n)
    (hXY : ∀ n, IndepFun (fun ξ i ↦ (sceneCloudX pcloud) n i ξ)
      (fun ξ j ↦ (sceneCloudY qcloud) n j ξ) (sceneCloudSample n))
    (g : ((↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) → ℝ → (ℚ → M) → ℝ)
    (hgt : ∀ (f : (↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) (t : ℝ),
      g f t = atlasPiecewiseRoot P a κ lambda G)
    (hdecomp : ∀ (f : (↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) (t : ℝ),
      (∑' j, ∫ z in populationSeedRootPiece P a κ lambda j,
          populationAtlasTheta P a κ lambda j z ^ (-2 / q) * G j z ∂lambda) =
        (∑ c : T.Index, T.tilePopValue (P := P) (a := a) (κ := κ)
          (lambda := lambda) (q := q) G c))
    (hlaw : ∀ (f : (↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) (t : ℝ) (c : T.Index),
      T.TilePalmSampleLaw (ε := ε) f t sceneCloudSample (sceneCloudX pcloud)
        (sceneCloudY qcloud) tileScale c
        (fun _ ↦ T.tilePopValue (P := P) (a := a) (κ := κ) (lambda := lambda) (q := q) G c)) :
    RootedTileCampbellMeanIdentification P a κ lambda g q sceneCloudSample
      (hprobFrozenCostFamily (K := A ∪ B) T (sceneCloudX pcloud) (sceneCloudY qcloud)
        (canonicalBase u T probeFam probeOfTile pcloud qcloud)
        (uniformTilePlan (fun n ↦ Fin (n + 1))) tileScale) T.Index :=
  frozenCampbellMeanIdentification_sceneCloud_of_threeFieldBundle
    (T := T) (A := A) (B := B) pcloud qcloud G probeFam probeOfTile
    (canonicalMarking u) bundle (measurable_canonicalMarking_of_lipschitz hu)
    hprobe hprobe_bound hF hcomplete hu ha hinj hXi hYi hXlaw hYlaw hXY
    g hgt hdecomp hlaw

/-- **The lower-lane mean law at the canonical marking** (marking derived; V18 shape). -/
theorem lowerLaneRootedTileMeanLaw_of_canonicalMarking
    (T : D.TaylorTiles ε) {A B : Set M}
    (pcloud qcloud : ∀ n, Fin (n + 1) → M)
    (G : ℕ → (ℚ → M) → ℝ)
    (probeFam : FinalProbeSpace A B → ℕ → (ℚ → M) →
      MarkedCloudPoint → MarkedCloudPoint → ℝ)
    (probeOfTile : T.Index → FinalProbeSpace A B)
    (bundle : SceneCloudThreeFieldLaneBundle (P := P) (a := a) (κ := κ)
      (lambda := lambda) (D := D) (ε := ε) (T := T) (A := A) (B := B)
      pcloud qcloud
      (canonicalBase u T probeFam probeOfTile pcloud qcloud) G)
    (hprobe : ∀ (φ : FinalProbeSpace A B) (j : ℕ) (z : ℚ → M),
      Measurable (fun p : MarkedCloudPoint × MarkedCloudPoint => probeFam φ j z p.1 p.2))
    (hprobe_bound : ∃ Gc : ℝ, ∀ (φ : FinalProbeSpace A B) (j : ℕ) (z : ℚ → M)
      (x y : MarkedCloudPoint), |probeFam φ j z x y| ≤ Gc)
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _instTileCampbellFromPalmMetric : MetricSpace M := F.metricSpace;
      LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))
    {μ ν : ℕ → Measure M} [∀ n, IsProbabilityMeasure (μ n)]
    [∀ n, IsProbabilityMeasure (ν n)]
    (hXi : ∀ n, iIndepFun ((sceneCloudX pcloud) n) (sceneCloudSample n))
    (hYi : ∀ n, iIndepFun ((sceneCloudY qcloud) n) (sceneCloudSample n))
    (hXlaw : ∀ (n : ℕ) (i : Fin (n + 1)),
      (sceneCloudSample n).map ((sceneCloudX pcloud) n i) = μ n)
    (hYlaw : ∀ (n : ℕ) (j : Fin (n + 1)),
      (sceneCloudSample n).map ((sceneCloudY qcloud) n j) = ν n)
    (hXY : ∀ n, IndepFun (fun ξ i ↦ (sceneCloudX pcloud) n i ξ)
      (fun ξ j ↦ (sceneCloudY qcloud) n j ξ) (sceneCloudSample n))
    (hlaw : ∀ (f : (↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) (t : ℝ) (c : T.Index),
      T.TilePalmSampleLaw (ε := ε) f t sceneCloudSample (sceneCloudX pcloud)
        (sceneCloudY qcloud) tileScale c
        (fun _ ↦ T.tilePopValue (P := P) (a := a) (κ := κ) (lambda := lambda) (q := q) G c)) :
    LowerLaneRootedTileMeanLaw (P := P) (a := a) (κ := κ) (lambda := lambda) (q := q)
      T (A := A) (B := B) pcloud qcloud
      (canonicalBase u T probeFam probeOfTile pcloud qcloud) G :=
  lowerLaneRootedTileMeanLaw_of_threeFieldBundle (T := T) (A := A) (B := B)
    pcloud qcloud G probeFam probeOfTile (canonicalMarking u) bundle
    (measurable_canonicalMarking_of_lipschitz hu) hprobe hprobe_bound
    hF hcomplete hu ha hinj hXi hYi hXlaw hYlaw hXY hlaw
