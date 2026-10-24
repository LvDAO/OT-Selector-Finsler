import OTSelector.Reconstruction.FinslerOriginalHz0FreeLaneBundle
import OTSelector.Reconstruction.FinslerOriginalLaneBaseFieldsReduction

/-!
# The 3-field probe-kernel lane bundle

Combining the wave-36/37 reductions: sceneCloudAnalyticLaneBundle (15 fields) -> 8 ->
7 -> 6 -> 4 -> **3 fields**.  SceneCloudProbeKernelLaneBundle keeps exactly

* hbdd : LaneBaseBound A B T pcloud qcloud base G  (the single existential bound
  replacing Bp / hBp / hbase, FinslerOriginalLaneBaseFieldsReduction:78);
* hε : ε ≤ 1 / 2;
* hp : forall c n s, (u (X n 0 s), u (Y n 0 s)) in (T.core c).window.region.

hExch is REMOVED: it is derived from the lane iid binders and the probe-kernel data by
maskedEntryExchangeability_tileCostMatrix_forall.  hz0 is REMOVED: it is
reference_mem_coverCenters T (free).  Bp / hBp / hbase are collapsed into hbdd and
recovered by Classical.choose.

## Exactly which probe-kernel hypotheses are needed

To derive hExch one needs (beyond the lane iid/law binders hXi hYi hXlaw hYlaw hXY):
* probeKernel : the pair kernel of the probe matrix;
* hprobePair : normalizedProbe base t n s c i j = probeKernel f t n c (X n i s, Y n j s);
* hPsi : Measurable (T.tilePairKernel c (tileScale n) t (probeKernel f t n c));
* hPsiB : a uniform bound for T.tilePairKernel c (tileScale n) t (probeKernel f t n c).

These four are NOT among the V11 endgame binders: V11 supplies the probe family
probeFam, its pair measurability hprobe and its uniform bound hprobe_bound
(FinslerOriginalPaperTheoremFinalV11:282-289).  hPsi and hPsiB follow from
hprobe/hprobe_bound once the probe kernel is the pair evaluation of probeFam, and
hprobePair is then the definitional unfolding of normalizedProbe/base; but that step
needs the base-from-probeFam definition, which is a remaining producer, so the four
curried hypotheses are explicit here.

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
/-! ## 1. The 3-field bundle -/

/-- **The probe-kernel lane bundle.**  Only the base bound, the retained-edge scale
condition and the window condition remain; hExch and hz0 are derived. -/
structure SceneCloudProbeKernelLaneBundle
    (T : D.TaylorTiles ε) {A B : Set M}
    (pcloud qcloud : ∀ n, Fin (n + 1) → M)
    (base : ∀ n, Fin (n + 1) → T.Index → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (G : ℕ → (ℚ → M) → ℝ) : Type _ where
  hbdd : LaneBaseBound A B T pcloud qcloud base G
  hε : ε ≤ 1 / 2
  hp : ∀ (c : T.Index) (n : ℕ) (s : Fin (n + 1)),
    (u ((sceneCloudX pcloud) n ⟨0, Nat.succ_pos n⟩ s),
      u ((sceneCloudY qcloud) n ⟨0, Nat.succ_pos n⟩ s)) ∈ (T.core c).window.region

/-! ## 2. Filling hExch and hbdd back in -/

/-- **The 6-field bundle from the 3-field bundle.**  hExch is derived by
maskedEntryExchangeability_tileCostMatrix_forall (slot measurability from
measurable_sceneCloud_slot, pairwise independence from hXY via IndepFun.comp with
measurable_pi_apply), and Bp / hBp / hbase come from hbdd by Classical.choose. -/
noncomputable def sceneCloudHz0FreeLaneBundle_of_probeKernelLane
    (T : D.TaylorTiles ε) {A B : Set M}
    (pcloud qcloud : ∀ n, Fin (n + 1) → M)
    (base : ∀ n, Fin (n + 1) → T.Index → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (G : ℕ → (ℚ → M) → ℝ)
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
    (probeKernel : ((↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) → ℝ → ℕ → T.Index → M × M → ℝ)
    (hprobePair : ∀ (f : (↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) (t : ℝ) (n : ℕ) (c : T.Index)
      (s : Fin (n + 1)) (i j : Fin (n + 1)),
      normalizedProbe (K := A ∪ B) base t n s c i j =
        probeKernel f t n c ((sceneCloudX pcloud) n i s, (sceneCloudY qcloud) n j s))
    (hΨ : ∀ (f : (↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) (t : ℝ) (n : ℕ) (c : T.Index),
      Measurable (T.tilePairKernel c (tileScale n) t (probeKernel f t n c)))
    (hΨb : ∀ (f : (↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) (t : ℝ) (n : ℕ) (c : T.Index),
      ∃ B : ℝ, ∀ p : M × M,
        |T.tilePairKernel c (tileScale n) t (probeKernel f t n c) p| ≤ B)
    (bundle : SceneCloudProbeKernelLaneBundle (P := P) (a := a) (κ := κ)
      (lambda := lambda) (D := D) (ε := ε) (T := T) (A := A) (B := B)
      pcloud qcloud base G) :
    SceneCloudHz0FreeLaneBundle (P := P) (a := a) (κ := κ) (lambda := lambda)
      (D := D) (ε := ε) (T := T) (A := A) (B := B) pcloud qcloud base G :=
  { hExch := fun f t n c ↦
      maskedEntryExchangeability_tileCostMatrix_forall (T := T) (K := A ∪ B)
        sceneCloudSample (sceneCloudX pcloud) (sceneCloudY qcloud) tileScale
        (fun f t n s c' ↦ normalizedProbe (K := A ∪ B) base t n s c')
        (μ := μ) (ν := ν)
        (fun n i ↦ measurable_sceneCloud_slot n ((sceneCloudX pcloud) n i))
        (fun n j ↦ measurable_sceneCloud_slot n ((sceneCloudY qcloud) n j))
        hXlaw hYlaw
        (fun n i j ↦ (hXY n).comp (measurable_pi_apply i) (measurable_pi_apply j))
        probeKernel hprobePair hΨ hΨb f t n c
    Bp := Classical.choose bundle.hbdd
    hBp := (Classical.choose_spec bundle.hbdd).1
    hbase := (Classical.choose_spec bundle.hbdd).2
    hε := bundle.hε
    hp := bundle.hp }

/-! ## 3. The bridges -/

/-- **LowerLaneRootedTileMeanLaw from the 3-field bundle + hlaw.** -/
theorem lowerLaneRootedTileMeanLaw_of_probeKernelLaneBundle
    (T : D.TaylorTiles ε) {A B : Set M}
    (pcloud qcloud : ∀ n, Fin (n + 1) → M)
    (base : ∀ n, Fin (n + 1) → T.Index → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (G : ℕ → (ℚ → M) → ℝ)
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
    (probeKernel : ((↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) → ℝ → ℕ → T.Index → M × M → ℝ)
    (hprobePair : ∀ (f : (↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) (t : ℝ) (n : ℕ) (c : T.Index)
      (s : Fin (n + 1)) (i j : Fin (n + 1)),
      normalizedProbe (K := A ∪ B) base t n s c i j =
        probeKernel f t n c ((sceneCloudX pcloud) n i s, (sceneCloudY qcloud) n j s))
    (hΨ : ∀ (f : (↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) (t : ℝ) (n : ℕ) (c : T.Index),
      Measurable (T.tilePairKernel c (tileScale n) t (probeKernel f t n c)))
    (hΨb : ∀ (f : (↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) (t : ℝ) (n : ℕ) (c : T.Index),
      ∃ B : ℝ, ∀ p : M × M,
        |T.tilePairKernel c (tileScale n) t (probeKernel f t n c) p| ≤ B)
    (bundle : SceneCloudProbeKernelLaneBundle (P := P) (a := a) (κ := κ)
      (lambda := lambda) (D := D) (ε := ε) (T := T) (A := A) (B := B)
      pcloud qcloud base G)
    (hlaw : ∀ (f : (↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) (t : ℝ) (c : T.Index),
      T.TilePalmSampleLaw (ε := ε) f t sceneCloudSample (sceneCloudX pcloud)
        (sceneCloudY qcloud) tileScale c
        (fun _ ↦ T.tilePopValue (P := P) (a := a) (κ := κ) (lambda := lambda) (q := q) G c)) :
    LowerLaneRootedTileMeanLaw (P := P) (a := a) (κ := κ) (lambda := lambda) (q := q)
      T (A := A) (B := B) pcloud qcloud base G :=
  lowerLaneRootedTileMeanLaw_of_hz0FreeBundle (T := T) (A := A) (B := B)
    pcloud qcloud base G
    (sceneCloudHz0FreeLaneBundle_of_probeKernelLane (T := T) (A := A) (B := B)
      pcloud qcloud base G hXi hYi hXlaw hYlaw hXY probeKernel hprobePair hΨ hΨb bundle)
    hlaw

/-- **The lane hId from the 3-field bundle + hlaw.** -/
theorem frozenCampbellMeanIdentification_sceneCloud_of_probeKernelLaneBundle
    (T : D.TaylorTiles ε) {A B : Set M}
    (pcloud qcloud : ∀ n, Fin (n + 1) → M)
    (base : ∀ n, Fin (n + 1) → T.Index → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (G : ℕ → (ℚ → M) → ℝ)
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
    (probeKernel : ((↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) → ℝ → ℕ → T.Index → M × M → ℝ)
    (hprobePair : ∀ (f : (↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) (t : ℝ) (n : ℕ) (c : T.Index)
      (s : Fin (n + 1)) (i j : Fin (n + 1)),
      normalizedProbe (K := A ∪ B) base t n s c i j =
        probeKernel f t n c ((sceneCloudX pcloud) n i s, (sceneCloudY qcloud) n j s))
    (hΨ : ∀ (f : (↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) (t : ℝ) (n : ℕ) (c : T.Index),
      Measurable (T.tilePairKernel c (tileScale n) t (probeKernel f t n c)))
    (hΨb : ∀ (f : (↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) (t : ℝ) (n : ℕ) (c : T.Index),
      ∃ B : ℝ, ∀ p : M × M,
        |T.tilePairKernel c (tileScale n) t (probeKernel f t n c) p| ≤ B)
    (bundle : SceneCloudProbeKernelLaneBundle (P := P) (a := a) (κ := κ)
      (lambda := lambda) (D := D) (ε := ε) (T := T) (A := A) (B := B)
      pcloud qcloud base G)
    (g : ((↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) → ℝ → (ℚ → M) → ℝ)
    (hgt : ∀ (f : (↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) (t : ℝ),
      g f t = atlasPiecewiseRoot P a κ lambda G)
    (hdecomp : ∀ (f : (↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) (t : ℝ),
      (∑' j, ∫ z in populationSeedRootPiece P a κ lambda j,
          populationAtlasTheta P a κ lambda j z ^ (-2 / q) * G j z ∂lambda) =
        (∑ c : T.Index, T.tilePopValue (P := P) (a := a) (κ := κ)
          (lambda := lambda) (q := q) G c))
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _instTileCampbellFromPalmMetric : MetricSpace M := F.metricSpace;
      LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))
    (hlaw : ∀ (f : (↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) (t : ℝ) (c : T.Index),
      T.TilePalmSampleLaw (ε := ε) f t sceneCloudSample (sceneCloudX pcloud)
        (sceneCloudY qcloud) tileScale c
        (fun _ ↦ T.tilePopValue (P := P) (a := a) (κ := κ) (lambda := lambda) (q := q) G c)) :
    RootedTileCampbellMeanIdentification P a κ lambda g q sceneCloudSample
      (hprobFrozenCostFamily (K := A ∪ B) T (sceneCloudX pcloud) (sceneCloudY qcloud)
        base (uniformTilePlan (fun n ↦ Fin (n + 1))) tileScale) T.Index :=
  frozenCampbellMeanIdentification_sceneCloud_of_hz0FreeBundle (T := T) (A := A) (B := B)
    pcloud qcloud base G
    (sceneCloudHz0FreeLaneBundle_of_probeKernelLane (T := T) (A := A) (B := B)
      pcloud qcloud base G hXi hYi hXlaw hYlaw hXY probeKernel hprobePair hΨ hΨb bundle)
    g hgt hdecomp hF hcomplete hu ha hinj hlaw
