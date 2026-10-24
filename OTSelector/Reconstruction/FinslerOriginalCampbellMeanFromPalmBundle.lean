import OTSelector.Reconstruction.FinslerOriginalAnalyticLaneBundleReduction
import OTSelector.Reconstruction.FinslerOriginalTileCampbellMeanFromPalm
import OTSelector.Reconstruction.FinslerOriginalPalmLLNAnalyticSideConditions

/-!
# The lane hId from the Palm sample law and ONE analytic bundle

## 1. Dropping hclip and the redundant analytic binders

V8 consumed frozenCampbellMeanIdentification_sceneCloud_of_rootedTileMeanConvergencePalmSide,
which re-requires hclip plus all analytic integrability/exchangeability binders even
though its hconv is LowerLaneRootedTileMeanLaw.  In FinslerOriginalTileCampbellMeanFromPalm
the theorem frozenCampbellMeanIdentification_sceneCloud_of_rootedTileMeanConvergence needs,
besides hconv, only hint (frozen cost integrability), hgt and hdecomp.

Since lowerLaneRootedTileMeanLaw_of_palmSampleLaw_and_bundle produces hconv from the Palm
sample law family hlaw and the single SceneCloudAnalyticLaneBundle, the whole lower-lane
analytic block is now one structure: every integrability/exchangeability side condition
comes from the bundle, and hclip is DERIVED inside (from hε, hz0, hp and the bounded
probe base: tileFixedPairClippingCorrection_sceneCloud_tendsto_zero).

## 2. Declarations

* frozenCampbellMeanIdentification_sceneCloud_of_palmSampleLaw_and_bundle :
  hlaw + SceneCloudAnalyticLaneBundle + hint + hgt + hdecomp (and the geometric lane
  data) -> RootedTileCampbellMeanIdentification; hclip is not a binder.
* SceneCloudFullLowerLaneBundle : the analytic bundle extended with g, hgt, hdecomp and
  hint, so the remaining lower-lane analytic block is 1 binder.
* frozenCampbellMeanIdentification_sceneCloud_of_fullBundle :
  hlaw + SceneCloudFullLowerLaneBundle (and the geometric lane data) ->
  RootedTileCampbellMeanIdentification, with g read off the bundle.

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
/-! ## 1. The hId from the Palm sample law and one analytic bundle (no hclip binder) -/

/-- **The lane hId from hlaw + one analytic bundle.**  hclip is derived, not assumed:
the clipping correction vanishes from the bundle's hε, hz0, hp and the bounded probe
base.  The remaining inputs are hint, hgt, hdecomp and the geometric lane data. -/
theorem frozenCampbellMeanIdentification_sceneCloud_of_palmSampleLaw_and_bundle
    (T : D.TaylorTiles ε) {A B : Set M}
    (pcloud qcloud : ∀ n, Fin (n + 1) → M)
    (base : ∀ n, Fin (n + 1) → T.Index → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (G : ℕ → (ℚ → M) → ℝ)
    (bundle : SceneCloudAnalyticLaneBundle (P := P) (a := a) (κ := κ) (lambda := lambda)
      (D := D) (ε := ε) (T := T) (A := A) (B := B) pcloud qcloud base G)
    (g : ((↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) → ℝ → (ℚ → M) → ℝ)
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _instTileCampbellFromPalmMetric : MetricSpace M := F.metricSpace;
      LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))
    (hint : ∀ (f : (↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) (t : ℝ) (n : ℕ) (c : T.Index),
      Integrable (T.tileFrozenCost (fun s i ↦ (sceneCloudX pcloud) n i s)
        (fun s i ↦ (sceneCloudY qcloud) n i s)
        (fun s c' ↦ normalizedProbe (K := A ∪ B) base t n s c')
        ((uniformTilePlan (fun n ↦ Fin (n + 1))) n) (tileScale n) t c) (sceneCloudSample n))
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
        base (uniformTilePlan (fun n ↦ Fin (n + 1))) tileScale) T.Index := by
  have hclip : ∀ (f : (↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) (t : ℝ) (c : T.Index),
      Tendsto (fun n ↦ T.tileFixedPairClippingCorrection f t sceneCloudSample
        (sceneCloudX pcloud) (sceneCloudY qcloud) tileScale
        (fun (f : (↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) t n s c' ↦
          normalizedProbe (K := A ∪ B) base t n s c') n c) atTop (𝓝 0) :=
    fun f t c ↦
      tileFixedPairClippingCorrection_sceneCloud_tendsto_zero (T := T) (A := A) (B := B)
        pcloud qcloud base bundle.hBp bundle.hbase bundle.hintClip bundle.hε bundle.hz₀
        bundle.hp f t c
  have hconv : LowerLaneRootedTileMeanLaw (P := P) (a := a) (κ := κ)
      (lambda := lambda) (q := q) T (A := A) (B := B) pcloud qcloud base G :=
    lowerLaneRootedTileMeanLaw_of_palmSampleLaw_and_bundle (T := T) (A := A) (B := B)
      pcloud qcloud base G bundle hlaw
  exact frozenCampbellMeanIdentification_sceneCloud_of_rootedTileMeanConvergence
    (T := T) (A := A) (B := B) pcloud qcloud base bundle.hBp bundle.hbase
    bundle.hintC bundle.hintP (fun f t c n ↦ bundle.hintLin f t n c) bundle.hintClip
    hclip (uniformTilePlan (fun n ↦ Fin (n + 1))) bundle.hintEntry bundle.hExch
    bundle.hintCost bundle.hintRes bundle.hresv G g hF hcomplete hu ha hinj hint hgt
    hdecomp hconv

/-! ## 2. Extending the bundle with g, hgt, hdecomp, hint -/

/-- **The full lower-lane analytic bundle.**  SceneCloudAnalyticLaneBundle extended
with the readout family g, the atlas identification hgt, the population covering
identity hdecomp and the frozen cost integrability hint.  The entire remaining
lower-lane analytic block is one binder. -/
structure SceneCloudFullLowerLaneBundle
    (T : D.TaylorTiles ε) {A B : Set M}
    (pcloud qcloud : ∀ n, Fin (n + 1) → M)
    (base : ∀ n, Fin (n + 1) → T.Index → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (G : ℕ → (ℚ → M) → ℝ) : Type _ where
  analytic : SceneCloudAnalyticLaneBundle (P := P) (a := a) (κ := κ)
    (lambda := lambda) (D := D) (ε := ε) (T := T) (A := A) (B := B)
    pcloud qcloud base G
  g : ((↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) → ℝ → (ℚ → M) → ℝ
  hgt : ∀ (f : (↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) (t : ℝ),
    g f t = atlasPiecewiseRoot P a κ lambda G
  hdecomp : ∀ (f : (↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) (t : ℝ),
    (∑' j, ∫ z in populationSeedRootPiece P a κ lambda j,
        populationAtlasTheta P a κ lambda j z ^ (-2 / q) * G j z ∂lambda) =
      (∑ c : T.Index, T.tilePopValue (P := P) (a := a) (κ := κ)
        (lambda := lambda) (q := q) G c)
  hint : ∀ (f : (↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) (t : ℝ) (n : ℕ) (c : T.Index),
    Integrable (T.tileFrozenCost (fun s i ↦ (sceneCloudX pcloud) n i s)
      (fun s i ↦ (sceneCloudY qcloud) n i s)
      (fun s c' ↦ normalizedProbe (K := A ∪ B) base t n s c')
      ((uniformTilePlan (fun n ↦ Fin (n + 1))) n) (tileScale n) t c) (sceneCloudSample n)

/-- **The lane hId from hlaw + ONE full bundle.**  g, hgt, hdecomp and hint are read
off the bundle; hclip is still derived (from the analytic part), never assumed. -/
theorem frozenCampbellMeanIdentification_sceneCloud_of_fullBundle
    (T : D.TaylorTiles ε) {A B : Set M}
    (pcloud qcloud : ∀ n, Fin (n + 1) → M)
    (base : ∀ n, Fin (n + 1) → T.Index → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (G : ℕ → (ℚ → M) → ℝ)
    (bundle : SceneCloudFullLowerLaneBundle (P := P) (a := a) (κ := κ)
      (lambda := lambda) (D := D) (ε := ε) (q := q) (T := T) (A := A) (B := B)
      pcloud qcloud base G)
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
    RootedTileCampbellMeanIdentification P a κ lambda bundle.g q sceneCloudSample
      (hprobFrozenCostFamily (K := A ∪ B) T (sceneCloudX pcloud) (sceneCloudY qcloud)
        base (uniformTilePlan (fun n ↦ Fin (n + 1))) tileScale) T.Index :=
  frozenCampbellMeanIdentification_sceneCloud_of_palmSampleLaw_and_bundle
    (T := T) (A := A) (B := B) pcloud qcloud base G bundle.analytic bundle.g
    hF hcomplete hu ha hinj bundle.hint bundle.hgt bundle.hdecomp hlaw
