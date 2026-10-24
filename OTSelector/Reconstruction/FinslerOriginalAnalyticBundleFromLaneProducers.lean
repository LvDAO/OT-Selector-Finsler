import OTSelector.Reconstruction.FinslerOriginalAnalyticLaneBundleReduction
import OTSelector.Reconstruction.FinslerOriginalCampbellMeanFromPalmBundle
import OTSelector.Reconstruction.FinslerOriginalPalmLLNAnalyticSideConditions

/-!
# The analytic lane bundles from the repo lane producers

## 1. Constructing the bundles from PalmLLNAnalyticBundle

PalmLLNAnalyticBundle.lane is a repo TileLaneInputs; its producer
tileLaneInputs_of_laneData (resp. tileLaneInputs_of_cellRefinement) already discharges

* hgt (rfl, g := atlasPiecewiseRoot),
* hExch (maskedEntryExchangeability_tileCostMatrix_forall, from the iid slot laws and
  pair independence),
* hresv (tilePlanResidualVanishing_of_scaleBounds, from the scale bounds),
* hdecomp (population covering identity, tileLaneInputs_of_cellRefinement);

the lane also carries hintEntry, hintCost, hintRes.  The bounded probe base and the
linear/probe/split/clipping integrabilities are PalmLLNAnalyticBundle fields
(Bp, hBp, hbase, hintC, hintP, hintLin, hintClip) and hint is its frozen integrability.

SceneCloudAnalyticLaneBundle_of_palmLLNAnalyticBundle therefore constructs the scene-cloud
analytic bundle from PalmLLNAnalyticBundle plus the lane plan identification
hAssign : palm.lane.Assign = uniformTilePlan, hε, hz0, hp: hExch, hresv, hintEntry,
hintCost, hintC, hintP, hintLin, hintClip are transported from the lane, and the
hintRes/hresv fields are rewritten along hAssign.

SceneCloudFullLowerLaneBundle_of_palmLLNAnalyticBundle additionally supplies g, hgt,
hdecomp (read off the lane) and hint (rewritten along hAssign), so the whole lower-lane
analytic block is one binder.

## 2. Sharpest identification theorems

* lowerLaneRootedTileMeanLaw_of_palmLLNAnalyticBundle: LowerLaneRootedTileMeanLaw from
  PalmLLNAnalyticBundle + hAssign/hε/hz0/hp + hlaw.
* frozenCampbellMeanIdentification_sceneCloud_of_palmLLNAnalyticBundle: the lane hId
  (RootedTileCampbellMeanIdentification) from the same data + the geometric lane data.

Fields discharged: hExch, hresv, hgt, hdecomp (lane producers), hintEntry, hintCost
(lane), hintC, hintP, hintLin, hintClip, hint, Bp/hBp/hbase (bundle fields).
Remaining explicit inputs: hAssign, hε, hz0, hp, hlaw (and the geometric lane data
hF, hcomplete, hu, ha, hinj for the identification theorem).

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
/-- **The scene-cloud analytic bundle from PalmLLNAnalyticBundle.**  The lane fields
(hintEntry, hExch, hintCost, hintRes, hresv), the bounded probe base and the four
integrability conditions come from the repo bundle; hε, hz0, hp are the remaining
retained-edge/window data. -/
noncomputable def SceneCloudAnalyticLaneBundle_of_palmLLNAnalyticBundle
    (T : D.TaylorTiles ε) {A B : Set M}
    (pcloud qcloud : ∀ n, Fin (n + 1) → M)
    (base : ∀ n, Fin (n + 1) → T.Index → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (G : ℕ → (ℚ → M) → ℝ)
    (palm : PalmLLNAnalyticBundle (P := P) (a := a) (κ := κ) (lambda := lambda)
      (D := D) (ε := ε) (q := q) (T := T) (A := A) (B := B) pcloud qcloud base G)
    (hAssign : palm.lane.Assign = uniformTilePlan (fun n ↦ Fin (n + 1)))
    (hε : ε ≤ 1 / 2)
    (hz₀ : ∀ c : T.Index, T.reference c ∈ (T.cover c.1).centers)
    (hp : ∀ (c : T.Index) (n : ℕ) (s : Fin (n + 1)),
      (u ((sceneCloudX pcloud) n ⟨0, Nat.succ_pos n⟩ s),
        u ((sceneCloudY qcloud) n ⟨0, Nat.succ_pos n⟩ s)) ∈ (T.core c).window.region) :
    SceneCloudAnalyticLaneBundle (P := P) (a := a) (κ := κ) (lambda := lambda)
      (D := D) (ε := ε) (T := T) (A := A) (B := B) pcloud qcloud base G :=
  { hintEntry := palm.lane.hintEntry
    hExch := palm.lane.hExch
    hintCost := palm.lane.hintCost
    hintRes := hAssign ▸ palm.lane.hintRes
    hresv := hAssign ▸ palm.lane.hresv
    Bp := palm.Bp
    hBp := palm.hBp
    hbase := palm.hbase
    hintC := palm.hintC
    hintP := palm.hintP
    hintLin := fun f t n c ↦ palm.hintLin f t c n
    hintClip := palm.hintClip
    hε := hε
    hz₀ := hz₀
    hp := hp }

/-- **The full lower-lane analytic bundle from PalmLLNAnalyticBundle.**  Adds g, hgt,
hdecomp (read off the lane, hence discharged by the lane producers) and hint. -/
noncomputable def SceneCloudFullLowerLaneBundle_of_palmLLNAnalyticBundle
    (T : D.TaylorTiles ε) {A B : Set M}
    (pcloud qcloud : ∀ n, Fin (n + 1) → M)
    (base : ∀ n, Fin (n + 1) → T.Index → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (G : ℕ → (ℚ → M) → ℝ)
    (palm : PalmLLNAnalyticBundle (P := P) (a := a) (κ := κ) (lambda := lambda)
      (D := D) (ε := ε) (q := q) (T := T) (A := A) (B := B) pcloud qcloud base G)
    (hAssign : palm.lane.Assign = uniformTilePlan (fun n ↦ Fin (n + 1)))
    (hε : ε ≤ 1 / 2)
    (hz₀ : ∀ c : T.Index, T.reference c ∈ (T.cover c.1).centers)
    (hp : ∀ (c : T.Index) (n : ℕ) (s : Fin (n + 1)),
      (u ((sceneCloudX pcloud) n ⟨0, Nat.succ_pos n⟩ s),
        u ((sceneCloudY qcloud) n ⟨0, Nat.succ_pos n⟩ s)) ∈ (T.core c).window.region) :
    SceneCloudFullLowerLaneBundle (P := P) (a := a) (κ := κ) (lambda := lambda)
      (D := D) (ε := ε) (q := q) (T := T) (A := A) (B := B) pcloud qcloud base G :=
  { analytic :=
      SceneCloudAnalyticLaneBundle_of_palmLLNAnalyticBundle (T := T) (A := A) (B := B)
        pcloud qcloud base G palm hAssign hε hz₀ hp
    g := palm.lane.g
    hgt := palm.lane.hgt
    hdecomp := palm.lane.hdecomp
    hint := hAssign ▸ palm.hint }

/-! ## 2. Sharpest consuming theorems -/

/-- **LowerLaneRootedTileMeanLaw from PalmLLNAnalyticBundle + hlaw.**  The analytic
bundle is constructed from the repo bundle, so hExch, hresv, hintEntry, hintCost,
hintC, hintP, hintLin, hintClip are discharged; only hAssign, hε, hz0, hp and the
Palm sample law remain. -/
theorem lowerLaneRootedTileMeanLaw_of_palmLLNAnalyticBundle
    (T : D.TaylorTiles ε) {A B : Set M}
    (pcloud qcloud : ∀ n, Fin (n + 1) → M)
    (base : ∀ n, Fin (n + 1) → T.Index → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (G : ℕ → (ℚ → M) → ℝ)
    (palm : PalmLLNAnalyticBundle (P := P) (a := a) (κ := κ) (lambda := lambda)
      (D := D) (ε := ε) (q := q) (T := T) (A := A) (B := B) pcloud qcloud base G)
    (hAssign : palm.lane.Assign = uniformTilePlan (fun n ↦ Fin (n + 1)))
    (hε : ε ≤ 1 / 2)
    (hz₀ : ∀ c : T.Index, T.reference c ∈ (T.cover c.1).centers)
    (hp : ∀ (c : T.Index) (n : ℕ) (s : Fin (n + 1)),
      (u ((sceneCloudX pcloud) n ⟨0, Nat.succ_pos n⟩ s),
        u ((sceneCloudY qcloud) n ⟨0, Nat.succ_pos n⟩ s)) ∈ (T.core c).window.region)
    (hlaw : ∀ (f : (↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) (t : ℝ) (c : T.Index),
      T.TilePalmSampleLaw (ε := ε) f t sceneCloudSample (sceneCloudX pcloud)
        (sceneCloudY qcloud) tileScale c
        (fun _ ↦ T.tilePopValue (P := P) (a := a) (κ := κ) (lambda := lambda) (q := q) G c)) :
    LowerLaneRootedTileMeanLaw (P := P) (a := a) (κ := κ) (lambda := lambda) (q := q)
      T (A := A) (B := B) pcloud qcloud base G :=
  lowerLaneRootedTileMeanLaw_of_palmSampleLaw_and_bundle (T := T) (A := A) (B := B)
    pcloud qcloud base G
    (SceneCloudAnalyticLaneBundle_of_palmLLNAnalyticBundle (T := T) (A := A) (B := B)
      pcloud qcloud base G palm hAssign hε hz₀ hp)
    hlaw

/-- **The lane hId from PalmLLNAnalyticBundle + hlaw (sharpest form).**  The full
lower-lane analytic block is one bundle constructed from the repo bundle; only the
plan identification hAssign, the retained-edge data hε/hz0/hp, the geometric lane data
and the Palm sample law remain. -/
theorem frozenCampbellMeanIdentification_sceneCloud_of_palmLLNAnalyticBundle
    (T : D.TaylorTiles ε) {A B : Set M}
    (pcloud qcloud : ∀ n, Fin (n + 1) → M)
    (base : ∀ n, Fin (n + 1) → T.Index → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (G : ℕ → (ℚ → M) → ℝ)
    (palm : PalmLLNAnalyticBundle (P := P) (a := a) (κ := κ) (lambda := lambda)
      (D := D) (ε := ε) (q := q) (T := T) (A := A) (B := B) pcloud qcloud base G)
    (hAssign : palm.lane.Assign = uniformTilePlan (fun n ↦ Fin (n + 1)))
    (hε : ε ≤ 1 / 2)
    (hz₀ : ∀ c : T.Index, T.reference c ∈ (T.cover c.1).centers)
    (hp : ∀ (c : T.Index) (n : ℕ) (s : Fin (n + 1)),
      (u ((sceneCloudX pcloud) n ⟨0, Nat.succ_pos n⟩ s),
        u ((sceneCloudY qcloud) n ⟨0, Nat.succ_pos n⟩ s)) ∈ (T.core c).window.region)
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
    RootedTileCampbellMeanIdentification P a κ lambda palm.lane.g q sceneCloudSample
      (hprobFrozenCostFamily (K := A ∪ B) T (sceneCloudX pcloud) (sceneCloudY qcloud)
        base (uniformTilePlan (fun n ↦ Fin (n + 1))) tileScale) T.Index :=
  frozenCampbellMeanIdentification_sceneCloud_of_fullBundle (T := T) (A := A) (B := B)
    pcloud qcloud base G
    (SceneCloudFullLowerLaneBundle_of_palmLLNAnalyticBundle (T := T) (A := A) (B := B)
      pcloud qcloud base G palm hAssign hε hz₀ hp)
    hF hcomplete hu ha hinj hlaw
