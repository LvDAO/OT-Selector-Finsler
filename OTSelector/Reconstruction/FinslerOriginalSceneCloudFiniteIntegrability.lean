import OTSelector.Reconstruction.FinslerOriginalAnalyticBundleFromLaneProducers

/-!
# Finite integrability on the scene cloud: the 15-bundle collapses to 8 fields

The scene cloud sample is the uniform empirical measure on the finite type Fin (n + 1)
(sceneCloudSample n = empiricalMeasure id), which is a probability measure.  Hence:

* EVERY real-valued function is integrable (Integrable.of_finite), so all seven
  integrability fields of SceneCloudAnalyticLaneBundle (hintEntry, hintCost, hintRes,
  hintC, hintP, hintLin, hintClip) are discharged with no hypotheses;
* EVERY function into any MeasurableSpace is measurable (measurable_of_countable), so the
  V11 lane measurability binders hX and hY are discharged;
* in particular the V11 frozen integrability binder hfrozen_int is discharged.

The only remaining content of SceneCloudAnalyticLaneBundle is collected in
SceneCloudNonIntegrabilityLaneBundle: Bp, hBp, hbase, hExch, hresv, hEps, hz0, hp (8
fields).  From it we rebuild the analytic bundle, the full lower-lane bundle (with hint
also discharged), and the two consuming theorems.

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

/-! ## 1. Finite-sample integrability and measurability -/

/-- On the finite scene-cloud sample space every real-valued function is integrable. -/
theorem integrable_sceneCloudSample (n : ℕ) (g : Fin (n + 1) → ℝ) :
    Integrable g (sceneCloudSample n) :=
  Integrable.of_finite

/-- On the finite scene-cloud sample space every function is measurable. -/
theorem measurable_sceneCloud_slot (n : ℕ) {α : Type*} [MeasurableSpace α]
    (g : Fin (n + 1) → α) : Measurable g :=
  measurable_of_countable g

/-- The V11 source-cloud measurability binder hX is discharged. -/
theorem sceneCloudX_measurable (pcloud : ∀ n, Fin (n + 1) → M) :
    ∀ (n : ℕ) (i : Fin (n + 1)), Measurable ((sceneCloudX pcloud) n i) :=
  fun n i ↦ measurable_sceneCloud_slot n _

/-- The V11 target-cloud measurability binder hY is discharged. -/
theorem sceneCloudY_measurable (qcloud : ∀ n, Fin (n + 1) → M) :
    ∀ (n : ℕ) (i : Fin (n + 1)), Measurable ((sceneCloudY qcloud) n i) :=
  fun n i ↦ measurable_sceneCloud_slot n _

/-- The V11 frozen integrability binder hfrozen_int is discharged. -/
theorem hprobFrozenCostFamily_integrable
    (T : D.TaylorTiles ε) {A B : Set M}
    (pcloud qcloud : ∀ n, Fin (n + 1) → M)
    (base : ∀ n, Fin (n + 1) → T.Index → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (G : ℕ → (ℚ → M) → ℝ)
    (f : (↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) (t : ℝ) (n : ℕ) :
    Integrable (hprobFrozenCostFamily (K := A ∪ B) T (sceneCloudX pcloud)
      (sceneCloudY qcloud) base (uniformTilePlan (fun n ↦ Fin (n + 1)))
      tileScale f t n) (sceneCloudSample n) :=
  integrable_sceneCloudSample n _
/-! ## 2. The non-integrability bundle: 8 fields only -/

/-- **The scene-cloud analytic lane bundle with all integrability fields removed.**
Only the bounded probe base, the masked-entry exchangeability, the plan-residual
vanishing and the retained-edge window/scale data remain. -/
structure SceneCloudNonIntegrabilityLaneBundle
    (T : D.TaylorTiles ε) {A B : Set M}
    (pcloud qcloud : ∀ n, Fin (n + 1) → M)
    (base : ∀ n, Fin (n + 1) → T.Index → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (G : ℕ → (ℚ → M) → ℝ) : Type _ where
  hExch : ∀ (f : (↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) (t : ℝ) (n : ℕ) (c : T.Index),
    MaskedEntryExchangeability (sceneCloudSample n)
      (T.tileCostMatrix f t (sceneCloudX pcloud) (sceneCloudY qcloud) tileScale
        (fun f t n s c' ↦ normalizedProbe (K := A ∪ B) base t n s c') n c)
  hresv : T.TilePlanResidualVanishing sceneCloudSample
    (uniformTilePlan (fun n ↦ Fin (n + 1))) (sceneCloudX pcloud) (sceneCloudY qcloud)
    tileScale
    (fun (f : (↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) t n s c' ↦
      normalizedProbe (K := A ∪ B) base t n s c')
  Bp : ℝ
  hBp : 0 ≤ Bp
  hbase : ∀ (n : ℕ) (s : Fin (n + 1)) (c' : T.Index) (i j : Fin (n + 1)),
    |base n s c' i j| ≤ Bp
  hε : ε ≤ 1 / 2
  hz₀ : ∀ c : T.Index, T.reference c ∈ (T.cover c.1).centers
  hp : ∀ (c : T.Index) (n : ℕ) (s : Fin (n + 1)),
    (u ((sceneCloudX pcloud) n ⟨0, Nat.succ_pos n⟩ s),
      u ((sceneCloudY qcloud) n ⟨0, Nat.succ_pos n⟩ s)) ∈ (T.core c).window.region

/-- **The analytic bundle from the non-integrability bundle.**  All seven
integrability fields are filled by integrable_sceneCloudSample. -/
noncomputable def sceneCloudAnalyticLaneBundle_of_nonIntegrability
    (T : D.TaylorTiles ε) {A B : Set M}
    (pcloud qcloud : ∀ n, Fin (n + 1) → M)
    (base : ∀ n, Fin (n + 1) → T.Index → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (G : ℕ → (ℚ → M) → ℝ)
    (bundle : SceneCloudNonIntegrabilityLaneBundle (P := P) (a := a) (κ := κ)
      (lambda := lambda) (D := D) (ε := ε) (T := T) (A := A) (B := B)
      pcloud qcloud base G) :
    SceneCloudAnalyticLaneBundle (P := P) (a := a) (κ := κ) (lambda := lambda)
      (D := D) (ε := ε) (T := T) (A := A) (B := B) pcloud qcloud base G :=
  { hintEntry := fun f t n c i j ↦ integrable_sceneCloudSample n _
    hExch := bundle.hExch
    hintCost := fun f t n c ↦ integrable_sceneCloudSample n _
    hintRes := fun f t n c ↦ integrable_sceneCloudSample n _
    hresv := bundle.hresv
    Bp := bundle.Bp
    hBp := bundle.hBp
    hbase := bundle.hbase
    hintC := fun f t n c ↦ integrable_sceneCloudSample n _
    hintP := fun f t n c ↦ integrable_sceneCloudSample n _
    hintLin := fun f t n c ↦ integrable_sceneCloudSample n _
    hintClip := fun f t n c ↦ integrable_sceneCloudSample n _
    hε := bundle.hε
    hz₀ := bundle.hz₀
    hp := bundle.hp }

/-- **The full lower-lane bundle from the non-integrability bundle.**  hint is also
discharged by integrable_sceneCloudSample; only g, hgt and hdecomp are supplied. -/
noncomputable def sceneCloudFullLowerLaneBundle_of_nonIntegrability
    (T : D.TaylorTiles ε) {A B : Set M}
    (pcloud qcloud : ∀ n, Fin (n + 1) → M)
    (base : ∀ n, Fin (n + 1) → T.Index → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (G : ℕ → (ℚ → M) → ℝ)
    (bundle : SceneCloudNonIntegrabilityLaneBundle (P := P) (a := a) (κ := κ)
      (lambda := lambda) (D := D) (ε := ε) (T := T) (A := A) (B := B)
      pcloud qcloud base G)
    (g : ((↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) → ℝ → (ℚ → M) → ℝ)
    (hgt : ∀ (f : (↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) (t : ℝ),
      g f t = atlasPiecewiseRoot P a κ lambda G)
    (hdecomp : ∀ (f : (↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) (t : ℝ),
      (∑' j, ∫ z in populationSeedRootPiece P a κ lambda j,
          populationAtlasTheta P a κ lambda j z ^ (-2 / q) * G j z ∂lambda) =
        (∑ c : T.Index, T.tilePopValue (P := P) (a := a) (κ := κ)
          (lambda := lambda) (q := q) G c)) :
    SceneCloudFullLowerLaneBundle (P := P) (a := a) (κ := κ) (lambda := lambda)
      (D := D) (ε := ε) (q := q) (T := T) (A := A) (B := B) pcloud qcloud base G :=
  { analytic :=
      sceneCloudAnalyticLaneBundle_of_nonIntegrability (T := T) (A := A) (B := B)
        pcloud qcloud base G bundle
    g := g
    hgt := hgt
    hdecomp := hdecomp
    hint := fun f t n c ↦ integrable_sceneCloudSample n _ }

/-! ## 3. The consuming theorems with the 8-field bundle -/

/-- **LowerLaneRootedTileMeanLaw from the 8-field bundle + hlaw.** -/
theorem lowerLaneRootedTileMeanLaw_of_nonIntegrabilityBundle
    (T : D.TaylorTiles ε) {A B : Set M}
    (pcloud qcloud : ∀ n, Fin (n + 1) → M)
    (base : ∀ n, Fin (n + 1) → T.Index → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (G : ℕ → (ℚ → M) → ℝ)
    (bundle : SceneCloudNonIntegrabilityLaneBundle (P := P) (a := a) (κ := κ)
      (lambda := lambda) (D := D) (ε := ε) (T := T) (A := A) (B := B)
      pcloud qcloud base G)
    (hlaw : ∀ (f : (↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) (t : ℝ) (c : T.Index),
      T.TilePalmSampleLaw (ε := ε) f t sceneCloudSample (sceneCloudX pcloud)
        (sceneCloudY qcloud) tileScale c
        (fun _ ↦ T.tilePopValue (P := P) (a := a) (κ := κ) (lambda := lambda) (q := q) G c)) :
    LowerLaneRootedTileMeanLaw (P := P) (a := a) (κ := κ) (lambda := lambda) (q := q)
      T (A := A) (B := B) pcloud qcloud base G :=
  lowerLaneRootedTileMeanLaw_of_palmSampleLaw_and_bundle (T := T) (A := A) (B := B)
    pcloud qcloud base G
    (sceneCloudAnalyticLaneBundle_of_nonIntegrability (T := T) (A := A) (B := B)
      pcloud qcloud base G bundle)
    hlaw

/-- **The lane hId from the 8-field bundle + hlaw.**  hint and all seven integrability
side conditions are discharged by finite integrability; hclip is derived downstream. -/
theorem frozenCampbellMeanIdentification_sceneCloud_of_nonIntegrabilityBundle
    (T : D.TaylorTiles ε) {A B : Set M}
    (pcloud qcloud : ∀ n, Fin (n + 1) → M)
    (base : ∀ n, Fin (n + 1) → T.Index → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (G : ℕ → (ℚ → M) → ℝ)
    (bundle : SceneCloudNonIntegrabilityLaneBundle (P := P) (a := a) (κ := κ)
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
  frozenCampbellMeanIdentification_sceneCloud_of_fullBundle (T := T) (A := A) (B := B)
    pcloud qcloud base G
    (sceneCloudFullLowerLaneBundle_of_nonIntegrability (T := T) (A := A) (B := B)
      pcloud qcloud base G bundle g hgt hdecomp)
    hF hcomplete hu ha hinj hlaw
