import OTSelector.Reconstruction.FinslerOriginalSceneCloudFiniteIntegrability

/-!
# Discharging the uniform-plan residual: 8 fields down to 7

## 1. TilePlanResidualVanishing at the uniform plan - CLOSED unconditionally

uniformTilePlan (fun n => Fin (n+1)) n s i j is definitionally 1 / ((n+1 : ℕ) : ℝ)
(FinslerOriginalFixedPairIdentificationClosed, def uniformTilePlan), while
TilePlanResidualVanishing is the convergence of (1/(n+1)) times the plan residual
integral of (A n s i j - 1/(n+1)) * tileCostMatrix.  For the uniform plan the entry
difference is zero, so the plan residual part is identically zero and the convergence
is the constant zero sequence.  Hence no scale/optimality bounds are needed at the
uniform plan: tilePlanResidualVanishing_uniformTilePlan is unconditional.

## 2. hExch - NOT discharged by hXi/hYi/hXlaw/hYlaw/hXY

The repo producer maskedEntryExchangeability_tileCostMatrix_forall needs, besides the
slot laws hXlaw/hYlaw and pairwise independence hpair, the probe pair-functionality
(hprobePair), the probe measurability (hPsi) and the probe boundedness (hPsiB).  The
lane measurabilities hX/hY and the pairwise independence hpair follow from hXY (project
the independent families), but the probe-side fields are additional kernel data, so
hExch is retained in the minimal bundle.

## 3. Deliverables

SceneCloudMinimalLaneBundle keeps only 7 fields (hExch, Bp, hBp, hbase, hEps, hz0, hp);
sceneCloudNonIntegrabilityLaneBundle_of_minimal rebuilds the 8-field bundle with hresv
discharged; frozenCampbellMeanIdentification_sceneCloud_of_minimalBundle and
lowerLaneRootedTileMeanLaw_of_minimalBundle bridge to the consuming theorems of
FinslerOriginalSceneCloudFiniteIntegrability.

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
/-! ## 1. The uniform-plan residual vanishes unconditionally -/

/-- **TilePlanResidualVanishing at the uniform plan, unconditionally.**  For
A := uniformTilePlan the plan residual part is identically zero (each entry difference
A n s i j - 1/(n+1) is zero), so the scaled residual converges to 0. -/
theorem tilePlanResidualVanishing_uniformTilePlan
    (T : D.TaylorTiles ε) {A B : Set M}
    (Ω : ℕ → Type*) [∀ n, MeasurableSpace (Ω n)]
    (sample : ∀ n, Measure (Ω n))
    (X Y : ∀ n, Fin (n + 1) → Ω n → M)
    (scale : ℕ → ℝ)
    (hprobe : ((↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) → ℝ → ∀ n, Ω n → T.Index →
      Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) :
    T.TilePlanResidualVanishing (K := A ∪ B) sample (uniformTilePlan Ω) X Y scale
      hprobe := by
  intro f t c
  have hzero : ∀ n, (1 / ((n + 1 : ℕ) : ℝ)) *
      planResidualTilePart (T := T) sample (uniformTilePlan Ω) f t X Y scale
        hprobe n c = 0 := by
    intro n
    have hpart : planResidualTilePart (T := T) sample (uniformTilePlan Ω) f t X Y
        scale hprobe n c = 0 := by
      simp only [planResidualTilePart]
      have hfun : (fun s ↦ ∑ i, ∑ j,
          (uniformTilePlan Ω n s i j - 1 / ((n + 1 : ℕ) : ℝ)) *
            T.tileCostMatrix f t X Y scale hprobe n c s i j) = fun _ ↦ (0 : ℝ) := by
        funext s
        simp [uniformTilePlan]
      rw [hfun]
      simp
    rw [hpart, mul_zero]
  rw [show (fun n ↦ (1 / ((n + 1 : ℕ) : ℝ)) *
      planResidualTilePart (T := T) sample (uniformTilePlan Ω) f t X Y scale
        hprobe n c) = fun _ ↦ (0 : ℝ) from funext hzero]
  exact tendsto_const_nhds

/-! ## 2. The minimal bundle: 7 fields -/

/-- **The scene-cloud non-integrability bundle with hresv discharged.**  Only the
masked-entry exchangeability, the bounded probe base and the retained-edge window/scale
data remain (7 fields). -/
structure SceneCloudMinimalLaneBundle
    (T : D.TaylorTiles ε) {A B : Set M}
    (pcloud qcloud : ∀ n, Fin (n + 1) → M)
    (base : ∀ n, Fin (n + 1) → T.Index → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (G : ℕ → (ℚ → M) → ℝ) : Type _ where
  hExch : ∀ (f : (↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) (t : ℝ) (n : ℕ) (c : T.Index),
    MaskedEntryExchangeability (sceneCloudSample n)
      (T.tileCostMatrix f t (sceneCloudX pcloud) (sceneCloudY qcloud) tileScale
        (fun f t n s c' ↦ normalizedProbe (K := A ∪ B) base t n s c') n c)
  Bp : ℝ
  hBp : 0 ≤ Bp
  hbase : ∀ (n : ℕ) (s : Fin (n + 1)) (c' : T.Index) (i j : Fin (n + 1)),
    |base n s c' i j| ≤ Bp
  hε : ε ≤ 1 / 2
  hz₀ : ∀ c : T.Index, T.reference c ∈ (T.cover c.1).centers
  hp : ∀ (c : T.Index) (n : ℕ) (s : Fin (n + 1)),
    (u ((sceneCloudX pcloud) n ⟨0, Nat.succ_pos n⟩ s),
      u ((sceneCloudY qcloud) n ⟨0, Nat.succ_pos n⟩ s)) ∈ (T.core c).window.region

/-- **The 8-field non-integrability bundle from the 7-field minimal bundle.**  hresv is
discharged by tilePlanResidualVanishing_uniformTilePlan. -/
noncomputable def sceneCloudNonIntegrabilityLaneBundle_of_minimal
    (T : D.TaylorTiles ε) {A B : Set M}
    (pcloud qcloud : ∀ n, Fin (n + 1) → M)
    (base : ∀ n, Fin (n + 1) → T.Index → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (G : ℕ → (ℚ → M) → ℝ)
    (bundle : SceneCloudMinimalLaneBundle (P := P) (a := a) (κ := κ)
      (lambda := lambda) (D := D) (ε := ε) (T := T) (A := A) (B := B)
      pcloud qcloud base G) :
    SceneCloudNonIntegrabilityLaneBundle (P := P) (a := a) (κ := κ)
      (lambda := lambda) (D := D) (ε := ε) (T := T) (A := A) (B := B)
      pcloud qcloud base G :=
  { hExch := bundle.hExch
    hresv :=
      tilePlanResidualVanishing_uniformTilePlan (T := T) (A := A) (B := B)
        (fun n ↦ Fin (n + 1)) sceneCloudSample (sceneCloudX pcloud)
        (sceneCloudY qcloud) tileScale
        (fun f t n s c' ↦ normalizedProbe (K := A ∪ B) base t n s c')
    Bp := bundle.Bp
    hBp := bundle.hBp
    hbase := bundle.hbase
    hε := bundle.hε
    hz₀ := bundle.hz₀
    hp := bundle.hp }

/-! ## 3. The bridges -/

/-- **LowerLaneRootedTileMeanLaw from the 7-field minimal bundle + hlaw.** -/
theorem lowerLaneRootedTileMeanLaw_of_minimalBundle
    (T : D.TaylorTiles ε) {A B : Set M}
    (pcloud qcloud : ∀ n, Fin (n + 1) → M)
    (base : ∀ n, Fin (n + 1) → T.Index → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (G : ℕ → (ℚ → M) → ℝ)
    (bundle : SceneCloudMinimalLaneBundle (P := P) (a := a) (κ := κ)
      (lambda := lambda) (D := D) (ε := ε) (T := T) (A := A) (B := B)
      pcloud qcloud base G)
    (hlaw : ∀ (f : (↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) (t : ℝ) (c : T.Index),
      T.TilePalmSampleLaw (ε := ε) f t sceneCloudSample (sceneCloudX pcloud)
        (sceneCloudY qcloud) tileScale c
        (fun _ ↦ T.tilePopValue (P := P) (a := a) (κ := κ) (lambda := lambda) (q := q) G c)) :
    LowerLaneRootedTileMeanLaw (P := P) (a := a) (κ := κ) (lambda := lambda) (q := q)
      T (A := A) (B := B) pcloud qcloud base G :=
  lowerLaneRootedTileMeanLaw_of_nonIntegrabilityBundle (T := T) (A := A) (B := B)
    pcloud qcloud base G
    (sceneCloudNonIntegrabilityLaneBundle_of_minimal (T := T) (A := A) (B := B)
      pcloud qcloud base G bundle)
    hlaw

/-- **The lane hId from the 7-field minimal bundle + hlaw.**  All integrabilities,
hint, hclip and hresv are discharged internally. -/
theorem frozenCampbellMeanIdentification_sceneCloud_of_minimalBundle
    (T : D.TaylorTiles ε) {A B : Set M}
    (pcloud qcloud : ∀ n, Fin (n + 1) → M)
    (base : ∀ n, Fin (n + 1) → T.Index → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (G : ℕ → (ℚ → M) → ℝ)
    (bundle : SceneCloudMinimalLaneBundle (P := P) (a := a) (κ := κ)
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
  frozenCampbellMeanIdentification_sceneCloud_of_nonIntegrabilityBundle (T := T)
    (A := A) (B := B) pcloud qcloud base G
    (sceneCloudNonIntegrabilityLaneBundle_of_minimal (T := T) (A := A) (B := B)
      pcloud qcloud base G bundle)
    g hgt hdecomp hF hcomplete hu ha hinj hlaw
