import OTSelector.Reconstruction.FinslerOriginalMinimalLaneBundleHz0Reduction

/-!
# The 6-field lane bundle: hz0 removed outright

hz0 : forall c : T.Index, T.reference c in (T.cover c.1).centers is definitionally
(T.partition c.1).center_mem c.2 (FiniteRootNeighborhoodPartition.center_mem), so it is
free and is removed from the bundle: SceneCloudHz0FreeLaneBundle has exactly 6 fields
(hExch, Bp, hBp, hbase, hEps, hp).  sceneCloudMinimalLaneBundle_of_hz0Free reconstructs
the 7-field bundle by filling hz0 with reference_mem_coverCenters, and the two bridges
reach the sharpest hId and lower-lane mean-law theorems.  The field chain is
15 -> 8 -> 7 -> 6.

## Exact field types

* hExch : forall (f : ((A ∪ B) × (A ∪ B)) →ᵇ ℝ) (t : ℝ) (n) (c : T.Index),
    MaskedEntryExchangeability (sceneCloudSample n)
      (T.tileCostMatrix f t (sceneCloudX pcloud) (sceneCloudY qcloud) tileScale
        (fun f t n s c' => normalizedProbe base t n s c') n c);
* Bp : ℝ;  hBp : 0 ≤ Bp;
* hbase : forall n s c' i j, |base n s c' i j| ≤ Bp;
* hEps : ε ≤ 1 / 2;
* hp : forall c n s, (u (X n 0 s), u (Y n 0 s)) in (T.core c).window.region.

## Further reduction of Bp / hBp / hbase

The three fields are equivalent to the single existential field
  exists Bp : ℝ, 0 ≤ Bp and forall n s c' i j, |base n s c' i j| ≤ Bp
(hbase_bdd_of_hz0FreeBundle extracts it; sceneCloudHz0FreeLaneBundle_of_bddBase
rebuilds the bundle from it).  Bp is an actual bound on the infinite family of finite
probe matrices, so it cannot be dropped without a probe-boundedness producer: the
probe families are data, not structure of T.  hEps is the Taylor accuracy condition
(no bound on ε is a field of TaylorTiles, only cover/partition are), and hp is the
paper's retained-edge window condition on the physical lane; neither has a producer in
the tile structure, so both remain.

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
/-! ## 1. The 6-field bundle -/

/-- **The scene-cloud minimal lane bundle with hz0 removed.**  hz0 is free
(reference_mem_coverCenters), so only these 6 fields carry content. -/
structure SceneCloudHz0FreeLaneBundle
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
  hp : ∀ (c : T.Index) (n : ℕ) (s : Fin (n + 1)),
    (u ((sceneCloudX pcloud) n ⟨0, Nat.succ_pos n⟩ s),
      u ((sceneCloudY qcloud) n ⟨0, Nat.succ_pos n⟩ s)) ∈ (T.core c).window.region

/-! ## 2. Filling hz0 back in -/

/-- **The 7-field minimal bundle from the 6-field one.**  hz0 is filled by
reference_mem_coverCenters (no hypothesis). -/
noncomputable def sceneCloudMinimalLaneBundle_of_hz0Free
    (T : D.TaylorTiles ε) {A B : Set M}
    (pcloud qcloud : ∀ n, Fin (n + 1) → M)
    (base : ∀ n, Fin (n + 1) → T.Index → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (G : ℕ → (ℚ → M) → ℝ)
    (bundle : SceneCloudHz0FreeLaneBundle (P := P) (a := a) (κ := κ)
      (lambda := lambda) (D := D) (ε := ε) (T := T) (A := A) (B := B)
      pcloud qcloud base G) :
    SceneCloudMinimalLaneBundle (P := P) (a := a) (κ := κ) (lambda := lambda)
      (D := D) (ε := ε) (T := T) (A := A) (B := B) pcloud qcloud base G :=
  { hExch := bundle.hExch
    Bp := bundle.Bp
    hBp := bundle.hBp
    hbase := bundle.hbase
    hε := bundle.hε
    hz₀ := fun c ↦ reference_mem_coverCenters T c
    hp := bundle.hp }

/-! ## 3. The bridges -/

/-- **LowerLaneRootedTileMeanLaw from the 6-field bundle + hlaw.** -/
theorem lowerLaneRootedTileMeanLaw_of_hz0FreeBundle
    (T : D.TaylorTiles ε) {A B : Set M}
    (pcloud qcloud : ∀ n, Fin (n + 1) → M)
    (base : ∀ n, Fin (n + 1) → T.Index → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (G : ℕ → (ℚ → M) → ℝ)
    (bundle : SceneCloudHz0FreeLaneBundle (P := P) (a := a) (κ := κ)
      (lambda := lambda) (D := D) (ε := ε) (T := T) (A := A) (B := B)
      pcloud qcloud base G)
    (hlaw : ∀ (f : (↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) (t : ℝ) (c : T.Index),
      T.TilePalmSampleLaw (ε := ε) f t sceneCloudSample (sceneCloudX pcloud)
        (sceneCloudY qcloud) tileScale c
        (fun _ ↦ T.tilePopValue (P := P) (a := a) (κ := κ) (lambda := lambda) (q := q) G c)) :
    LowerLaneRootedTileMeanLaw (P := P) (a := a) (κ := κ) (lambda := lambda) (q := q)
      T (A := A) (B := B) pcloud qcloud base G :=
  lowerLaneRootedTileMeanLaw_of_minimalBundle (T := T) (A := A) (B := B)
    pcloud qcloud base G
    (sceneCloudMinimalLaneBundle_of_hz0Free (T := T) (A := A) (B := B)
      pcloud qcloud base G bundle)
    hlaw

/-- **The lane hId from the 6-field bundle + hlaw.** -/
theorem frozenCampbellMeanIdentification_sceneCloud_of_hz0FreeBundle
    (T : D.TaylorTiles ε) {A B : Set M}
    (pcloud qcloud : ∀ n, Fin (n + 1) → M)
    (base : ∀ n, Fin (n + 1) → T.Index → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (G : ℕ → (ℚ → M) → ℝ)
    (bundle : SceneCloudHz0FreeLaneBundle (P := P) (a := a) (κ := κ)
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
  frozenCampbellMeanIdentification_sceneCloud_of_minimalBundle (T := T) (A := A) (B := B)
    pcloud qcloud base G
    (sceneCloudMinimalLaneBundle_of_hz0Free (T := T) (A := A) (B := B)
      pcloud qcloud base G bundle)
    g hgt hdecomp hF hcomplete hu ha hinj hlaw

/-! ## 4. Reducing Bp / hBp / hbase to one existential field -/

/-- **The three boundedness fields are one existential statement.** -/
theorem hbase_bdd_of_hz0FreeBundle
    (T : D.TaylorTiles ε) {A B : Set M}
    (pcloud qcloud : ∀ n, Fin (n + 1) → M)
    (base : ∀ n, Fin (n + 1) → T.Index → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (G : ℕ → (ℚ → M) → ℝ)
    (bundle : SceneCloudHz0FreeLaneBundle (P := P) (a := a) (κ := κ)
      (lambda := lambda) (D := D) (ε := ε) (T := T) (A := A) (B := B)
      pcloud qcloud base G) :
    ∃ Bp : ℝ, 0 ≤ Bp ∧
      ∀ (n : ℕ) (s : Fin (n + 1)) (c' : T.Index) (i j : Fin (n + 1)),
        |base n s c' i j| ≤ Bp :=
  ⟨bundle.Bp, bundle.hBp, bundle.hbase⟩

/-- **The 6-field bundle from 4 inputs.**  The existential bound replaces
Bp / hBp / hbase, so only hExch, the boundedness of the probe base, hEps and hp remain. -/
noncomputable def sceneCloudHz0FreeLaneBundle_of_bddBase
    (T : D.TaylorTiles ε) {A B : Set M}
    (pcloud qcloud : ∀ n, Fin (n + 1) → M)
    (base : ∀ n, Fin (n + 1) → T.Index → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (G : ℕ → (ℚ → M) → ℝ)
    (hExch : ∀ (f : (↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) (t : ℝ) (n : ℕ) (c : T.Index),
      MaskedEntryExchangeability (sceneCloudSample n)
        (T.tileCostMatrix f t (sceneCloudX pcloud) (sceneCloudY qcloud) tileScale
          (fun f t n s c' ↦ normalizedProbe (K := A ∪ B) base t n s c') n c))
    (hbdd : ∃ Bp : ℝ, 0 ≤ Bp ∧
      ∀ (n : ℕ) (s : Fin (n + 1)) (c' : T.Index) (i j : Fin (n + 1)),
        |base n s c' i j| ≤ Bp)
    (hε : ε ≤ 1 / 2)
    (hp : ∀ (c : T.Index) (n : ℕ) (s : Fin (n + 1)),
      (u ((sceneCloudX pcloud) n ⟨0, Nat.succ_pos n⟩ s),
        u ((sceneCloudY qcloud) n ⟨0, Nat.succ_pos n⟩ s)) ∈ (T.core c).window.region) :
    SceneCloudHz0FreeLaneBundle (P := P) (a := a) (κ := κ) (lambda := lambda)
      (D := D) (ε := ε) (T := T) (A := A) (B := B) pcloud qcloud base G :=
  { hExch := hExch
    Bp := Classical.choose hbdd
    hBp := (Classical.choose_spec hbdd).1
    hbase := (Classical.choose_spec hbdd).2
    hε := hε
    hp := hp }
