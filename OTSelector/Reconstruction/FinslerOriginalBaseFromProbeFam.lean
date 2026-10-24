import OTSelector.Reconstruction.FinslerOriginalProbeKernelLaneBundle
import OTSelector.Reconstruction.FinslerOriginalTilePairRegularity

/-!
# The canonical base from probeFam: closing the four probe-kernel hypotheses

## The canonical base and probe kernel (repo convention)

Following the repo's pair-functional probe convention
(FinslerOriginalProbePairFunctionalityConcrete, probeOfPairKernel_apply, true by rfl),
the lane probe matrix is the pair kernel evaluated at the two cloud points.  Given

* probeFam : FinalProbeSpace A B -> N -> (Q -> M) -> MarkedCloudPoint -> MarkedCloudPoint -> R
  (the endgame probe family, FinslerOriginalPaperTheoremFinalV16),
* probeOfTile : T.Index -> FinalProbeSpace A B  (the probe chosen for each tile),
* marking : M -> MarkedCloudPoint  (the formal marked point of a physical point),

we set

  baseOfProbeFam n s c' i j
    = probeFam (probeOfTile c') 0 (T.reference c')
        (marking (pcloud n s)) (marking (qcloud n s)),
  probeKernelOfProbeFam f t n c p
    = (1 / ((1 + |t|) * ((n+1 : N) : R))) *
        probeFam (probeOfTile c) 0 (T.reference c) (marking p.1) (marking p.2).

The normalization factor is exactly normalizedProbe's, so the pair functionality
normalizedProbe base t n s c i j = probeKernel f t n c (X n i s, Y n j s) is definitional
(probeKernelOfProbeFam_hprobePair, by rfl): the base IS the pair kernel at the cloud
points, hence definitionally the one used in the lane (up to the normalization factor).

## The four hypotheses, proved

* hprobePair: rfl.
* hPsi: measurable_tilePairKernel from hprobe composed with measurable marking
  (Measurable.prodMk), measurable_frozenPhysicalCost_pair and the repo cell/window
  measurability.
* hPsiB: exists_frozenCost_bound_on_mask (UNCONDITIONAL mask-local frozen-cost bound)
  + tileCostPair_abs_le_on_mask with the probe bound from hprobe_bound
  + tilePairKernel_abs_le_of_masked.

So the probe-kernel data is generated from probeFam, its pair measurability hprobe and
its uniform bound hprobe_bound, plus the marking map (whose measurability is required;
no canonical marking of physical points exists in the tile lane data, so it is an
explicit input).

## Field chain

15 -> 8 -> 7 -> 6 -> 4 -> 3 fields; SceneCloudThreeFieldLaneBundle keeps only hbdd, hEps,
hp, and the bridges below reach the sharpest hId and lower-lane mean-law theorems.

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
/-! ## 1. The canonical base and probe kernel -/

/-- The canonical lane base: the pair kernel of probeFam at the two cloud points. -/
noncomputable def baseOfProbeFam (T : D.TaylorTiles ε) {A B : Set M}
    (probeFam : FinalProbeSpace A B → ℕ → (ℚ → M) →
      MarkedCloudPoint → MarkedCloudPoint → ℝ)
    (probeOfTile : T.Index → FinalProbeSpace A B) (marking : M → MarkedCloudPoint)
    (pcloud qcloud : ∀ n, Fin (n + 1) → M) :
    ∀ n, Fin (n + 1) → T.Index → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
  fun n s c' _ _ ↦
    probeFam (probeOfTile c') 0 (T.reference c')
      (marking (pcloud n s)) (marking (qcloud n s))

/-- The canonical probe kernel: the normalized pair evaluation of probeFam. -/
noncomputable def probeKernelOfProbeFam (T : D.TaylorTiles ε) {A B : Set M}
    (probeFam : FinalProbeSpace A B → ℕ → (ℚ → M) →
      MarkedCloudPoint → MarkedCloudPoint → ℝ)
    (probeOfTile : T.Index → FinalProbeSpace A B) (marking : M → MarkedCloudPoint) :
    ((↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) → ℝ → ℕ → T.Index → M × M → ℝ :=
  fun _ t n c p ↦
    (1 / ((1 + |t|) * ((n + 1 : ℕ) : ℝ))) *
      probeFam (probeOfTile c) 0 (T.reference c) (marking p.1) (marking p.2)

/-- **Probe pair-functionality, by rfl**: the normalized probe is the pair kernel at
the cloud points. -/
theorem probeKernelOfProbeFam_hprobePair (T : D.TaylorTiles ε) {A B : Set M}
    (probeFam : FinalProbeSpace A B → ℕ → (ℚ → M) →
      MarkedCloudPoint → MarkedCloudPoint → ℝ)
    (probeOfTile : T.Index → FinalProbeSpace A B) (marking : M → MarkedCloudPoint)
    (pcloud qcloud : ∀ n, Fin (n + 1) → M) :
    ∀ (f : (↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) (t : ℝ) (n : ℕ) (c : T.Index)
      (s : Fin (n + 1)) (i j : Fin (n + 1)),
      normalizedProbe (K := A ∪ B)
          (baseOfProbeFam (T := T) probeFam probeOfTile marking pcloud qcloud)
          t n s c i j =
        probeKernelOfProbeFam (T := T) probeFam probeOfTile marking f t n c
          ((sceneCloudX pcloud) n i s, (sceneCloudY qcloud) n j s) :=
  fun f t n c s i j ↦ rfl

/-- **hprobePair is the definitional pair functionality.** -/
theorem probeKernelOfProbeFam_measurable (T : D.TaylorTiles ε) {A B : Set M}
    (probeFam : FinalProbeSpace A B → ℕ → (ℚ → M) →
      MarkedCloudPoint → MarkedCloudPoint → ℝ)
    (probeOfTile : T.Index → FinalProbeSpace A B) (marking : M → MarkedCloudPoint)
    (hmark : Measurable marking)
    (hprobe : ∀ (φ : FinalProbeSpace A B) (j : ℕ) (z : ℚ → M),
      Measurable (fun p : MarkedCloudPoint × MarkedCloudPoint => probeFam φ j z p.1 p.2))
    (f : (↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) (t : ℝ) (n : ℕ) (c : T.Index) :
    Measurable (probeKernelOfProbeFam (T := T) probeFam probeOfTile marking f t n c) := by
  have hpair : Measurable (fun p : M × M => (marking p.1, marking p.2)) :=
    (hmark.comp measurable_fst).prodMk (hmark.comp measurable_snd)
  exact ((hprobe (probeOfTile c) 0 (T.reference c)).comp hpair).const_mul _

/-- Pointwise bound of the canonical probe kernel from hprobe_bound. -/
theorem abs_probeKernelOfProbeFam (T : D.TaylorTiles ε) {A B : Set M}
    (probeFam : FinalProbeSpace A B → ℕ → (ℚ → M) →
      MarkedCloudPoint → MarkedCloudPoint → ℝ)
    (probeOfTile : T.Index → FinalProbeSpace A B) (marking : M → MarkedCloudPoint)
    {Gc : ℝ}
    (hprobe_bound : ∀ (φ : FinalProbeSpace A B) (j : ℕ) (z : ℚ → M)
      (x y : MarkedCloudPoint), |probeFam φ j z x y| ≤ Gc)
    (f : (↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) (t : ℝ) (n : ℕ) (c : T.Index)
    (p : M × M) :
    |probeKernelOfProbeFam (T := T) probeFam probeOfTile marking f t n c p| ≤
      (1 / ((1 + |t|) * ((n + 1 : ℕ) : ℝ))) * Gc := by
  have hcoef0 : 0 ≤ 1 / ((1 + |t|) * ((n + 1 : ℕ) : ℝ)) := by positivity
  show |(1 / ((1 + |t|) * ((n + 1 : ℕ) : ℝ))) *
    probeFam (probeOfTile c) 0 (T.reference c) (marking p.1) (marking p.2)| ≤ _
  rw [abs_mul, abs_of_nonneg hcoef0]
  exact mul_le_mul_of_nonneg_left
    (hprobe_bound (probeOfTile c) 0 (T.reference c) (marking p.1) (marking p.2)) hcoef0

/-! ## 2. hPsi and hPsiB proved -/

/-- **hPsi: measurability of the masked pair kernel of the canonical probe.** -/
theorem probeKernelOfProbeFam_hΨ (T : D.TaylorTiles ε) {A B : Set M}
    (probeFam : FinalProbeSpace A B → ℕ → (ℚ → M) →
      MarkedCloudPoint → MarkedCloudPoint → ℝ)
    (probeOfTile : T.Index → FinalProbeSpace A B) (marking : M → MarkedCloudPoint)
    (hmark : Measurable marking)
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
      (probeKernelOfProbeFam (T := T) probeFam probeOfTile marking f t n c)) :=
  measurable_tilePairKernel (T := T) c (tileScale n) t _
    (measurableSet_tileCell (T := T) c)
    (measurableSet_tileWindowRegion (T := T) c)
    ha (measurable_u_of_lipschitz hu)
    (measurable_frozenPhysicalCost_pair (T := T) hF hcomplete hu ha hinj c)
    (probeKernelOfProbeFam_measurable (T := T) probeFam probeOfTile marking hmark hprobe
      f t n c)

/-- **hPsiB: uniform boundedness of the masked pair kernel of the canonical
probe**, from the unconditional mask-local frozen-cost bound and hprobe_bound. -/
theorem probeKernelOfProbeFam_hΨb (T : D.TaylorTiles ε) {A B : Set M}
    (probeFam : FinalProbeSpace A B → ℕ → (ℚ → M) →
      MarkedCloudPoint → MarkedCloudPoint → ℝ)
    (probeOfTile : T.Index → FinalProbeSpace A B) (marking : M → MarkedCloudPoint)
    {Gc : ℝ}
    (hprobe_bound : ∀ (φ : FinalProbeSpace A B) (j : ℕ) (z : ℚ → M)
      (x y : MarkedCloudPoint), |probeFam φ j z x y| ≤ Gc)
    (f : (↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) (t : ℝ) (n : ℕ) (c : T.Index) :
    ∃ B : ℝ, ∀ p : M × M,
      |T.tilePairKernel c (tileScale n) t
        (probeKernelOfProbeFam (T := T) probeFam probeOfTile marking f t n c) p| ≤ B := by
  obtain ⟨Mfc, hMfc0, hfc⟩ := exists_frozenCost_bound_on_mask (T := T) c
  have hGc0 : 0 ≤ Gc :=
    (abs_nonneg _).trans
      (hprobe_bound (probeOfTile c) 0 (T.reference c)
        (0, ⟨0, ⟨le_refl _, by norm_num⟩⟩) (0, ⟨0, ⟨le_refl _, by norm_num⟩⟩))
  have hcoef0 : 0 ≤ 1 / ((1 + |t|) * ((n + 1 : ℕ) : ℝ)) := by positivity
  have hB0 : 0 ≤ |1 - 2 * ε| * (|tileScale n| * Mfc) + |t| *
      ((1 / ((1 + |t|) * ((n + 1 : ℕ) : ℝ))) * Gc) := by positivity
  exact ⟨_, tilePairKernel_abs_le_of_masked (T := T) c (tileScale n) t _ hB0
    (tileCostPair_abs_le_on_mask (T := T) c (tileScale n) t _ hfc
      (abs_probeKernelOfProbeFam (T := T) probeFam probeOfTile marking hprobe_bound
        f t n c))⟩


/-! ## 3. The 3-field bundle, the endgame constructor and the bridges -/

/-- **The 3-field lane bundle**: the base bound, the Taylor accuracy condition and the
retained-edge window condition.  hExch, hz0, the seven integrabilities, hint, hresv and
the four probe-kernel hypotheses are all discharged downstream. -/
structure SceneCloudThreeFieldLaneBundle
    (T : D.TaylorTiles ε) {A B : Set M}
    (pcloud qcloud : ∀ n, Fin (n + 1) → M)
    (base : ∀ n, Fin (n + 1) → T.Index → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (G : ℕ → (ℚ → M) → ℝ) : Type _ where
  hbdd : LaneBaseBound A B T pcloud qcloud base G
  hε : ε ≤ 1 / 2
  hp : ∀ (c : T.Index) (n : ℕ) (s : Fin (n + 1)),
    (u ((sceneCloudX pcloud) n ⟨0, Nat.succ_pos n⟩ s),
      u ((sceneCloudY qcloud) n ⟨0, Nat.succ_pos n⟩ s)) ∈ (T.core c).window.region

/-- The 3-field bundle is exactly the probe-kernel bundle. -/
noncomputable def sceneCloudProbeKernelLaneBundle_of_threeFieldLane
    (T : D.TaylorTiles ε) {A B : Set M}
    (pcloud qcloud : ∀ n, Fin (n + 1) → M)
    (base : ∀ n, Fin (n + 1) → T.Index → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (G : ℕ → (ℚ → M) → ℝ)
    (bundle : SceneCloudThreeFieldLaneBundle (P := P) (a := a) (κ := κ)
      (lambda := lambda) (D := D) (ε := ε) (T := T) (A := A) (B := B)
      pcloud qcloud base G) :
    SceneCloudProbeKernelLaneBundle (P := P) (a := a) (κ := κ) (lambda := lambda)
      (D := D) (ε := ε) (T := T) (A := A) (B := B) pcloud qcloud base G :=
  { hbdd := bundle.hbdd
    hε := bundle.hε
    hp := bundle.hp }

/-- Rebuild the 3-field bundle from the probe-kernel bundle. -/
noncomputable def sceneCloudThreeFieldLaneBundle_of_probeKernelLane
    (T : D.TaylorTiles ε) {A B : Set M}
    (pcloud qcloud : ∀ n, Fin (n + 1) → M)
    (base : ∀ n, Fin (n + 1) → T.Index → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (G : ℕ → (ℚ → M) → ℝ)
    (bundle : SceneCloudProbeKernelLaneBundle (P := P) (a := a) (κ := κ)
      (lambda := lambda) (D := D) (ε := ε) (T := T) (A := A) (B := B)
      pcloud qcloud base G) :
    SceneCloudThreeFieldLaneBundle (P := P) (a := a) (κ := κ) (lambda := lambda)
      (D := D) (ε := ε) (T := T) (A := A) (B := B) pcloud qcloud base G :=
  { hbdd := bundle.hbdd
    hε := bundle.hε
    hp := bundle.hp }

/-- **The 6-field bundle from the 3-field bundle and the endgame probe data.**  The four
probe-kernel hypotheses are proved for the canonical base, so batch29's constructor
applies. -/
noncomputable def sceneCloudHz0FreeLaneBundle_of_endgameProbe
    (T : D.TaylorTiles ε) {A B : Set M}
    (pcloud qcloud : ∀ n, Fin (n + 1) → M)
    (G : ℕ → (ℚ → M) → ℝ)
    (probeFam : FinalProbeSpace A B → ℕ → (ℚ → M) →
      MarkedCloudPoint → MarkedCloudPoint → ℝ)
    (probeOfTile : T.Index → FinalProbeSpace A B) (marking : M → MarkedCloudPoint)
    (bundle : SceneCloudThreeFieldLaneBundle (P := P) (a := a) (κ := κ)
      (lambda := lambda) (D := D) (ε := ε) (T := T) (A := A) (B := B)
      pcloud qcloud
      (baseOfProbeFam (T := T) probeFam probeOfTile marking pcloud qcloud) G)
    (hmark : Measurable marking)
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
      (baseOfProbeFam (T := T) probeFam probeOfTile marking pcloud qcloud) G := by
  have hGc : ∀ (φ : FinalProbeSpace A B) (j : ℕ) (z : ℚ → M)
      (x y : MarkedCloudPoint), |probeFam φ j z x y| ≤ Classical.choose hprobe_bound :=
    Classical.choose_spec hprobe_bound
  exact sceneCloudHz0FreeLaneBundle_of_probeKernelLane (T := T) (A := A) (B := B)
    pcloud qcloud
    (baseOfProbeFam (T := T) probeFam probeOfTile marking pcloud qcloud) G
    hXi hYi hXlaw hYlaw hXY
    (probeKernelOfProbeFam (T := T) probeFam probeOfTile marking)
    (probeKernelOfProbeFam_hprobePair (T := T) probeFam probeOfTile marking pcloud qcloud)
    (fun f t n c ↦ probeKernelOfProbeFam_hΨ (T := T) probeFam probeOfTile marking
      hmark hprobe hF hcomplete hu ha hinj f t n c)
    (fun f t n c ↦ probeKernelOfProbeFam_hΨb (T := T) probeFam probeOfTile marking
      hGc f t n c)
    { hbdd := bundle.hbdd, hε := bundle.hε, hp := bundle.hp }

/-- **The lane hId from the 3-field bundle and the endgame probe data.**  Everything
except g/hgt/hdecomp, the geometric data and hlaw is derived. -/
theorem frozenCampbellMeanIdentification_sceneCloud_of_threeFieldBundle
    (T : D.TaylorTiles ε) {A B : Set M}
    (pcloud qcloud : ∀ n, Fin (n + 1) → M)
    (G : ℕ → (ℚ → M) → ℝ)
    (probeFam : FinalProbeSpace A B → ℕ → (ℚ → M) →
      MarkedCloudPoint → MarkedCloudPoint → ℝ)
    (probeOfTile : T.Index → FinalProbeSpace A B) (marking : M → MarkedCloudPoint)
    (bundle : SceneCloudThreeFieldLaneBundle (P := P) (a := a) (κ := κ)
      (lambda := lambda) (D := D) (ε := ε) (T := T) (A := A) (B := B)
      pcloud qcloud
      (baseOfProbeFam (T := T) probeFam probeOfTile marking pcloud qcloud) G)
    (hmark : Measurable marking)
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
        (baseOfProbeFam (T := T) probeFam probeOfTile marking pcloud qcloud)
        (uniformTilePlan (fun n ↦ Fin (n + 1))) tileScale) T.Index :=
  frozenCampbellMeanIdentification_sceneCloud_of_hz0FreeBundle (T := T) (A := A) (B := B)
    pcloud qcloud
    (baseOfProbeFam (T := T) probeFam probeOfTile marking pcloud qcloud) G
    (sceneCloudHz0FreeLaneBundle_of_endgameProbe (T := T) (A := A) (B := B)
      pcloud qcloud G probeFam probeOfTile marking bundle hmark hprobe hprobe_bound
      hF hcomplete hu ha hinj hXi hYi hXlaw hYlaw hXY)
    g hgt hdecomp hF hcomplete hu ha hinj hlaw

/-- **LowerLaneRootedTileMeanLaw from the 3-field bundle and the endgame probe data.** -/
theorem lowerLaneRootedTileMeanLaw_of_threeFieldBundle
    (T : D.TaylorTiles ε) {A B : Set M}
    (pcloud qcloud : ∀ n, Fin (n + 1) → M)
    (G : ℕ → (ℚ → M) → ℝ)
    (probeFam : FinalProbeSpace A B → ℕ → (ℚ → M) →
      MarkedCloudPoint → MarkedCloudPoint → ℝ)
    (probeOfTile : T.Index → FinalProbeSpace A B) (marking : M → MarkedCloudPoint)
    (bundle : SceneCloudThreeFieldLaneBundle (P := P) (a := a) (κ := κ)
      (lambda := lambda) (D := D) (ε := ε) (T := T) (A := A) (B := B)
      pcloud qcloud
      (baseOfProbeFam (T := T) probeFam probeOfTile marking pcloud qcloud) G)
    (hmark : Measurable marking)
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
      (baseOfProbeFam (T := T) probeFam probeOfTile marking pcloud qcloud) G :=
  lowerLaneRootedTileMeanLaw_of_hz0FreeBundle (T := T) (A := A) (B := B)
    pcloud qcloud
    (baseOfProbeFam (T := T) probeFam probeOfTile marking pcloud qcloud) G
    (sceneCloudHz0FreeLaneBundle_of_endgameProbe (T := T) (A := A) (B := B)
      pcloud qcloud G probeFam probeOfTile marking bundle hmark hprobe hprobe_bound
      hF hcomplete hu ha hinj hXi hYi hXlaw hYlaw hXY)
    hlaw
