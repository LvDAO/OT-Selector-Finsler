import OTSelector.Reconstruction.FinslerOriginalUniformPlanResidualDischarge

/-!
# hz0 is free and hExch is derivable: the 7-field bundle from probe-kernel data

## 1. hz0 (the only window field with no producer in the bundle) is a projection

hz0 : forall c : T.Index, T.reference c in (T.cover c.1).centers, where
T.reference c = (T.partition c.1).center c.2 (FinslerPopulationPressureTiles, def
reference).  FiniteRootNeighborhoodPartition (FinslerCoefficientCorePartition:21) has
the field center_mem : forall i, center i in centers, and T.partition c.1 is a
partition with centers := (T.cover c.1).centers.  Hence hz0 is definitionally
(T.partition c.1).center_mem c.2 and needs no hypothesis:
reference_mem_coverCenters.  The 7-field bundle keeps hz0 only as a field; it is not an
input.

## 2. hExch is derived from the probe-kernel data

maskedEntryExchangeability_tileCostMatrix_forall (FinslerOriginalTileMaskedExchangeabilityInstance:165)
proves MaskedEntryExchangeability of tileCostMatrix from:
* slot measurability hX/hY - here measurable_sceneCloud_slot (finite sample space);
* slot laws hXlaw/hYlaw;
* pairwise cross independence hpair: derived from the lane binder hXY via IndepFun.comp
  with the measurable coordinate projections (measurable_pi_apply);
* probe pair-functionality hprobePair, probe measurability hPsi, probe boundedness hPsiB.
The iid binders hXi/hYi are carried as lane data (they are the paper's iid hypothesis).

## 3. Deliverables

reference_mem_coverCenters;
sceneCloudMinimalLaneBundle_of_probeKernel (builds SceneCloudMinimalLaneBundle with
hExch and hz0 discharged);
frozenCampbellMeanIdentification_sceneCloud_of_probeKernelLane (bridge to the sharpest
hId theorem of FinslerOriginalUniformPlanResidualDischarge).

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
/-! ## 1. hz0 is the partition's center-membership projection -/

/-- **hz0 is free.**  The tile reference point is the center of its root-neighborhood
partition cell, and FiniteRootNeighborhoodPartition.center_mem already places every
center in the cover's centers: no hypothesis is needed. -/
theorem reference_mem_coverCenters (T : D.TaylorTiles ε) (c : T.Index) :
    T.reference c ∈ (T.cover c.1).centers :=
  (T.partition c.1).center_mem c.2

/-! ## 2. The probe-kernel lane constructor -/

/-- **SceneCloudMinimalLaneBundle from the iid lane binders and the probe kernel.**
hExch is derived by maskedEntryExchangeability_tileCostMatrix_forall (slot
measurability from measurable_sceneCloud_slot, pairwise independence from hXY by
IndepFun.comp with the coordinate projections) and hz0 is derived by
reference_mem_coverCenters. -/
noncomputable def sceneCloudMinimalLaneBundle_of_probeKernel
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
    (Bp : ℝ) (hBp : 0 ≤ Bp)
    (hbase : ∀ (n : ℕ) (s : Fin (n + 1)) (c' : T.Index) (i j : Fin (n + 1)),
      |base n s c' i j| ≤ Bp)
    (hε : ε ≤ 1 / 2)
    (hp : ∀ (c : T.Index) (n : ℕ) (s : Fin (n + 1)),
      (u ((sceneCloudX pcloud) n ⟨0, Nat.succ_pos n⟩ s),
        u ((sceneCloudY qcloud) n ⟨0, Nat.succ_pos n⟩ s)) ∈ (T.core c).window.region) :
    SceneCloudMinimalLaneBundle (P := P) (a := a) (κ := κ) (lambda := lambda)
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
    Bp := Bp
    hBp := hBp
    hbase := hbase
    hε := hε
    hz₀ := fun c ↦ reference_mem_coverCenters T c
    hp := hp }

/-! ## 3. Bridge to the sharpest identification theorem -/

/-- **The lane hId from the probe-kernel lane.**  hExch, hz0, hresv, hint and all seven
integrabilities are discharged; only the lane binders, the probe kernel properties,
Bp/hBp/hbase/hEps/hp, g/hgt/hdecomp, the geometric data and hlaw remain. -/
theorem frozenCampbellMeanIdentification_sceneCloud_of_probeKernelLane
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
    (Bp : ℝ) (hBp : 0 ≤ Bp)
    (hbase : ∀ (n : ℕ) (s : Fin (n + 1)) (c' : T.Index) (i j : Fin (n + 1)),
      |base n s c' i j| ≤ Bp)
    (hε : ε ≤ 1 / 2)
    (hp : ∀ (c : T.Index) (n : ℕ) (s : Fin (n + 1)),
      (u ((sceneCloudX pcloud) n ⟨0, Nat.succ_pos n⟩ s),
        u ((sceneCloudY qcloud) n ⟨0, Nat.succ_pos n⟩ s)) ∈ (T.core c).window.region)
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
    (sceneCloudMinimalLaneBundle_of_probeKernel (T := T) (A := A) (B := B)
      pcloud qcloud base G hXi hYi hXlaw hYlaw hXY probeKernel hprobePair hΨ hΨb
      Bp hBp hbase hε hp)
    g hgt hdecomp hF hcomplete hu ha hinj hlaw
