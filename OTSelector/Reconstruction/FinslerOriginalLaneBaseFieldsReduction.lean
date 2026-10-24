import OTSelector.Reconstruction.FinslerOriginalUniformPlanResidualDischarge
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
/-!
# Reducing the lane-bundle base fields: Bp and hBp are redundant

The five fields of `SceneCloudMinimalLaneBundle` examined here have the exact types

* `Bp : ℝ`;
* `hBp : 0 ≤ Bp`;
* `hbase : ∀ (n : ℕ) (s : Fin (n+1)) (c' : T.Index) (i j : Fin (n+1)), |base n s c' i j| ≤ Bp`;
* `hε : ε ≤ 1/2`;
* `hp : ∀ (c : T.Index) (n : ℕ) (s : Fin (n+1)), (u (X n 0 s), u (Y n 0 s)) ∈ (T.core c).window.region`.

Delivered:

* `hBp_nonneg_of_hbase`: `hBp` is DERIVABLE from `hbase` given one tiling index
  (`0 ≤ |base 0 ⟨0⟩ c0 ⟨0⟩ ⟨0⟩| ≤ Bp`), so it need not be assumed separately;
* `LaneBaseBound`: the single existential bound replacing `Bp`/`hBp`/`hbase`;
* `SceneCloudLaneBaseData`/`laneBaseBound_of_laneBaseData`: the base data as one
  structure and its extraction from the minimal bundle;
* `sceneCloudMinimalLaneBundle_of_laneBaseData`: rebuild the minimal bundle from the
  base data plus the remaining independent fields;
* `laneBaseBound_of_bundle`: extraction of the existential bound from the bundle.

`hε` and `hp` are independent hypotheses (numeric resp. geometric); no repo producer
derives them from the other fields, so they remain explicit.

No `sorry`, `admit` or added axiom.
-/

/-- `hBp` is redundant given `hbase` and one tiling index. -/
theorem hBp_nonneg_of_hbase
    (T : D.TaylorTiles ε) {A B : Set M}
    (pcloud qcloud : ∀ n, Fin (n + 1) → M)
    (base : ∀ n, Fin (n + 1) → T.Index → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (G : ℕ → (ℚ → M) → ℝ) (Bp : ℝ)
    (hbase : ∀ (n : ℕ) (s : Fin (n + 1)) (c' : T.Index) (i j : Fin (n + 1)),
      |base n s c' i j| ≤ Bp)
    (c0 : T.Index) : 0 ≤ Bp :=
  le_trans (abs_nonneg _)
    (hbase 0 ⟨0, Nat.succ_pos 0⟩ c0 ⟨0, Nat.succ_pos 0⟩ ⟨0, Nat.succ_pos 0⟩)

/-- The uniform base-matrix bound, without a separately named `Bp`. -/
def LaneBaseBound
    (A B : Set M) (T : D.TaylorTiles ε)
    (pcloud qcloud : ∀ n, Fin (n + 1) → M)
    (base : ∀ n, Fin (n + 1) → T.Index → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (G : ℕ → (ℚ → M) → ℝ) : Prop :=
  ∃ Bp : ℝ, 0 ≤ Bp ∧ ∀ (n : ℕ) (s : Fin (n + 1)) (c' : T.Index)
    (i j : Fin (n + 1)), |base n s c' i j| ≤ Bp

/-- The base-matrix data of the minimal bundle. -/
structure SceneCloudLaneBaseData
    (T : D.TaylorTiles ε) (A B : Set M)
    (base : ∀ n, Fin (n + 1) → T.Index → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) where
  Bp : ℝ
  hBp : 0 ≤ Bp
  hbase : ∀ (n : ℕ) (s : Fin (n + 1)) (c' : T.Index) (i j : Fin (n + 1)),
    |base n s c' i j| ≤ Bp

/-- Extraction of the base data from the minimal bundle. -/
def sceneCloudLaneBaseData_of_bundle
    (T : D.TaylorTiles ε) {A B : Set M}
    (pcloud qcloud : ∀ n, Fin (n + 1) → M)
    (base : ∀ n, Fin (n + 1) → T.Index → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (G : ℕ → (ℚ → M) → ℝ)
    (bundle : SceneCloudMinimalLaneBundle (P := P) (a := a) (κ := κ)
      (lambda := lambda) (D := D) (ε := ε) (T := T) (A := A) (B := B)
      pcloud qcloud base G) :
    SceneCloudLaneBaseData T A B base :=
  { Bp := bundle.Bp, hBp := bundle.hBp, hbase := bundle.hbase }

/-- The existential base bound, extracted from the minimal bundle. -/
theorem laneBaseBound_of_bundle
    (T : D.TaylorTiles ε) {A B : Set M}
    (pcloud qcloud : ∀ n, Fin (n + 1) → M)
    (base : ∀ n, Fin (n + 1) → T.Index → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (G : ℕ → (ℚ → M) → ℝ)
    (bundle : SceneCloudMinimalLaneBundle (P := P) (a := a) (κ := κ)
      (lambda := lambda) (D := D) (ε := ε) (T := T) (A := A) (B := B)
      pcloud qcloud base G) :
    LaneBaseBound A B T pcloud qcloud base G :=
  ⟨bundle.Bp, bundle.hBp, bundle.hbase⟩

/-- Rebuild the minimal lane bundle from the base data plus the remaining four
independent fields. -/
noncomputable def sceneCloudMinimalLaneBundle_of_laneBaseData
    (T : D.TaylorTiles ε) {A B : Set M}
    (pcloud qcloud : ∀ n, Fin (n + 1) → M)
    (base : ∀ n, Fin (n + 1) → T.Index → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (G : ℕ → (ℚ → M) → ℝ)
    (data : SceneCloudLaneBaseData T A B base)
    (hExch : ∀ (f : (↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) (t : ℝ) (n : ℕ) (c : T.Index),
      MaskedEntryExchangeability (sceneCloudSample n)
        (T.tileCostMatrix f t (sceneCloudX pcloud) (sceneCloudY qcloud) tileScale
          (fun f t n s c' ↦ normalizedProbe (K := A ∪ B) base t n s c') n c))
    (hε : ε ≤ 1 / 2)
    (hz₀ : ∀ c : T.Index, T.reference c ∈ (T.cover c.1).centers)
    (hp : ∀ (c : T.Index) (n : ℕ) (s : Fin (n + 1)),
      (u ((sceneCloudX pcloud) n ⟨0, Nat.succ_pos n⟩ s),
        u ((sceneCloudY qcloud) n ⟨0, Nat.succ_pos n⟩ s)) ∈ (T.core c).window.region) :
    SceneCloudMinimalLaneBundle (P := P) (a := a) (κ := κ)
      (lambda := lambda) (D := D) (ε := ε) (T := T) (A := A) (B := B)
      pcloud qcloud base G where
  hExch := hExch
  Bp := data.Bp
  hBp := data.hBp
  hbase := data.hbase
  hε := hε
  hz₀ := hz₀
  hp := hp

end OTSelector.Reconstruction
