import OTSelector.Reconstruction.FinslerOriginalCanonicalMarking

/-!
# Removing the tile probe choice from the canonical-marking route

## What the tile data carries

A token list of the tile carrier (FinslerPopulationPressureTiles) is

  D.TaylorTiles eps  =  cover : forall i, TaylorRootCover eps
                       partition : forall i, FiniteRootNeighborhoodPartition ...,
  T.Index = (i : Fin D.haar.continuous.count) x Fin (T.partition i).count,
  T.core k = D.haar.continuous.coefficient k.1   (the frozen physical coefficient:
              window, frozen cost, roots),
  T.reference k = (T.partition k.1).center k.2    (a root, i.e. a map Q -> M).

None of these fields produces an element of

  FinalProbeSpace A B = ((A u B) x (A u B)) ->b Real,

so the tile data determines no canonical probe per tile.  Likewise the repository has
no tile-indexed probe family: probeFam is model data (a hypothesis bundle
RootwiseStationaryInputs) and probeOfTile only selects one of its probes per tile.
Hence probeOfTile is genuinely free data; its exact minimal hypothesis is that it be
an arbitrary function T.Index -> FinalProbeSpace A B.

## No regularity is ever used

Every hypothesis-producing step is unconditional in the tile probe choice:

* the base bound is derived from hprobe_bound for EVERY probeOfTile, with the explicit
  uniform constant max Gc 0 (abs_canonicalBase_le, laneBaseBound_canonicalBase,
  laneBaseBound_canonicalBase_forall); this removes the hbdd field of the 3-field
  bundle (sceneCloudThreeFieldLaneBundle_of_probeBound,
  sceneCloudProbeKernelLaneBundle_of_probeBound);
* canonicalProbeKernel_hprobePair / _hPsi / _hPsiB of FinslerOriginalCanonicalMarking
  are stated for an arbitrary probeOfTile (no measurability, continuity or bound is
  assumed).

A data-free canonical default exists: canonicalProbeOfTile, the zero probe on every
tile (canonicalProbe); the choice space is always nonempty (nonempty_probeOfTile).

## Independence in the relevant sense

The canonical base sees the tile probe choice only through the per-tile readout
tileProbeReadout T probeFam probeOfTile c = probeFam (probeOfTile c) 0 (T.reference c):
equal readouts give equal bases and equal probe kernels
(canonicalBase_eq_of_tileProbeReadout_eq,
canonicalProbeKernel_eq_of_tileProbeReadout_eq).  If probeFam does not depend on its
probe argument, the base is independent of probeOfTile and the input is removable
entirely (canonicalBase_eq_of_probeFam_const,
canonicalProbeKernel_eq_of_probeFam_const).  On the other hand the choice can change
the lane model (exists_probeFam_bases_ne), so no canonical value is determined by T.

## V18 residual

In paperTheoremFinalV18_of_canonicalBase the new inputs of the canonical-marking route
are probeOfTile, marking and hmark.  The marking and its measurability are removed by
FinslerOriginalCanonicalMarking.  The residual input of this module is exactly one
arbitrary function probeOfTile : T.Index -> FinalProbeSpace A B, with no regularity
requirement; it can be fixed to canonicalProbeOfTile (no probe input remains) and is
removable outright when probeFam is probe-independent.  No other input is added.

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

/-! ## 1. The canonical data-free probe choice -/

/-- The canonical probe-space element that needs no data: the zero bounded continuous
function on the pair space of the carrier. -/
noncomputable def canonicalProbe (A B : Set M) : FinalProbeSpace A B := 0

/-- The canonical tile probe choice: the zero probe on every tile.  It is defined from
nothing but the tile index type, so every caller can supply it. -/
noncomputable def canonicalProbeOfTile (T : D.TaylorTiles ε) {A B : Set M} :
    T.Index → FinalProbeSpace A B :=
  fun _ ↦ canonicalProbe A B

/-- The constant one probe: used to exhibit that two admissible tile probe choices can
give different lane bases. -/
noncomputable def oneProbe (A B : Set M) : FinalProbeSpace A B := 1

@[simp] theorem canonicalProbe_apply (A B : Set M)
    (p : ↥(A ∪ B) × ↥(A ∪ B)) : canonicalProbe A B p = 0 := rfl

@[simp] theorem oneProbe_apply (A B : Set M)
    (p : ↥(A ∪ B) × ↥(A ∪ B)) : oneProbe A B p = 1 := rfl

/-- The tile-probe choice space is nonempty: an arbitrary function is always available. -/
theorem nonempty_probeOfTile (T : D.TaylorTiles ε) {A B : Set M} :
    Nonempty (T.Index → FinalProbeSpace A B) :=
  ⟨canonicalProbeOfTile (T := T)⟩

/-! ## 2. No regularity is needed on the tile probe choice -/

/-- **Pointwise base bound from hprobe_bound alone, for every tile probe choice.** -/
theorem abs_canonicalBase_le (T : D.TaylorTiles ε) {A B : Set M}
    (pcloud qcloud : ∀ n, Fin (n + 1) → M)
    (probeFam : FinalProbeSpace A B → ℕ → (ℚ → M) →
      MarkedCloudPoint → MarkedCloudPoint → ℝ)
    (probeOfTile : T.Index → FinalProbeSpace A B) {Gc : ℝ}
    (hprobe_bound : ∀ (φ : FinalProbeSpace A B) (j : ℕ) (z : ℚ → M)
      (x y : MarkedCloudPoint), |probeFam φ j z x y| ≤ Gc)
    (n : ℕ) (s : Fin (n + 1)) (c' : T.Index) (i j : Fin (n + 1)) :
    |(canonicalBase u T probeFam probeOfTile pcloud qcloud) n s c' i j| ≤ max Gc 0 := by
  exact le_trans
    (hprobe_bound (probeOfTile c') 0 (T.reference c')
      (canonicalMarking u (pcloud n s)) (canonicalMarking u (qcloud n s)))
    (le_max_left Gc 0)

/-- **The 3-field base bound at the canonical base, for every tile probe choice.** -/
theorem laneBaseBound_canonicalBase (T : D.TaylorTiles ε) {A B : Set M}
    (pcloud qcloud : ∀ n, Fin (n + 1) → M)
    (G : ℕ → (ℚ → M) → ℝ)
    (probeFam : FinalProbeSpace A B → ℕ → (ℚ → M) →
      MarkedCloudPoint → MarkedCloudPoint → ℝ)
    (probeOfTile : T.Index → FinalProbeSpace A B) {Gc : ℝ}
    (hprobe_bound : ∀ (φ : FinalProbeSpace A B) (j : ℕ) (z : ℚ → M)
      (x y : MarkedCloudPoint), |probeFam φ j z x y| ≤ Gc) :
    LaneBaseBound A B T pcloud qcloud
      (canonicalBase u T probeFam probeOfTile pcloud qcloud) G :=
  ⟨max Gc 0, le_max_right Gc 0, fun n s c' i j ↦
    abs_canonicalBase_le (T := T) (A := A) (B := B) pcloud qcloud probeFam
      probeOfTile hprobe_bound n s c' i j⟩

/-- **Every function T.Index -> FinalProbeSpace A B is an admissible tile probe
choice.**  The base bound holds uniformly, with no measurability, continuity or
boundedness assumption on the choice. -/
theorem laneBaseBound_canonicalBase_forall (T : D.TaylorTiles ε) {A B : Set M}
    (pcloud qcloud : ∀ n, Fin (n + 1) → M)
    (G : ℕ → (ℚ → M) → ℝ)
    (probeFam : FinalProbeSpace A B → ℕ → (ℚ → M) →
      MarkedCloudPoint → MarkedCloudPoint → ℝ)
    {Gc : ℝ}
    (hprobe_bound : ∀ (φ : FinalProbeSpace A B) (j : ℕ) (z : ℚ → M)
      (x y : MarkedCloudPoint), |probeFam φ j z x y| ≤ Gc) :
    ∀ probeOfTile : T.Index → FinalProbeSpace A B,
      LaneBaseBound A B T pcloud qcloud
        (canonicalBase u T probeFam probeOfTile pcloud qcloud) G :=
  fun probeOfTile ↦ laneBaseBound_canonicalBase (T := T) (A := A) (B := B)
    pcloud qcloud G probeFam probeOfTile hprobe_bound

/-! ## 3. The bundle at the canonical base with the base bound derived -/

/-- **The 3-field lane bundle at the canonical base, for every tile probe choice**,
with hbdd derived from hprobe_bound; only the two geometric fields remain as inputs. -/
noncomputable def sceneCloudThreeFieldLaneBundle_of_probeBound
    (T : D.TaylorTiles ε) {A B : Set M}
    (pcloud qcloud : ∀ n, Fin (n + 1) → M)
    (G : ℕ → (ℚ → M) → ℝ)
    (probeFam : FinalProbeSpace A B → ℕ → (ℚ → M) →
      MarkedCloudPoint → MarkedCloudPoint → ℝ)
    (probeOfTile : T.Index → FinalProbeSpace A B)
    (hprobe_bound : ∃ Gc : ℝ, ∀ (φ : FinalProbeSpace A B) (j : ℕ) (z : ℚ → M)
      (x y : MarkedCloudPoint), |probeFam φ j z x y| ≤ Gc)
    (hεT : ε ≤ 1 / 2)
    (hpT : ∀ (c : T.Index) (n : ℕ) (s : Fin (n + 1)),
      (u ((sceneCloudX pcloud) n ⟨0, Nat.succ_pos n⟩ s),
        u ((sceneCloudY qcloud) n ⟨0, Nat.succ_pos n⟩ s)) ∈ (T.core c).window.region) :
    SceneCloudThreeFieldLaneBundle (P := P) (a := a) (κ := κ) (lambda := lambda)
      (D := D) (ε := ε) (T := T) (A := A) (B := B) pcloud qcloud
      (canonicalBase u T probeFam probeOfTile pcloud qcloud) G :=
  { hbdd := laneBaseBound_canonicalBase (T := T) (A := A) (B := B) pcloud qcloud G
      probeFam probeOfTile (Gc := Classical.choose hprobe_bound)
      (Classical.choose_spec hprobe_bound)
    hε := hεT
    hp := hpT }

/-- **The probe-kernel lane bundle at the canonical base, for every tile probe
choice**, from hprobe_bound and the two geometric fields. -/
noncomputable def sceneCloudProbeKernelLaneBundle_of_probeBound
    (T : D.TaylorTiles ε) {A B : Set M}
    (pcloud qcloud : ∀ n, Fin (n + 1) → M)
    (G : ℕ → (ℚ → M) → ℝ)
    (probeFam : FinalProbeSpace A B → ℕ → (ℚ → M) →
      MarkedCloudPoint → MarkedCloudPoint → ℝ)
    (probeOfTile : T.Index → FinalProbeSpace A B)
    (hprobe_bound : ∃ Gc : ℝ, ∀ (φ : FinalProbeSpace A B) (j : ℕ) (z : ℚ → M)
      (x y : MarkedCloudPoint), |probeFam φ j z x y| ≤ Gc)
    (hεT : ε ≤ 1 / 2)
    (hpT : ∀ (c : T.Index) (n : ℕ) (s : Fin (n + 1)),
      (u ((sceneCloudX pcloud) n ⟨0, Nat.succ_pos n⟩ s),
        u ((sceneCloudY qcloud) n ⟨0, Nat.succ_pos n⟩ s)) ∈ (T.core c).window.region) :
    SceneCloudProbeKernelLaneBundle (P := P) (a := a) (κ := κ) (lambda := lambda)
      (D := D) (ε := ε) (T := T) (A := A) (B := B) pcloud qcloud
      (canonicalBase u T probeFam probeOfTile pcloud qcloud) G :=
  sceneCloudProbeKernelLaneBundle_of_canonicalBase (T := T) (A := A) (B := B)
    pcloud qcloud G probeFam probeOfTile
    (sceneCloudThreeFieldLaneBundle_of_probeBound (T := T) (A := A) (B := B)
      pcloud qcloud G probeFam probeOfTile hprobe_bound hεT hpT)

/-! ## 4. Dependence on the tile probe choice -/

/-- The only way the canonical base sees the tile probe choice: through the per-tile
probe readout phi -> probeFam phi 0 (T.reference c). -/
def tileProbeReadout (T : D.TaylorTiles ε) {A B : Set M}
    (probeFam : FinalProbeSpace A B → ℕ → (ℚ → M) →
      MarkedCloudPoint → MarkedCloudPoint → ℝ)
    (probeOfTile : T.Index → FinalProbeSpace A B) :
    T.Index → MarkedCloudPoint → MarkedCloudPoint → ℝ :=
  fun c ↦ probeFam (probeOfTile c) 0 (T.reference c)

/-- Equal per-tile probe readouts give equal canonical bases. -/
theorem canonicalBase_eq_of_tileProbeReadout_eq (T : D.TaylorTiles ε) {A B : Set M}
    (pcloud qcloud : ∀ n, Fin (n + 1) → M)
    (probeFam : FinalProbeSpace A B → ℕ → (ℚ → M) →
      MarkedCloudPoint → MarkedCloudPoint → ℝ)
    {probeOfTile₁ probeOfTile₂ : T.Index → FinalProbeSpace A B}
    (h : tileProbeReadout (T := T) probeFam probeOfTile₁ =
      tileProbeReadout (T := T) probeFam probeOfTile₂) :
    canonicalBase u T probeFam probeOfTile₁ pcloud qcloud =
      canonicalBase u T probeFam probeOfTile₂ pcloud qcloud := by
  funext n s c' i j
  simpa only [canonicalBase, baseOfProbeFam, tileProbeReadout] using
    congrFun (congrFun (congrFun h c') (canonicalMarking u (pcloud n s)))
      (canonicalMarking u (qcloud n s))

/-- Equal per-tile probe readouts give equal canonical probe kernels. -/
theorem canonicalProbeKernel_eq_of_tileProbeReadout_eq (T : D.TaylorTiles ε)
    {A B : Set M}
    (probeFam : FinalProbeSpace A B → ℕ → (ℚ → M) →
      MarkedCloudPoint → MarkedCloudPoint → ℝ)
    {probeOfTile₁ probeOfTile₂ : T.Index → FinalProbeSpace A B}
    (h : tileProbeReadout (T := T) probeFam probeOfTile₁ =
      tileProbeReadout (T := T) probeFam probeOfTile₂) :
    canonicalProbeKernel u T probeFam probeOfTile₁ =
      canonicalProbeKernel u T probeFam probeOfTile₂ := by
  funext f t n c p
  have hc := congrFun (congrFun (congrFun h c) (canonicalMarking u p.1))
    (canonicalMarking u p.2)
  simp only [tileProbeReadout] at hc
  rw [canonicalProbeKernel, probeKernelOfProbeFam,
    canonicalProbeKernel, probeKernelOfProbeFam, hc]

/-- If the probe family does not depend on its probe argument, the canonical base is
independent of the tile probe choice; the input is then removable. -/
theorem canonicalBase_eq_of_probeFam_const (T : D.TaylorTiles ε) {A B : Set M}
    (pcloud qcloud : ∀ n, Fin (n + 1) → M)
    (probeFam : FinalProbeSpace A B → ℕ → (ℚ → M) →
      MarkedCloudPoint → MarkedCloudPoint → ℝ)
    (probeOfTile : T.Index → FinalProbeSpace A B)
    (hconst : ∀ (φ : FinalProbeSpace A B) (j : ℕ) (z : ℚ → M)
      (x y : MarkedCloudPoint), probeFam φ j z x y = probeFam 0 j z x y) :
    canonicalBase u T probeFam probeOfTile pcloud qcloud =
      canonicalBase u T probeFam
        (canonicalProbeOfTile (T := T) (A := A) (B := B)) pcloud qcloud := by
  apply canonicalBase_eq_of_tileProbeReadout_eq (T := T) (A := A) (B := B)
    (pcloud := pcloud) (qcloud := qcloud)
  funext c x y
  simpa only [tileProbeReadout, canonicalProbeOfTile, canonicalProbe] using
    hconst (probeOfTile c) 0 (T.reference c) x y

/-- If the probe family does not depend on its probe argument, the canonical probe
kernel is independent of the tile probe choice. -/
theorem canonicalProbeKernel_eq_of_probeFam_const (T : D.TaylorTiles ε) {A B : Set M}
    (probeFam : FinalProbeSpace A B → ℕ → (ℚ → M) →
      MarkedCloudPoint → MarkedCloudPoint → ℝ)
    (probeOfTile : T.Index → FinalProbeSpace A B)
    (hconst : ∀ (φ : FinalProbeSpace A B) (j : ℕ) (z : ℚ → M)
      (x y : MarkedCloudPoint), probeFam φ j z x y = probeFam 0 j z x y) :
    canonicalProbeKernel u T probeFam probeOfTile =
      canonicalProbeKernel u T probeFam
        (canonicalProbeOfTile (T := T) (A := A) (B := B)) := by
  apply canonicalProbeKernel_eq_of_tileProbeReadout_eq (T := T) (A := A) (B := B)
  funext c x y
  simpa only [tileProbeReadout, canonicalProbeOfTile, canonicalProbe] using
    hconst (probeOfTile c) 0 (T.reference c) x y

/-- **The tile probe choice is genuine data**: some admissible probe family gives
different canonical bases for two different choices.  Hence no canonical probe value is
determined by the tile data; only the hypothesis interface is choice-independent. -/
theorem exists_probeFam_bases_ne (T : D.TaylorTiles ε) {A B : Set M}
    (hAB : (A ∪ B).Nonempty) (hT : Nonempty T.Index)
    (pcloud qcloud : ∀ n, Fin (n + 1) → M) :
    ∃ probeFam : FinalProbeSpace A B → ℕ → (ℚ → M) →
        MarkedCloudPoint → MarkedCloudPoint → ℝ,
      canonicalBase u T probeFam (canonicalProbeOfTile (T := T) (A := A) (B := B))
          pcloud qcloud ≠
        canonicalBase u T probeFam
          (fun _ : T.Index ↦ oneProbe A B) pcloud qcloud := by
  obtain ⟨p0, hp0⟩ := hAB
  obtain ⟨c0⟩ := hT
  refine ⟨fun φ _ _ _ _ ↦ φ (⟨p0, hp0⟩, ⟨p0, hp0⟩), ?_⟩
  intro hEq
  have h := congrFun (congrFun (congrFun (congrFun (congrFun hEq 0)
    ⟨0, Nat.succ_pos 0⟩) c0) ⟨0, Nat.succ_pos 0⟩) ⟨0, Nat.succ_pos 0⟩
  simp only [canonicalBase, baseOfProbeFam, canonicalProbeOfTile] at h
  rw [canonicalProbe_apply, oneProbe_apply] at h
  exact zero_ne_one h

end OTSelector.Reconstruction
