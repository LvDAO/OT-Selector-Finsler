import OTSelector.Reconstruction.FinslerOriginalCampbellMeanFromPalmBundle
import OTSelector.Reconstruction.FinslerOriginalTileLaneDischarge
import OTSelector.Reconstruction.FinslerOriginalFrozenStationaryPressureIdentification

/-!
# Simplifying the readout-side binders of the V11 endgame

The V11 endgame (`FinslerOriginalPaperTheoremFinalV11`, readout binders at
`Groot`, `hgt`, `hdecomp`) carries a population covering identity whose
statement quantifies `(f : (↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) (t : ℝ)` although neither
the probe `f` nor the tilt `t` occurs in the identity: both sides are built from
`Groot`, the population seed pieces and the tile index only.  This module

* names the genuinely `f`-`t`-free proposition (`PopulationAtlasCovering`) and
  proves it equivalent to the V11 form of `hdecomp` (both directions are
  immediate; the V11 quantification is vacuous);
* records that the repo already proves the covering identity from the
  cell-refinement hypothesis: `T.PieceCellRefinement (q := q) Groot` together
  with the finite atlas tail identity implies it
  (`campbellAveragedFrozenCost_eq_tileSum_of_cell_refinement` of
  `FinslerOriginalTileRefinementCounting`), so V11's `hdecomp` can be replaced
  by those two named measure-theoretic inputs instead of being assumed;
* feeds the simplified binder into
  `frozenCampbellMeanIdentification_sceneCloud_of_palmSampleLaw_and_bundle`
  (two wrappers: one taking the `f`-`t`-free covering identity, one taking the
  cell-refinement plus tail producers directly).

The other two readout binders are *not* vacuous and are not simplified here:
`Groot : ℕ → (ℚ → M) → ℝ` is genuine root data, and `hgt` relates the
`f`-`t`-dependent frozen readout `frozenRootedCostReadout … f t` (which uses
`f` and `t` through the frozen matching `Mst` and the tilt prefactor) to the
glued atlas root `atlasPiecewiseRoot Seed a κ lambda Groot`.

No sorry, admit or added axiom occurs.
-/

open Set Function Matrix Filter MeasureTheory ProbabilityTheory Manifold Module
  OTSelector.Probability
open OTSelector.Geometry
open OTSelector.PointProcess OTSelector.PointProcess.StationaryForwardMatching
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
open OTSelector.PointProcess OTSelector.PointProcess.StationaryForwardMatching
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

/-! ## 1. The f-t-free form of the covering identity -/

/-- **The population covering identity without the vacuous quantifiers.**  The
V11 binder `hdecomp` quantifies every probe `f` and tilt `t` although neither
occurs in the identity; this is that identity itself: the Campbell series of the
atlas frozen root `G` equals the finite sum of the per-tile population Campbell
values. -/
def PopulationAtlasCovering (T : D.TaylorTiles ε) (q : ℝ)
    (G : ℕ → (ℚ → M) → ℝ) : Prop :=
  (∑' j, ∫ z in populationSeedRootPiece P a κ lambda j,
      populationAtlasTheta P a κ lambda j z ^ (-2 / q) * G j z ∂lambda) =
    ∑ c : T.Index, T.tilePopValue (P := P) (a := a) (κ := κ)
      (lambda := lambda) (q := q) G c

/-- **The V11 form of `hdecomp` is exactly the f-t-free covering identity.**  The
quantification over probes and tilts is vacuous in both directions: the forward
direction instantiates an arbitrary probe and tilt, and the reverse direction
ignores them. -/
theorem populationAtlasCovering_iff_hdecomp
    (T : D.TaylorTiles ε) {A B : Set M} (G : ℕ → (ℚ → M) → ℝ) :
    (∀ (f : (↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) (t : ℝ),
      (∑' j, ∫ z in populationSeedRootPiece P a κ lambda j,
          populationAtlasTheta P a κ lambda j z ^ (-2 / q) * G j z ∂lambda) =
        (∑ c : T.Index, T.tilePopValue (P := P) (a := a) (κ := κ)
          (lambda := lambda) (q := q) G c)) ↔
      PopulationAtlasCovering (P := P) (a := a) (κ := κ) (lambda := lambda)
        (D := D) T q G :=
  ⟨fun h => h (Classical.arbitrary _) 0,
    fun h _ _ => h⟩

/-! ## 2. The covering identity from cell refinement -/

/-- **The f-t-free covering identity from the cell-refinement hypothesis.**  This
is `campbellAveragedFrozenCost_eq_tileSum_of_cell_refinement`: the per-piece
cell-refinement integral identity and the vanishing of the atlas tail outside the
finite retained coefficient family give the covering identity. -/
theorem populationAtlasCovering_of_cellRefinement
    (T : D.TaylorTiles ε) (G : ℕ → (ℚ → M) → ℝ)
    (hrefine : T.PieceCellRefinement (q := q) G)
    (htail : (∑' j, ∫ z in populationSeedRootPiece P a κ lambda j,
        populationAtlasTheta P a κ lambda j z ^ (-2 / q) * G j z ∂lambda) =
      ∑ i : Fin D.haar.continuous.count,
        ∫ z in populationSeedRootPiece P a κ lambda
            (D.haar.continuous.coefficient i).seedIndex,
          populationAtlasTheta P a κ lambda
              (D.haar.continuous.coefficient i).seedIndex z ^ (-2 / q) *
            G (D.haar.continuous.coefficient i).seedIndex z ∂lambda) :
    PopulationAtlasCovering (P := P) (a := a) (κ := κ) (lambda := lambda)
      (D := D) T q G :=
  campbellAveragedFrozenCost_eq_tileSum_of_cell_refinement (T := T) G hrefine htail

/-- **The V11 form of `hdecomp` from cell refinement.**  The vacuous
quantification is harmless here: the repo producer
`hdecomp_of_cell_refinement` already emits the V11 binder, and this is its
f-t-free restatement. -/
theorem hdecomp_of_cellRefinement
    (T : D.TaylorTiles ε) {A B : Set M} (G : ℕ → (ℚ → M) → ℝ)
    (hrefine : T.PieceCellRefinement (q := q) G)
    (htail : (∑' j, ∫ z in populationSeedRootPiece P a κ lambda j,
        populationAtlasTheta P a κ lambda j z ^ (-2 / q) * G j z ∂lambda) =
      ∑ i : Fin D.haar.continuous.count,
        ∫ z in populationSeedRootPiece P a κ lambda
            (D.haar.continuous.coefficient i).seedIndex,
          populationAtlasTheta P a κ lambda
              (D.haar.continuous.coefficient i).seedIndex z ^ (-2 / q) *
            G (D.haar.continuous.coefficient i).seedIndex z ∂lambda) :
    ∀ (f : (↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) (t : ℝ),
      (∑' j, ∫ z in populationSeedRootPiece P a κ lambda j,
          populationAtlasTheta P a κ lambda j z ^ (-2 / q) * G j z ∂lambda) =
        ∑ c : T.Index, T.tilePopValue (P := P) (a := a) (κ := κ)
          (lambda := lambda) (q := q) G c :=
  hdecomp_of_cell_refinement (T := T) (K := A ∪ B) (q := q) G hrefine htail

/-! ## 3. Feeding the simplified binder to the Palm-bundle producer -/

/-- **The lane hId from the simplified, f-t-free covering identity.**  This is
`frozenCampbellMeanIdentification_sceneCloud_of_palmSampleLaw_and_bundle` with
the vacuous binder `hdecomp` replaced by the f-t-free covering identity: only
`hint`, `hgt` and the covering identity remain readout-side inputs. -/
theorem frozenCampbellMeanIdentification_sceneCloud_of_palmSampleLaw_and_bundle_of_covering
    (T : D.TaylorTiles ε) {A B : Set M}
    (pcloud qcloud : ∀ n, Fin (n + 1) → M)
    (base : ∀ n, Fin (n + 1) → T.Index → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (G : ℕ → (ℚ → M) → ℝ)
    (bundle : SceneCloudAnalyticLaneBundle (P := P) (a := a) (κ := κ)
      (lambda := lambda) (D := D) (ε := ε) (T := T) (A := A) (B := B)
      pcloud qcloud base G)
    (g : ((↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) → ℝ → (ℚ → M) → ℝ)
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _instCoveringBundleMetric : MetricSpace M := F.metricSpace;
      LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))
    (hint : ∀ (f : (↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) (t : ℝ) (n : ℕ) (c : T.Index),
      Integrable (T.tileFrozenCost (fun s i ↦ (sceneCloudX pcloud) n i s)
        (fun s i ↦ (sceneCloudY qcloud) n i s)
        (fun s c' ↦ normalizedProbe (K := A ∪ B) base t n s c')
        ((uniformTilePlan (fun n ↦ Fin (n + 1))) n) (tileScale n) t c)
        (sceneCloudSample n))
    (hgt : ∀ (f : (↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) (t : ℝ),
      g f t = atlasPiecewiseRoot P a κ lambda G)
    (hcovering : PopulationAtlasCovering (P := P) (a := a) (κ := κ)
      (lambda := lambda) (D := D) T q G)
    (hlaw : ∀ (f : (↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) (t : ℝ) (c : T.Index),
      T.TilePalmSampleLaw (ε := ε) f t sceneCloudSample (sceneCloudX pcloud)
        (sceneCloudY qcloud) tileScale c
        (fun _ ↦ T.tilePopValue (P := P) (a := a) (κ := κ) (lambda := lambda)
          (q := q) G c)) :
    RootedTileCampbellMeanIdentification P a κ lambda g q sceneCloudSample
      (hprobFrozenCostFamily (K := A ∪ B) T (sceneCloudX pcloud) (sceneCloudY qcloud)
        base (uniformTilePlan (fun n ↦ Fin (n + 1))) tileScale) T.Index :=
  frozenCampbellMeanIdentification_sceneCloud_of_palmSampleLaw_and_bundle
    (T := T) (A := A) (B := B) pcloud qcloud base G bundle g hF hcomplete hu
    ha hinj hint hgt (fun _ _ => hcovering) hlaw

/-- **The lane hId from cell refinement directly.**  The covering identity is not
even an input: the per-piece cell-refinement identity `T.PieceCellRefinement`
and the finite atlas tail identity produce it, and the Palm-bundle producer
consumes it. -/
theorem frozenCampbellMeanIdentification_sceneCloud_of_palmSampleLaw_and_bundle_of_cellRefinement
    (T : D.TaylorTiles ε) {A B : Set M}
    (pcloud qcloud : ∀ n, Fin (n + 1) → M)
    (base : ∀ n, Fin (n + 1) → T.Index → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (G : ℕ → (ℚ → M) → ℝ)
    (bundle : SceneCloudAnalyticLaneBundle (P := P) (a := a) (κ := κ)
      (lambda := lambda) (D := D) (ε := ε) (T := T) (A := A) (B := B)
      pcloud qcloud base G)
    (g : ((↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) → ℝ → (ℚ → M) → ℝ)
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _instCellRefinementBundleMetric : MetricSpace M := F.metricSpace;
      LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))
    (hint : ∀ (f : (↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) (t : ℝ) (n : ℕ) (c : T.Index),
      Integrable (T.tileFrozenCost (fun s i ↦ (sceneCloudX pcloud) n i s)
        (fun s i ↦ (sceneCloudY qcloud) n i s)
        (fun s c' ↦ normalizedProbe (K := A ∪ B) base t n s c')
        ((uniformTilePlan (fun n ↦ Fin (n + 1))) n) (tileScale n) t c)
        (sceneCloudSample n))
    (hgt : ∀ (f : (↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) (t : ℝ),
      g f t = atlasPiecewiseRoot P a κ lambda G)
    (hrefine : T.PieceCellRefinement (q := q) G)
    (htail : (∑' j, ∫ z in populationSeedRootPiece P a κ lambda j,
        populationAtlasTheta P a κ lambda j z ^ (-2 / q) * G j z ∂lambda) =
      ∑ i : Fin D.haar.continuous.count,
        ∫ z in populationSeedRootPiece P a κ lambda
            (D.haar.continuous.coefficient i).seedIndex,
          populationAtlasTheta P a κ lambda
              (D.haar.continuous.coefficient i).seedIndex z ^ (-2 / q) *
            G (D.haar.continuous.coefficient i).seedIndex z ∂lambda)
    (hlaw : ∀ (f : (↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) (t : ℝ) (c : T.Index),
      T.TilePalmSampleLaw (ε := ε) f t sceneCloudSample (sceneCloudX pcloud)
        (sceneCloudY qcloud) tileScale c
        (fun _ ↦ T.tilePopValue (P := P) (a := a) (κ := κ) (lambda := lambda)
          (q := q) G c)) :
    RootedTileCampbellMeanIdentification P a κ lambda g q sceneCloudSample
      (hprobFrozenCostFamily (K := A ∪ B) T (sceneCloudX pcloud) (sceneCloudY qcloud)
        base (uniformTilePlan (fun n ↦ Fin (n + 1))) tileScale) T.Index :=
  frozenCampbellMeanIdentification_sceneCloud_of_palmSampleLaw_and_bundle_of_covering
    T pcloud qcloud base G bundle g hF hcomplete hu ha hinj hint hgt
    (populationAtlasCovering_of_cellRefinement (P := P) (a := a) (κ := κ)
      (lambda := lambda) (D := D) T G hrefine htail) hlaw

/-! ## 4. The hgt binder: the frozen readout is itself a glued atlas root -/

/-- **The frozen readout is the first-owner gluing of its own root family.**  The
definition of `frozenRootedCostReadout` is the same `if ∃ j, z ∈ piece j then … else 0`
gluing as `atlasPiecewiseRoot` of the `f`-`t`-dependent root family
`j ↦ rootedFrozenIntegrand … f t j`.  This holds by definition; it shows that
`hgt` compares two first-owner gluings and is therefore equivalent to a
pointwise-on-piece identification, recorded next. -/
theorem frozenRootedCostReadout_eq_atlasPiecewiseRoot
    {A B : Set M}
    (α β : Measure OTSelector.UnitMark)
    (coef : FinalProbeSpace A B → ℕ → (ℚ → M) → ℝ → ℝ → ℝ)
    (probeFam : FinalProbeSpace A B → ℕ → (ℚ → M) →
      MarkedCloudPoint → MarkedCloudPoint → ℝ)
    (Mst : FinalProbeSpace A B → ℝ → ℕ → (ℚ → M) →
      StationaryForwardMatching α β)
    (q : ℝ) (f : FinalProbeSpace A B) (t : ℝ) :
    frozenRootedCostReadout (F := F) (u := u) (Seed := P) (a := a) (κ := κ)
        (lambda := lambda) (Z := ℚ → M) (A := A) (B := B) α β coef probeFam
        Mst q f t =
      atlasPiecewiseRoot P a κ lambda
        (fun j z ↦ rootedFrozenIntegrand (K := A ∪ B) α β P a κ lambda
          (fun φ' _ j z ↦ coef φ' j z) (fun φ' _ j z ↦ probeFam φ' j z)
          Mst q t f j z) := by
  unfold frozenRootedCostReadout rootedFrozenPieceIntegrand atlasPiecewiseRoot
  rfl

/-- **The glued root is zero off the atlas.**  At a point owned by no selected
population seed piece the first-owner gluing vanishes. -/
theorem atlasPiecewiseRoot_of_not_mem
    (G : ℕ → (ℚ → M) → ℝ) {z : ℚ → M}
    (hz : ¬ ∃ j : ℕ, z ∈ populationSeedRootPiece P a κ lambda j) :
    atlasPiecewiseRoot P a κ lambda G z = 0 := by
  unfold atlasPiecewiseRoot
  rw [dif_neg hz]

/-- **The hgt binder is a per-piece pointwise readout identification.**  Because
both sides of V11's `hgt` are first-owner gluings and the gluing is zero off the
atlas, the `∀ f t` equality of functions is equivalent to its value on each
population seed piece: on the piece `j`, the frozen integrand of the lane must
be the piece-`j` member of `G`.  No glued function and no function equality
occurs in the simplified form.  Note that this is *equivalent* to `hgt`: the
frozen integrand does depend on `f` and `t` (through `Mst` and the tilt
prefactor), so the per-piece identity is the genuine F14 content of `hgt`, not a
vacuous restatement. -/
theorem hgt_iff_piecewise
    {A B : Set M}
    (α β : Measure OTSelector.UnitMark)
    (coef : FinalProbeSpace A B → ℕ → (ℚ → M) → ℝ → ℝ → ℝ)
    (probeFam : FinalProbeSpace A B → ℕ → (ℚ → M) →
      MarkedCloudPoint → MarkedCloudPoint → ℝ)
    (Mst : FinalProbeSpace A B → ℝ → ℕ → (ℚ → M) →
      StationaryForwardMatching α β)
    (q : ℝ) (G : ℕ → (ℚ → M) → ℝ) :
    (∀ (f : (↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) (t : ℝ),
      frozenRootedCostReadout (F := F) (u := u) (Seed := P) (a := a)
          (κ := κ) (lambda := lambda) (Z := ℚ → M) (A := A) (B := B)
          α β coef probeFam Mst q f t =
        atlasPiecewiseRoot P a κ lambda G) ↔
      (∀ (f : (↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) (t : ℝ) (j : ℕ) (z : ℚ → M),
        z ∈ populationSeedRootPiece P a κ lambda j →
          frozenRootedCostReadout (F := F) (u := u) (Seed := P) (a := a)
            (κ := κ) (lambda := lambda) (Z := ℚ → M) (A := A) (B := B)
            α β coef probeFam Mst q f t z = G j z) := by
  constructor
  · intro h f t j z hz
    have h1 := congrFun (h f t) z
    rw [frozenRootedCostReadout_eq_atlasPiecewiseRoot (A := A) (B := B) α β
      coef probeFam Mst q f t] at h1
    rw [atlasPiecewiseRoot_of_mem P a κ lambda G hz] at h1
    rw [atlasPiecewiseRoot_of_mem P a κ lambda
      (fun j z ↦ rootedFrozenIntegrand (K := A ∪ B) α β P a κ lambda
        (fun φ' _ j z ↦ coef φ' j z) (fun φ' _ j z ↦ probeFam φ' j z)
        Mst q t f j z) hz] at h1
    rw [frozenRootedCostReadout_eq_atlasPiecewiseRoot (A := A) (B := B) α β
      coef probeFam Mst q f t]
    rw [atlasPiecewiseRoot_of_mem P a κ lambda
      (fun j z ↦ rootedFrozenIntegrand (K := A ∪ B) α β P a κ lambda
        (fun φ' _ j z ↦ coef φ' j z) (fun φ' _ j z ↦ probeFam φ' j z)
        Mst q t f j z) hz]
    exact h1
  · intro h f t
    funext z
    by_cases hz : ∃ j : ℕ, z ∈ populationSeedRootPiece P a κ lambda j
    · obtain ⟨j, hj⟩ := hz
      rw [atlasPiecewiseRoot_of_mem P a κ lambda G hj]
      exact h f t j z hj
    · rw [frozenRootedCostReadout_eq_atlasPiecewiseRoot (A := A) (B := B) α β
        coef probeFam Mst q f t]
      rw [atlasPiecewiseRoot_of_not_mem (P := P) (a := a) (κ := κ)
        (lambda := lambda) G hz]
      exact atlasPiecewiseRoot_of_not_mem (P := P) (a := a) (κ := κ)
        (lambda := lambda)
        (fun j z ↦ rootedFrozenIntegrand (K := A ∪ B) α β P a κ lambda
          (fun φ' _ j z ↦ coef φ' j z) (fun φ' _ j z ↦ probeFam φ' j z)
          Mst q t f j z) hz

end OTSelector.Reconstruction

