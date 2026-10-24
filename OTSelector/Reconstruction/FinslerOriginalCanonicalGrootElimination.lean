import OTSelector.Reconstruction.FinslerOriginalReadoutDecompositionSimplification
import OTSelector.Reconstruction.FinslerOriginalSceneCloudFiniteIntegrability
import OTSelector.Reconstruction.FinslerOriginalRootedTileCampbellMean
import OTSelector.Reconstruction.FinslerOriginalTileMeanValues
import OTSelector.Reconstruction.FinslerOriginalTileCountingConvergence
import OTSelector.Reconstruction.FinslerOriginalTileRefinementCounting

/-!
# Eliminating the atlas root family Groot and the gluing binder hgt

The V11 endgame carries three readout-side binders: the atlas root family
Groot : N -> (Q -> M) -> R, the gluing identity hgt relating the frozen readout
frozenRootedCostReadout to atlasPiecewiseRoot of Groot, and the population
covering identity hdecomp.  The previous module
(FinslerOriginalReadoutDecompositionSimplification) proved that the frozen
readout is itself the first-owner gluing of an (f,t)-dependent root family and
that V11's hdecomp quantifies (f,t) vacuously.  This module pushes the
simplification to its conclusion:

* it names the canonical rooted integrand family canonicalRootedIntegrand, i.e.
  the very family the readout glues.  At this family the gluing binder hgt
  becomes definitional, so
  frozenCampbellMeanIdentification_sceneCloud_of_canonicalRootedIntegrand
  carries no Groot and no hgt binder: both are eliminated;
* it names the resulting (f,t)-indexed covering identity
  (CanonicalRootedCovering), the canonical analogue of V11's hdecomp, and
  proves it from per-(f,t) cell refinement and vanishing atlas tails;
* it names the two resulting probability-side predicates at the canonical
  family: the canonical Palm sample law (CanonicalRootedTilePalmLaw, the
  canonical analogue of V11's hlaw) and the canonical Palm LLN
  (CanonicalRootedTileMeanLaw, the canonical analogue of
  PalmSideLowerLaneRootedTileMeanLaw);
* it proves the canonical Campbell value identity and the lane hId
  RootedTileCampbellMeanIdentification for the frozen readout, consuming only
  the canonical covering identity, the canonical Palm LLN and the geometric lane
  data (the frozen-cost integrability is discharged by finite integrability on
  the scene cloud).

The (f,t)-dependence of the canonical family is essential and is not a
trivialisation: rootedFrozenIntegrand depends on f and t through the frozen
stationary matching Mst and the tilt prefactor, so V11's hgt forced the whole
readout to be glued from a single (f,t)-independent root family, whereas here
each (f,t) glues its own family.  This is exactly what the outside quantification
of RootedTileCampbellMeanIdentification allows.

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
  {ε : ℝ} {A B : Set M}

/-! ## 1. The canonical rooted integrand: the family the readout glues -/

/-- **The canonical rooted integrand family of the frozen readout.**

At probe f and tilt t, the piece-j member is the Palm frozen integrand
rootedFrozenIntegrand of the lane's coefficient, probe and stationary matching
families at (f,t).  This is precisely the family whose first-owner gluing is
the frozen readout frozenRootedCostReadout ... f t, so using it as the atlas
root family makes the V11 gluing binder hgt definitional. -/
noncomputable def canonicalRootedIntegrand {A B : Set M}
    (α β : Measure OTSelector.UnitMark)
    (coef : FinalProbeSpace A B → ℕ → (ℚ → M) → ℝ → ℝ → ℝ)
    (probeFam : FinalProbeSpace A B → ℕ → (ℚ → M) →
      MarkedCloudPoint → MarkedCloudPoint → ℝ)
    (Mst : FinalProbeSpace A B → ℝ → ℕ → (ℚ → M) →
      StationaryForwardMatching α β)
    (q : ℝ) (f : FinalProbeSpace A B) (t : ℝ) : ℕ → (ℚ → M) → ℝ :=
  fun j z ↦ rootedFrozenIntegrand (K := A ∪ B) α β P a κ lambda
    (fun φ' _ j z ↦ coef φ' j z) (fun φ' _ j z ↦ probeFam φ' j z)
    Mst q t f j z

/-- **The gluing identity at the canonical family holds by definition.**  This is
the V11 binder hgt with Groot fixed to canonicalRootedIntegrand: the frozen
readout at (f,t) is the first-owner gluing of its own root family.  Since the
canonical family is (f,t)-dependent, the equality is definitional for each
(f,t); no hypothesis is left. -/
theorem frozenRootedCostReadout_eq_atlasPiecewiseRoot_canonical {A B : Set M}
    (α β : Measure OTSelector.UnitMark)
    (coef : FinalProbeSpace A B → ℕ → (ℚ → M) → ℝ → ℝ → ℝ)
    (probeFam : FinalProbeSpace A B → ℕ → (ℚ → M) →
      MarkedCloudPoint → MarkedCloudPoint → ℝ)
    (Mst : FinalProbeSpace A B → ℝ → ℕ → (ℚ → M) →
      StationaryForwardMatching α β)
    (q : ℝ) (f : FinalProbeSpace A B) (t : ℝ) :
    frozenRootedCostReadout (F := F) (u := u) (Seed := P) (a := a)
        (κ := κ) (lambda := lambda) (Z := ℚ → M) (A := A) (B := B) α β coef
        probeFam Mst q f t =
      atlasPiecewiseRoot P a κ lambda
        (canonicalRootedIntegrand (A := A) (B := B) (P := P) (a := a)
          (κ := κ) (lambda := lambda) α β coef probeFam Mst q f t) := by
  rw [frozenRootedCostReadout_eq_atlasPiecewiseRoot (A := A) (B := B) α β
    coef probeFam Mst q f t]
  rfl

/-! ## 2. The canonical covering and Palm-law predicates -/

/-- **The canonical covering identity at the rooted integrand.**

The (f,t)-indexed analogue of V11's hdecomp: for every probe f and tilt t, the
Campbell series of the canonical root family at (f,t) equals the finite sum of
its per-tile population Campbell values.  No single root family is required,
which is what the outside quantification of RootedTileCampbellMeanIdentification
permits.  The f-t-free V11 form is PopulationAtlasCovering for one fixed G. -/
abbrev CanonicalRootedCovering (T : D.TaylorTiles ε) (q : ℝ)
    {A B : Set M}
    (α β : Measure OTSelector.UnitMark)
    (coef : FinalProbeSpace A B → ℕ → (ℚ → M) → ℝ → ℝ → ℝ)
    (probeFam : FinalProbeSpace A B → ℕ → (ℚ → M) →
      MarkedCloudPoint → MarkedCloudPoint → ℝ)
    (Mst : FinalProbeSpace A B → ℝ → ℕ → (ℚ → M) →
      StationaryForwardMatching α β) : Prop :=
  ∀ (f : FinalProbeSpace A B) (t : ℝ),
    (∑' j, ∫ z in populationSeedRootPiece P a κ lambda j,
        populationAtlasTheta P a κ lambda j z ^ (-2 / q) *
          canonicalRootedIntegrand (A := A) (B := B) (P := P) (a := a)
            (κ := κ) (lambda := lambda) α β coef probeFam Mst q f t j z
          ∂lambda) =
      ∑ c : T.Index, T.tilePopValue (P := P) (a := a) (κ := κ)
        (lambda := lambda) (q := q)
        (canonicalRootedIntegrand (A := A) (B := B) (P := P) (a := a)
          (κ := κ) (lambda := lambda) α β coef probeFam Mst q f t) c

/-- **The canonical Palm sample law.**

The (f,t)-indexed analogue of V11's hlaw: at every retained tile, the
scene-cloud empirical frozen tile mean obeys the Palm sample law with population
value the tile Campbell value of the canonical root family at (f,t).  The
population value now depends on (f,t); this is the canonical form of the
TilePalmSampleLaw input of the lower lane. -/
abbrev CanonicalRootedTilePalmLaw (T : D.TaylorTiles ε)
    (pcloud qcloud : ∀ n, Fin (n + 1) → M)
    (base : ∀ n, Fin (n + 1) → T.Index → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (q : ℝ) {A B : Set M}
    (α β : Measure OTSelector.UnitMark)
    (coef : FinalProbeSpace A B → ℕ → (ℚ → M) → ℝ → ℝ → ℝ)
    (probeFam : FinalProbeSpace A B → ℕ → (ℚ → M) →
      MarkedCloudPoint → MarkedCloudPoint → ℝ)
    (Mst : FinalProbeSpace A B → ℝ → ℕ → (ℚ → M) →
      StationaryForwardMatching α β) : Type _ :=
  ∀ (f : FinalProbeSpace A B) (t : ℝ) (c : T.Index),
    T.TilePalmSampleLaw (ε := ε) f t sceneCloudSample (sceneCloudX pcloud)
      (sceneCloudY qcloud) tileScale c
      (fun _ ↦ T.tilePopValue (P := P) (a := a) (κ := κ) (lambda := lambda)
        (q := q) (canonicalRootedIntegrand (A := A) (B := B) (P := P) (a := a)
          (κ := κ) (lambda := lambda) α β coef probeFam Mst q f t) c)

/-- **The canonical Palm LLN (paper F16) at the rooted integrand.**

The (f,t)-indexed analogue of PalmSideLowerLaneRootedTileMeanLaw: the counted
per-tile empirical frozen means converge to the tile Campbell values of the
canonical root family at (f,t), with summable total error.  This is the only
remaining probabilistic input of the canonical lane. -/
abbrev CanonicalRootedTileMeanLaw (T : D.TaylorTiles ε)
    (pcloud qcloud : ∀ n, Fin (n + 1) → M)
    (base : ∀ n, Fin (n + 1) → T.Index → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (q : ℝ) {A B : Set M}
    (α β : Measure OTSelector.UnitMark)
    (coef : FinalProbeSpace A B → ℕ → (ℚ → M) → ℝ → ℝ → ℝ)
    (probeFam : FinalProbeSpace A B → ℕ → (ℚ → M) →
      MarkedCloudPoint → MarkedCloudPoint → ℝ)
    (Mst : FinalProbeSpace A B → ℝ → ℕ → (ℚ → M) →
      StationaryForwardMatching α β) : Prop :=
  T.RootedTileMeanConvergence
    (fun (f : FinalProbeSpace A B) (t : ℝ) (c : T.Index) ↦
      T.tilePopValue (P := P) (a := a) (κ := κ) (lambda := lambda) (q := q)
        (canonicalRootedIntegrand (A := A) (B := B) (P := P) (a := a)
          (κ := κ) (lambda := lambda) α β coef probeFam Mst q f t) c)
    sceneCloudSample (sceneCloudX pcloud) (sceneCloudY qcloud) tileScale
    (fun f t n s c' ↦ normalizedProbe (K := A ∪ B) base t n s c')
    (uniformTilePlan (fun n ↦ Fin (n + 1)))

/-! ## 3. The canonical covering identity from cell refinement -/

/-- **The canonical covering identity from per-(f,t) cell refinement.**  If every
canonical root family refines the population seed pieces into the retained tile
cells and its atlas tail beyond the finite retained coefficient family vanishes,
then the canonical covering identity holds.  This is the (f,t)-indexed form of
campbellAveragedFrozenCost_eq_tileSum_of_cell_refinement; it removes V11's
hdecomp in favour of two named measure-theoretic producers. -/
theorem canonicalRootedCovering_of_cellRefinement {A B : Set M}
    (T : D.TaylorTiles ε) (q : ℝ)
    (α β : Measure OTSelector.UnitMark)
    (coef : FinalProbeSpace A B → ℕ → (ℚ → M) → ℝ → ℝ → ℝ)
    (probeFam : FinalProbeSpace A B → ℕ → (ℚ → M) →
      MarkedCloudPoint → MarkedCloudPoint → ℝ)
    (Mst : FinalProbeSpace A B → ℝ → ℕ → (ℚ → M) →
      StationaryForwardMatching α β)
    (hrefine : ∀ (f : FinalProbeSpace A B) (t : ℝ),
      T.PieceCellRefinement (q := q)
        (canonicalRootedIntegrand (A := A) (B := B) (P := P) (a := a)
          (κ := κ) (lambda := lambda) α β coef probeFam Mst q f t))
    (htail : ∀ (f : FinalProbeSpace A B) (t : ℝ),
      (∑' j, ∫ z in populationSeedRootPiece P a κ lambda j,
          populationAtlasTheta P a κ lambda j z ^ (-2 / q) *
            canonicalRootedIntegrand (A := A) (B := B) (P := P) (a := a)
              (κ := κ) (lambda := lambda) α β coef probeFam Mst q f t j z
            ∂lambda) =
        ∑ i : Fin D.haar.continuous.count,
          ∫ z in populationSeedRootPiece P a κ lambda
              (D.haar.continuous.coefficient i).seedIndex,
            populationAtlasTheta P a κ lambda
                (D.haar.continuous.coefficient i).seedIndex z ^ (-2 / q) *
              canonicalRootedIntegrand (A := A) (B := B) (P := P) (a := a)
                (κ := κ) (lambda := lambda) α β coef probeFam Mst q f t
                (D.haar.continuous.coefficient i).seedIndex z ∂lambda) :
    CanonicalRootedCovering (A := A) (B := B) T q α β coef probeFam Mst :=
  fun f t ↦ campbellAveragedFrozenCost_eq_tileSum_of_cell_refinement (T := T)
    (q := q) (P := P) (a := a) (κ := κ) (lambda := lambda)
    (canonicalRootedIntegrand (A := A) (B := B) (P := P) (a := a) (κ := κ)
      (lambda := lambda) α β coef probeFam Mst q f t)
    (hrefine f t) (htail f t)

/-! ## 4. The canonical Campbell value identity -/

/-- **The Campbell-averaged frozen cost is the sum of the canonical tile values.**

From the canonical covering identity and the atlas scene bridge: for every probe
and tilt, the Campbell-averaged frozen cost of the frozen readout equals the
finite sum of the per-tile population Campbell values of the canonical root
family at (f,t).  This is the per-(f,t) form of cam = sum tilePopValue and the
key input of the per-tile mean bookkeeping. -/
theorem rootedReadout_campbellValue_canonical {A B : Set M}
    (T : D.TaylorTiles ε) (q : ℝ)
    (α β : Measure OTSelector.UnitMark)
    (coef : FinalProbeSpace A B → ℕ → (ℚ → M) → ℝ → ℝ → ℝ)
    (probeFam : FinalProbeSpace A B → ℕ → (ℚ → M) →
      MarkedCloudPoint → MarkedCloudPoint → ℝ)
    (Mst : FinalProbeSpace A B → ℝ → ℕ → (ℚ → M) →
      StationaryForwardMatching α β)
    (hcovering : CanonicalRootedCovering (A := A) (B := B) T q α β coef
      probeFam Mst)
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _instCanonicalValueMetric : MetricSpace M := F.metricSpace;
      LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val))) :
    ∀ (f : FinalProbeSpace A B) (t : ℝ),
      campbellAveragedFrozenCost P a κ lambda
        (frozenRootedCostReadout (F := F) (u := u) (Seed := P) (a := a)
          (κ := κ) (lambda := lambda) (Z := ℚ → M) (A := A) (B := B)
          α β coef probeFam Mst q f t) q =
      ∑ c : T.Index, T.tilePopValue (P := P) (a := a) (κ := κ)
        (lambda := lambda) (q := q)
        (canonicalRootedIntegrand (A := A) (B := B) (P := P) (a := a)
          (κ := κ) (lambda := lambda) α β coef probeFam Mst q f t) c := by
  intro f t
  rw [frozenRootedCostReadout_eq_atlasPiecewiseRoot_canonical (A := A) (B := B)
    α β coef probeFam Mst q f t]
  simpa using campbellAveragedFrozenCost_eq_tileSum_add_tail (T := T) (q := q)
    (P := P) (a := a) (κ := κ) (lambda := lambda)
    (canonicalRootedIntegrand (A := A) (B := B) (P := P) (a := a) (κ := κ)
      (lambda := lambda) α β coef probeFam Mst q f t)
    hF hcomplete hu ha hinj (tail := 0) (by
      rw [add_zero]
      exact hcovering f t)

/-! ## 5. The lane hId at the canonical rooted integrand -/

/-- **The frozen cost family of the hprob lane is the tile frozen cost family.**
Definitional restatement used to match the conclusion of
rootedTileCampbellMeanIdentification_of_tile_means with the V11 frozen cost
family hprobFrozenCostFamily. -/
theorem hprobFrozenCostFamily_eq_tileFrozenCostFamily
    (T : D.TaylorTiles ε) {A B : Set M}
    (pcloud qcloud : ∀ n, Fin (n + 1) → M)
    (base : ∀ n, Fin (n + 1) → T.Index → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) :
    hprobFrozenCostFamily (K := A ∪ B) (T := T) (sceneCloudX pcloud)
        (sceneCloudY qcloud) base (uniformTilePlan (fun n ↦ Fin (n + 1)))
        tileScale =
      (fun (f : FinalProbeSpace A B) (t : ℝ) (n : ℕ) (s : Fin (n + 1)) ↦
        fractionalAssignmentCost
          (T.originalFrozenCoreMatrix (fun i ↦ (sceneCloudX pcloud) n i s)
            (fun i ↦ (sceneCloudY qcloud) n i s) (tileScale n) t
            (fun c' ↦ normalizedProbe (K := A ∪ B) base t n s c'))
          ((uniformTilePlan (fun n ↦ Fin (n + 1))) n s) /
          ((n + 1 : ℕ) : ℝ)) := by
  unfold hprobFrozenCostFamily
  rfl

/-- **The lane hId at the canonical rooted integrand: Groot and hgt are
eliminated.**

RootedTileCampbellMeanIdentification quantifies (f,t) outside its existential
witnesses, so it suffices to know, for every probe and tilt, one root family
gluing the readout at that (f,t).  The canonical family
fun j z => rootedFrozenIntegrand ... f t j z does exactly this, and the V11
gluing binder hgt becomes definitional.  The remaining inputs are

* the canonical covering identity CanonicalRootedCovering (the (f,t)-indexed
  hdecomp, produced from cell refinement by
  canonicalRootedCovering_of_cellRefinement),
* the canonical Palm LLN CanonicalRootedTileMeanLaw (the (f,t)-indexed paper
  input F16),
* the geometric lane data (hF, hcomplete, hu, ha, hinj);

the frozen-cost integrability is discharged by finite integrability on the scene
cloud, and the identification of the hprob frozen cost family is definitional. -/
theorem frozenCampbellMeanIdentification_sceneCloud_of_canonicalRootedIntegrand
    (T : D.TaylorTiles ε) {A B : Set M}
    (pcloud qcloud : ∀ n, Fin (n + 1) → M)
    (base : ∀ n, Fin (n + 1) → T.Index → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (q : ℝ)
    (α β : Measure OTSelector.UnitMark)
    (coef : FinalProbeSpace A B → ℕ → (ℚ → M) → ℝ → ℝ → ℝ)
    (probeFam : FinalProbeSpace A B → ℕ → (ℚ → M) →
      MarkedCloudPoint → MarkedCloudPoint → ℝ)
    (Mst : FinalProbeSpace A B → ℝ → ℕ → (ℚ → M) →
      StationaryForwardMatching α β)
    (hcovering : CanonicalRootedCovering (A := A) (B := B) T q α β coef
      probeFam Mst)
    (hmean : CanonicalRootedTileMeanLaw (A := A) (B := B) T pcloud qcloud base
      q α β coef probeFam Mst)
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _instCanonicalIdMetric : MetricSpace M := F.metricSpace;
      LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val))) :
    RootedTileCampbellMeanIdentification (K := A ∪ B) P a κ lambda
      (frozenRootedCostReadout (F := F) (u := u) (Seed := P) (a := a)
        (κ := κ) (lambda := lambda) (Z := ℚ → M) (A := A) (B := B)
        α β coef probeFam Mst q) q sceneCloudSample
      (hprobFrozenCostFamily (K := A ∪ B) (T := T) (sceneCloudX pcloud)
        (sceneCloudY qcloud) base (uniformTilePlan (fun n ↦ Fin (n + 1)))
        tileScale) T.Index := by
  have h := rootedTileCampbellMeanIdentification_of_tile_means (T := T)
    (P := P) (a := a) (κ := κ) (lambda := lambda) (K := A ∪ B) (q := q)
    (X := sceneCloudX pcloud) (Y := sceneCloudY qcloud) (scale := tileScale)
    (hprobe := fun f t n s c' ↦ normalizedProbe (K := A ∪ B) base t n s c')
    (A := uniformTilePlan (fun n ↦ Fin (n + 1)))
    (g := frozenRootedCostReadout (F := F) (u := u) (Seed := P) (a := a)
      (κ := κ) (lambda := lambda) (Z := ℚ → M) (A := A) (B := B)
      α β coef probeFam Mst q)
    sceneCloudSample (fun f t n c ↦ integrable_sceneCloudSample n _)
    (rootedTileMeanCampbellValues_of_tile_mean_convergence (T := T) (P := P)
      (a := a) (κ := κ) (lambda := lambda) (K := A ∪ B) (q := q)
      (X := sceneCloudX pcloud) (Y := sceneCloudY qcloud) (scale := tileScale)
      (hprobe := fun f t n s c' ↦ normalizedProbe (K := A ∪ B) base t n s c')
      (A := uniformTilePlan (fun n ↦ Fin (n + 1)))
      (g := frozenRootedCostReadout (F := F) (u := u) (Seed := P) (a := a)
        (κ := κ) (lambda := lambda) (Z := ℚ → M) (A := A) (B := B)
        α β coef probeFam Mst q)
      sceneCloudSample
      (fun f t c ↦ T.tilePopValue (P := P) (a := a) (κ := κ) (lambda := lambda)
        (q := q) (canonicalRootedIntegrand (A := A) (B := B) (P := P) (a := a)
          (κ := κ) (lambda := lambda) α β coef probeFam Mst q f t) c)
      (rootedReadout_campbellValue_canonical (A := A) (B := B) T q α β coef
        probeFam Mst hcovering hF hcomplete hu ha hinj)
      (by
        unfold CanonicalRootedTileMeanLaw at hmean
        exact hmean))
  rw [hprobFrozenCostFamily_eq_tileFrozenCostFamily (A := A) (B := B) T
    pcloud qcloud base]
  exact h

end OTSelector.Reconstruction
