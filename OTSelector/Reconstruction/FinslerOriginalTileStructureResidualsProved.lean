import OTSelector.Reconstruction.FinslerSeedRootPartition
import OTSelector.Reconstruction.FinslerOriginalCanonicalCoveringFromAtlas

/-!
# The tile-structure residuals: integrability, tail collapse, and the root revision

FinslerOriginalCanonicalCoveringFromAtlas reduced the population covering
identity to three residuals: the a.e. piece/root-set revision hrev, the
integrability hInt of the weighted root integrand on each retained seed piece,
and the finite atlas-tail collapse htail.  This module discharges what is
provable and sharpens what is not.

## 1. hInt (integrability)

The repo's Measure.integrableOn_of_bounded only needs: the tested set has finite
measure (automatic, lambda is a finite measure), the integrand is a.e. strongly
measurable, and it is bounded on the tested set.  Hence the integrability
residual is NOT a separate analytic fact: it follows from (i) a.e.
AEstronlyMeasurable and (ii) a bound on the weighted root integrand.  We prove
this both for an arbitrary root family G and for the canonical rooted integrand
of the lane, and its per-(f,t) family form which is exactly hIntFam.

## 2. htail (tail collapse)

The retained coefficient family is Fin count with seed index map
i |-> (coefficient i).seedIndex.  If the root family vanishes outside the finite
set of retained seed indices, the atlas Campbell series is a finitely supported
tsum, so it collapses to the finite sum over the retained family
(tsum_eq_sum + Finset.sum_image).  The only extra input of the collapse to the
EXACT htail shape is injectivity of the retained seed-index map; without it the
right side counts a seed with its multiplicity, so the identity cannot hold in
that form for a nonzero family.  This is stated as hinjSeed.

## 3. hrev (the root revision)

The coefficient root set is genuinely arbitrary data: OriginalPopulationCoefficientCore
has a field roots : Set Z with roots_compact and roots_subset_piece only, so
piece subset roots a.e. is NOT a consequence of the tile structure (the
partition only covers roots, not the whole piece).  We prove:

* hrev holds trivially if the root set IS the piece (hrev_of_roots_eq_piece);
* hrev can be replaced by the strictly weaker, support-type residual
  hvan: the weighted root integrand vanishes pointwise on the piece off the
  root set.  pieceCellRefinement_of_vanishing_off_roots proves the per-piece
  cell refinement from hvan, measurable pieces, and integrability, using the
  indicator comparison piece.indicator F = union-of-cells.indicator F.

## 4. Composition

populationAtlasCovering_of_tileStructure_residualsProved proves the population
covering identity with hrev replaced by hvan and hInt replaced by measurability +
bound; canonicalRootedCovering_of_tileStructure_residualsProved is the
per-(f,t) canonical form, with htail produced from finite support.

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
  {ε : ℝ} {q : ℝ} {A B : Set M}

/-! ## 1. hInt: integrability from measurability and a bound -/

/-- **The weighted root integrand is integrable on a seed piece from a bound.**

Measurability plus boundedness imply the integrability residual hInt:
lambda is finite, so the tested seed piece has finite measure, and
Measure.integrableOn_of_bounded applies. -/
theorem integrableOn_weightedIntegrand_of_bounded
    (j : ℕ) (G : ℕ → (ℚ → M) → ℝ) {C : ℝ}
    (hmble : AEStronglyMeasurable (fun z ↦
      populationAtlasTheta P a κ lambda j z ^ (-2 / q) * G j z) lambda)
    (hbd : ∀ᵐ z ∂lambda.restrict (populationSeedRootPiece P a κ lambda j),
      ‖populationAtlasTheta P a κ lambda j z ^ (-2 / q) * G j z‖ ≤ C) :
    IntegrableOn (fun z ↦
      populationAtlasTheta P a κ lambda j z ^ (-2 / q) * G j z)
      (populationSeedRootPiece P a κ lambda j) lambda :=
  Measure.integrableOn_of_bounded (measure_ne_top lambda _) hmble hbd

/-- **The weighted canonical integrand is integrable on a seed piece from a
bound.**  This is the hInt residual for the lane's canonical family at one
retained seed index. -/
theorem integrableOn_canonicalIntegrand_of_bounded
    (α β : Measure OTSelector.UnitMark)
    (coef : FinalProbeSpace A B → ℕ → (ℚ → M) → ℝ → ℝ → ℝ)
    (probeFam : FinalProbeSpace A B → ℕ → (ℚ → M) →
      MarkedCloudPoint → MarkedCloudPoint → ℝ)
    (Mst : FinalProbeSpace A B → ℝ → ℕ → (ℚ → M) →
      StationaryForwardMatching α β)
    (f : FinalProbeSpace A B) (t : ℝ) (j : ℕ) {C : ℝ}
    (hmble : AEStronglyMeasurable (fun z ↦
      populationAtlasTheta P a κ lambda j z ^ (-2 / q) *
        canonicalRootedIntegrand (A := A) (B := B) (P := P) (a := a)
          (κ := κ) (lambda := lambda) α β coef probeFam Mst q f t j z) lambda)
    (hbd : ∀ᵐ z ∂lambda.restrict (populationSeedRootPiece P a κ lambda j),
      ‖populationAtlasTheta P a κ lambda j z ^ (-2 / q) *
        canonicalRootedIntegrand (A := A) (B := B) (P := P) (a := a)
          (κ := κ) (lambda := lambda) α β coef probeFam Mst q f t j z‖ ≤ C) :
    IntegrableOn (fun z ↦
      populationAtlasTheta P a κ lambda j z ^ (-2 / q) *
        canonicalRootedIntegrand (A := A) (B := B) (P := P) (a := a)
          (κ := κ) (lambda := lambda) α β coef probeFam Mst q f t j z)
      (populationSeedRootPiece P a κ lambda j) lambda :=
  Measure.integrableOn_of_bounded (measure_ne_top lambda _) hmble hbd

/-- **The per-(f,t) integrability family hIntFam, discharged.**  A family of
a.e. strongly measurable and a.e. bounded weighted canonical integrands gives
exactly the hIntFam binder of the covering residual theorem. -/
theorem integrableOn_canonicalIntegrand_family_of_bounded
    (α β : Measure OTSelector.UnitMark)
    (coef : FinalProbeSpace A B → ℕ → (ℚ → M) → ℝ → ℝ → ℝ)
    (probeFam : FinalProbeSpace A B → ℕ → (ℚ → M) →
      MarkedCloudPoint → MarkedCloudPoint → ℝ)
    (Mst : FinalProbeSpace A B → ℝ → ℕ → (ℚ → M) →
      StationaryForwardMatching α β) {C : ℝ}
    (hmble : ∀ (f : FinalProbeSpace A B) (t : ℝ)
      (i : Fin D.haar.continuous.count), AEStronglyMeasurable (fun z ↦
      populationAtlasTheta P a κ lambda
          (D.haar.continuous.coefficient i).seedIndex z ^ (-2 / q) *
        canonicalRootedIntegrand (A := A) (B := B) (P := P) (a := a)
          (κ := κ) (lambda := lambda) α β coef probeFam Mst q f t
          (D.haar.continuous.coefficient i).seedIndex z) lambda)
    (hbd : ∀ (f : FinalProbeSpace A B) (t : ℝ)
      (i : Fin D.haar.continuous.count),
      ∀ᵐ z ∂lambda.restrict (populationSeedRootPiece P a κ lambda
        (D.haar.continuous.coefficient i).seedIndex),
        ‖populationAtlasTheta P a κ lambda
            (D.haar.continuous.coefficient i).seedIndex z ^ (-2 / q) *
          canonicalRootedIntegrand (A := A) (B := B) (P := P) (a := a)
            (κ := κ) (lambda := lambda) α β coef probeFam Mst q f t
            (D.haar.continuous.coefficient i).seedIndex z‖ ≤ C) :
    ∀ (f : FinalProbeSpace A B) (t : ℝ)
      (i : Fin D.haar.continuous.count),
      IntegrableOn (fun z ↦
        populationAtlasTheta P a κ lambda
            (D.haar.continuous.coefficient i).seedIndex z ^ (-2 / q) *
          canonicalRootedIntegrand (A := A) (B := B) (P := P) (a := a)
            (κ := κ) (lambda := lambda) α β coef probeFam Mst q f t
            (D.haar.continuous.coefficient i).seedIndex z)
        (populationSeedRootPiece P a κ lambda
          (D.haar.continuous.coefficient i).seedIndex) lambda :=
  fun f t i ↦
    integrableOn_canonicalIntegrand_of_bounded (A := A) (B := B) α β coef
      probeFam Mst f t _ (hmble f t i) (hbd f t i)

/-! ## 2. htail: the atlas tail collapses from finite support -/

/-- **The finite atlas-tail collapse from finite support.**

If the root family vanishes outside the finite set of retained seed indices,
then the atlas Campbell series is a finitely supported tsum and collapses to
the finite sum over the retained coefficient family.  The map
i |-> (coefficient i).seedIndex must be injective for the collapse to have the
EXACT retained-collapse shape (otherwise the finite sum counts a repeated seed
with multiplicity). -/
theorem populationAtlasTail_collapse_of_finiteSupport
    (G : ℕ → (ℚ → M) → ℝ)
    (hinjSeed : Function.Injective (fun i : Fin D.haar.continuous.count ↦
      (D.haar.continuous.coefficient i).seedIndex))
    (hzero : ∀ j : ℕ,
      j ∉ Finset.univ.image (fun i : Fin D.haar.continuous.count ↦
        (D.haar.continuous.coefficient i).seedIndex) →
      ∀ z, G j z = 0) :
    (∑' j, ∫ z in populationSeedRootPiece P a κ lambda j,
        populationAtlasTheta P a κ lambda j z ^ (-2 / q) * G j z ∂lambda) =
      ∑ i : Fin D.haar.continuous.count,
        ∫ z in populationSeedRootPiece P a κ lambda
            (D.haar.continuous.coefficient i).seedIndex,
          populationAtlasTheta P a κ lambda
              (D.haar.continuous.coefficient i).seedIndex z ^ (-2 / q) *
            G (D.haar.continuous.coefficient i).seedIndex z ∂lambda := by
  have hterm : ∀ j : ℕ,
      j ∉ Finset.univ.image (fun i : Fin D.haar.continuous.count ↦
        (D.haar.continuous.coefficient i).seedIndex) →
      (∫ z in populationSeedRootPiece P a κ lambda j,
        populationAtlasTheta P a κ lambda j z ^ (-2 / q) * G j z ∂lambda) = 0 := by
    intro j hj
    have hfun : (fun z ↦ populationAtlasTheta P a κ lambda j z ^ (-2 / q) * G j z) =
        (fun _ ↦ (0 : ℝ)) := by
      funext z
      rw [hzero j hj z, mul_zero]
    rw [show (∫ z in populationSeedRootPiece P a κ lambda j,
        populationAtlasTheta P a κ lambda j z ^ (-2 / q) * G j z ∂lambda) =
        ∫ z in populationSeedRootPiece P a κ lambda j, (0 : ℝ) ∂lambda from by
      rw [hfun]]
    simp
  rw [tsum_eq_sum (s := Finset.univ.image (fun i : Fin D.haar.continuous.count ↦
    (D.haar.continuous.coefficient i).seedIndex)) hterm]
  rw [Finset.sum_image
    (f := fun j : ℕ ↦ ∫ z in populationSeedRootPiece P a κ lambda j,
      populationAtlasTheta P a κ lambda j z ^ (-2 / q) * G j z ∂lambda)
    (s := Finset.univ)
    (g := fun i : Fin D.haar.continuous.count ↦
      (D.haar.continuous.coefficient i).seedIndex)
    (fun i _ j _ hij ↦ hinjSeed hij)]

/-! ## 3. hrev: the root revision, and its strictly weaker replacement -/

/-- **hrev when the root set is the piece.**  If every retained coefficient's
root set is its seed piece, the a.e. revision hrev is immediate. -/
theorem hrev_of_roots_eq_piece
    (hpiece : ∀ j : ℕ, MeasurableSet (populationSeedRootPiece P a κ lambda j))
    (hroots : ∀ i : Fin D.haar.continuous.count,
      (D.haar.continuous.coefficient i).roots =
        populationSeedRootPiece P a κ lambda
          (D.haar.continuous.coefficient i).seedIndex) :
    ∀ i : Fin D.haar.continuous.count,
      ∀ᵐ z ∂lambda.restrict (populationSeedRootPiece P a κ lambda
        (D.haar.continuous.coefficient i).seedIndex),
        z ∈ (D.haar.continuous.coefficient i).roots := by
  intro i
  rw [hroots i]
  exact ae_restrict_mem (hpiece _)

/-- **The per-piece cell refinement from vanishing off the root set.**

This is the sharpened form of the hrev residual: the a.e. piece/root-set
identification is not needed at all if the weighted root integrand vanishes
pointwise on the piece off the root set.  The indicator of the piece and the
indicator of the union of the retained cells then agree identically, so their
integrals agree; additivity over the finite disjoint union of measurable cells
gives the refinement. -/
theorem pieceCellRefinement_of_vanishing_off_roots
    (T : D.TaylorTiles ε) (G : ℕ → (ℚ → M) → ℝ)
    (hpiece : ∀ i : Fin D.haar.continuous.count,
      MeasurableSet (populationSeedRootPiece P a κ lambda
        (D.haar.continuous.coefficient i).seedIndex))
    (hInt : ∀ i : Fin D.haar.continuous.count,
      IntegrableOn (fun z ↦
        populationAtlasTheta P a κ lambda
            (D.haar.continuous.coefficient i).seedIndex z ^ (-2 / q) *
          G (D.haar.continuous.coefficient i).seedIndex z)
        (populationSeedRootPiece P a κ lambda
          (D.haar.continuous.coefficient i).seedIndex) lambda)
    (hvan : ∀ (i : Fin D.haar.continuous.count) (z : ℚ → M),
      z ∈ populationSeedRootPiece P a κ lambda
          (D.haar.continuous.coefficient i).seedIndex →
      z ∉ (D.haar.continuous.coefficient i).roots →
      populationAtlasTheta P a κ lambda
          (D.haar.continuous.coefficient i).seedIndex z ^ (-2 / q) *
        G (D.haar.continuous.coefficient i).seedIndex z = 0) :
    T.PieceCellRefinement (q := q) G := by
  intro i
  have hU_eq : (⋃ k : Fin (T.partition i).count, (T.partition i).cell k) =
      (D.haar.continuous.coefficient i).roots := (T.partition i).union_eq
  have hU_sub : (⋃ k : Fin (T.partition i).count, (T.partition i).cell k) ⊆
      populationSeedRootPiece P a κ lambda
        (D.haar.continuous.coefficient i).seedIndex := by
    rw [hU_eq]
    exact (D.haar.continuous.coefficient i).roots_subset_piece
  have hmeasU : MeasurableSet
      (⋃ k : Fin (T.partition i).count, (T.partition i).cell k) :=
    MeasurableSet.iUnion (f := fun k : Fin (T.partition i).count ↦
      (T.partition i).cell k) (fun k ↦ (T.partition i).measurable_cell k)
  have hind : Set.indicator
      (populationSeedRootPiece P a κ lambda
        (D.haar.continuous.coefficient i).seedIndex)
      (fun z ↦ populationAtlasTheta P a κ lambda
          (D.haar.continuous.coefficient i).seedIndex z ^ (-2 / q) *
        G (D.haar.continuous.coefficient i).seedIndex z) =
      Set.indicator (⋃ k : Fin (T.partition i).count, (T.partition i).cell k)
        (fun z ↦ populationAtlasTheta P a κ lambda
            (D.haar.continuous.coefficient i).seedIndex z ^ (-2 / q) *
          G (D.haar.continuous.coefficient i).seedIndex z) := by
    funext z
    by_cases hz : z ∈ populationSeedRootPiece P a κ lambda
        (D.haar.continuous.coefficient i).seedIndex
    · by_cases hz2 : z ∈ (⋃ k : Fin (T.partition i).count, (T.partition i).cell k)
      · rw [Set.indicator_of_mem hz, Set.indicator_of_mem hz2]
      · have hroot : z ∉ (D.haar.continuous.coefficient i).roots := by
          rw [← hU_eq]
          exact hz2
        rw [Set.indicator_of_mem hz, Set.indicator_of_notMem hz2,
          hvan i z hz hroot]
    · have hz2 : z ∉ (⋃ k : Fin (T.partition i).count, (T.partition i).cell k) :=
        fun h ↦ hz (hU_sub h)
      rw [Set.indicator_of_notMem hz, Set.indicator_of_notMem hz2]
  calc (∫ z in populationSeedRootPiece P a κ lambda
        (D.haar.continuous.coefficient i).seedIndex,
        populationAtlasTheta P a κ lambda
            (D.haar.continuous.coefficient i).seedIndex z ^ (-2 / q) *
          G (D.haar.continuous.coefficient i).seedIndex z ∂lambda)
      = ∫ z, Set.indicator (populationSeedRootPiece P a κ lambda
          (D.haar.continuous.coefficient i).seedIndex)
          (fun z ↦ populationAtlasTheta P a κ lambda
              (D.haar.continuous.coefficient i).seedIndex z ^ (-2 / q) *
            G (D.haar.continuous.coefficient i).seedIndex z) z ∂lambda :=
        (MeasureTheory.integral_indicator (hpiece i)).symm
    _ = ∫ z, Set.indicator
          (⋃ k : Fin (T.partition i).count, (T.partition i).cell k)
          (fun z ↦ populationAtlasTheta P a κ lambda
              (D.haar.continuous.coefficient i).seedIndex z ^ (-2 / q) *
            G (D.haar.continuous.coefficient i).seedIndex z) z ∂lambda := by
        rw [hind]
    _ = ∫ z in (⋃ k : Fin (T.partition i).count, (T.partition i).cell k),
          populationAtlasTheta P a κ lambda
              (D.haar.continuous.coefficient i).seedIndex z ^ (-2 / q) *
            G (D.haar.continuous.coefficient i).seedIndex z ∂lambda :=
        MeasureTheory.integral_indicator hmeasU
    _ = ∑ k : Fin (T.partition i).count,
          ∫ z in (T.partition i).cell k,
            populationAtlasTheta P a κ lambda
                (D.haar.continuous.coefficient i).seedIndex z ^ (-2 / q) *
              G (D.haar.continuous.coefficient i).seedIndex z ∂lambda :=
        integral_iUnion_fintype
          (fun k : Fin (T.partition i).count ↦ (T.partition i).measurable_cell k)
          (T.partition i).disjoint
          (fun k ↦ (hInt i).mono_set ((Set.subset_iUnion
            (fun k : Fin (T.partition i).count ↦ (T.partition i).cell k) k).trans hU_sub))

/-! ## 4. Composed residuals: the covering identity -/

/-- **The population covering identity from the sharpened residuals.**

Same as populationAtlasCovering_of_tileStructure of
FinslerOriginalCanonicalCoveringFromAtlas, but with hrev replaced by the
vanishing-off-roots residual hvan. -/
theorem populationAtlasCovering_of_tileStructure_vanishing
    (T : D.TaylorTiles ε) (G : ℕ → (ℚ → M) → ℝ)
    (hpiece : ∀ i : Fin D.haar.continuous.count,
      MeasurableSet (populationSeedRootPiece P a κ lambda
        (D.haar.continuous.coefficient i).seedIndex))
    (hInt : ∀ i : Fin D.haar.continuous.count,
      IntegrableOn (fun z ↦
        populationAtlasTheta P a κ lambda
            (D.haar.continuous.coefficient i).seedIndex z ^ (-2 / q) *
          G (D.haar.continuous.coefficient i).seedIndex z)
        (populationSeedRootPiece P a κ lambda
          (D.haar.continuous.coefficient i).seedIndex) lambda)
    (hvan : ∀ (i : Fin D.haar.continuous.count) (z : ℚ → M),
      z ∈ populationSeedRootPiece P a κ lambda
          (D.haar.continuous.coefficient i).seedIndex →
      z ∉ (D.haar.continuous.coefficient i).roots →
      populationAtlasTheta P a κ lambda
          (D.haar.continuous.coefficient i).seedIndex z ^ (-2 / q) *
        G (D.haar.continuous.coefficient i).seedIndex z = 0)
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
  populationAtlasCovering_of_cellRefinement (T := T) (q := q) G
    (pieceCellRefinement_of_vanishing_off_roots (T := T) (q := q) G
      hpiece hInt hvan) htail

/-- **The population covering identity under explicit sufficient conditions
into checkable analytic hypotheses.**

hpiece is proved from the geometry (measurableSet_populationSeedRootPiece),
hInt is produced from a.e. strong measurability plus a bound, and htail from the
finite support of the atlas tail.  The only hypotheses left are: the
vanishing-off-roots support condition hvan, the measurability hmble, the bound
hbd, injectivity hinjSeed of the retained seed indices, and the finite support
hzero of the root family. -/
theorem populationAtlasCovering_of_tileStructure_residualsProved
    (T : D.TaylorTiles ε) (G : ℕ → (ℚ → M) → ℝ)
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _instTileResidualsMetric : MetricSpace M := F.metricSpace;
      LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))
    (hvan : ∀ (i : Fin D.haar.continuous.count) (z : ℚ → M),
      z ∈ populationSeedRootPiece P a κ lambda
          (D.haar.continuous.coefficient i).seedIndex →
      z ∉ (D.haar.continuous.coefficient i).roots →
      populationAtlasTheta P a κ lambda
          (D.haar.continuous.coefficient i).seedIndex z ^ (-2 / q) *
        G (D.haar.continuous.coefficient i).seedIndex z = 0)
    (hmble : ∀ i : Fin D.haar.continuous.count, AEStronglyMeasurable (fun z ↦
      populationAtlasTheta P a κ lambda
          (D.haar.continuous.coefficient i).seedIndex z ^ (-2 / q) *
        G (D.haar.continuous.coefficient i).seedIndex z) lambda)
    {C : ℝ}
    (hbd : ∀ i : Fin D.haar.continuous.count,
      ∀ᵐ z ∂lambda.restrict (populationSeedRootPiece P a κ lambda
        (D.haar.continuous.coefficient i).seedIndex),
        ‖populationAtlasTheta P a κ lambda
            (D.haar.continuous.coefficient i).seedIndex z ^ (-2 / q) *
          G (D.haar.continuous.coefficient i).seedIndex z‖ ≤ C)
    (hinjSeed : Function.Injective (fun i : Fin D.haar.continuous.count ↦
      (D.haar.continuous.coefficient i).seedIndex))
    (hzero : ∀ j : ℕ,
      j ∉ Finset.univ.image (fun i : Fin D.haar.continuous.count ↦
        (D.haar.continuous.coefficient i).seedIndex) →
      ∀ z, G j z = 0) :
    PopulationAtlasCovering (P := P) (a := a) (κ := κ) (lambda := lambda)
      (D := D) T q G :=
  populationAtlasCovering_of_tileStructure_vanishing (T := T) (q := q) G
    (fun i ↦ measurableSet_populationSeedRootPiece P a κ lambda
      hF hcomplete hu ha hinj _)
    (fun i ↦ integrableOn_weightedIntegrand_of_bounded
      (j := (D.haar.continuous.coefficient i).seedIndex) G
      (hmble i) (hbd i))
    hvan
    (populationAtlasTail_collapse_of_finiteSupport (q := q) G hinjSeed hzero)

/-- **The per-(f,t) canonical covering identity under explicit sufficient conditions
into checkable analytic hypotheses.**

The canonical form of populationAtlasCovering_of_tileStructure_residualsProved:
single hrev replacement hvanFam, per-(f,t) measurability and bounds,
injectivity of the retained seed indices, and per-(f,t) finite support of the
canonical family. -/
theorem canonicalRootedCovering_of_tileStructure_residualsProved
    (T : D.TaylorTiles ε) (α β : Measure OTSelector.UnitMark)
    (coef : FinalProbeSpace A B → ℕ → (ℚ → M) → ℝ → ℝ → ℝ)
    (probeFam : FinalProbeSpace A B → ℕ → (ℚ → M) →
      MarkedCloudPoint → MarkedCloudPoint → ℝ)
    (Mst : FinalProbeSpace A B → ℝ → ℕ → (ℚ → M) →
      StationaryForwardMatching α β)
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _instTileResidualsCanonMetric : MetricSpace M := F.metricSpace;
      LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))
    (hvanFam : ∀ (f : FinalProbeSpace A B) (t : ℝ)
      (i : Fin D.haar.continuous.count) (z : ℚ → M),
      z ∈ populationSeedRootPiece P a κ lambda
          (D.haar.continuous.coefficient i).seedIndex →
      z ∉ (D.haar.continuous.coefficient i).roots →
      populationAtlasTheta P a κ lambda
          (D.haar.continuous.coefficient i).seedIndex z ^ (-2 / q) *
        canonicalRootedIntegrand (A := A) (B := B) (P := P) (a := a)
          (κ := κ) (lambda := lambda) α β coef probeFam Mst q f t
          (D.haar.continuous.coefficient i).seedIndex z = 0)
    (hmbleFam : ∀ (f : FinalProbeSpace A B) (t : ℝ)
      (i : Fin D.haar.continuous.count), AEStronglyMeasurable (fun z ↦
      populationAtlasTheta P a κ lambda
          (D.haar.continuous.coefficient i).seedIndex z ^ (-2 / q) *
        canonicalRootedIntegrand (A := A) (B := B) (P := P) (a := a)
          (κ := κ) (lambda := lambda) α β coef probeFam Mst q f t
          (D.haar.continuous.coefficient i).seedIndex z) lambda)
    {C : ℝ}
    (hbdFam : ∀ (f : FinalProbeSpace A B) (t : ℝ)
      (i : Fin D.haar.continuous.count),
      ∀ᵐ z ∂lambda.restrict (populationSeedRootPiece P a κ lambda
        (D.haar.continuous.coefficient i).seedIndex),
        ‖populationAtlasTheta P a κ lambda
            (D.haar.continuous.coefficient i).seedIndex z ^ (-2 / q) *
          canonicalRootedIntegrand (A := A) (B := B) (P := P) (a := a)
            (κ := κ) (lambda := lambda) α β coef probeFam Mst q f t
            (D.haar.continuous.coefficient i).seedIndex z‖ ≤ C)
    (hinjSeed : Function.Injective (fun i : Fin D.haar.continuous.count ↦
      (D.haar.continuous.coefficient i).seedIndex))
    (hzeroFam : ∀ (f : FinalProbeSpace A B) (t : ℝ) (j : ℕ),
      j ∉ Finset.univ.image (fun i : Fin D.haar.continuous.count ↦
        (D.haar.continuous.coefficient i).seedIndex) →
      ∀ z, canonicalRootedIntegrand (A := A) (B := B) (P := P) (a := a)
        (κ := κ) (lambda := lambda) α β coef probeFam Mst q f t j z = 0) :
    CanonicalRootedCovering (A := A) (B := B) T q α β coef probeFam Mst :=
  fun f t ↦
    populationAtlasCovering_of_tileStructure_residualsProved (T := T)
      (G := canonicalRootedIntegrand (A := A) (B := B) (P := P) (a := a)
        (κ := κ) (lambda := lambda) α β coef probeFam Mst q f t)
      hF hcomplete hu ha hinj (hvanFam f t) (hmbleFam f t) (hbdFam f t)
      hinjSeed (hzeroFam f t)

end OTSelector.Reconstruction
