import OTSelector.Reconstruction.FinslerOriginalCanonicalPalmFromSingleFamily
import OTSelector.Reconstruction.FinslerOriginalReadoutDecompositionSimplification
import OTSelector.Reconstruction.FinslerOriginalTileRefinementCounting
import OTSelector.Reconstruction.FinslerOriginalCanonicalGrootElimination

/-!
# The population covering identity from the tile structure

FinslerOriginalPalmLLNPerProbeTilt and FinslerOriginalCanonicalPalmFromSingleFamily
reduced the canonical lane to a population covering family
hcover : forall f t, PopulationAtlasCovering ... (canonical family f t).
This module discharges that family from the tile structure itself.

## Is the covering identity definitional?

The covering identity is
  campbellAveragedFrozenCost P a kappa lambda G q = sum c, tilePopValue G c,
i.e. the atlas Campbell series over the disjointed seed pieces equals the finite
sum of the retained tile cell integrals.  It is NOT a definitional consequence of
the two definitions:

* the left side is a tsum over ALL seed pieces (disjointed reference roots),
  weighted by the seed's theta and the root family G;
* the right side is a finite sum over the retained coefficients' partition cells,
  weighted by the coefficient's theta and the SAME root family G, but evaluated
  only on retained cells.

The two sides are built from different index families (all seeds vs retained
coefficients times cells), so connecting them needs measure-theoretic input.
What this module proves is that the only remaining inputs are:

1. hrev: for each retained coefficient, the seed piece is almost everywhere
   contained in the coefficient's root set (forall i, forall^m z in piece i,
   z in roots i).  Together with the structural fact roots i subset piece i
   (OriginalPopulationCoefficientCore.roots_subset_piece) this identifies the
   piece with the root set a.e., and the root set with the union of the
   partition cells (FiniteRootNeighborhoodPartition.union_eq).
2. hInt: IntegrableOn of the weighted root integrand over each retained seed
   piece (needed to sum the cell integrals by additivity).
3. htail: the vanishing of the atlas tail outside the finite retained
   coefficient family (the finite collapse of the tsum), as in the repo's
   hdecomp producer.

In particular the per-piece integral refinement T.PieceCellRefinement, which
the repo kept as the named measure-theoretic input, is PROVED here from the tile
structure (partition union_eq, disjointness, cell measurability, cell subset
roots subset piece, and a.e. piece subset roots) plus integrability; it is no
longer a hypothesis.

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

namespace PopulationLocalPressureCore.TaylorTiles

open OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

/-- The per-piece cell-refinement integral identity from the tile structure.

The repo kept T.PieceCellRefinement as a named measure-theoretic input.  It is
proved here: the retained partition cells are measurable and pairwise disjoint
(FiniteRootNeighborhoodPartition), their union is the coefficient's root set
(union_eq), the root set is contained in the coefficient's seed piece
(roots_subset_piece), and on the piece the root set holds a.e. (hrev); hence
the piece and the union of cells are a.e. equal, their restricted measures
coincide, and additivity of the integral over a finite disjoint union of
measurable sets (integral_iUnion_fintype) gives the identity.  Integrability
of the weighted root integrand over the piece is hInt; over each cell it
follows by monotonicity. -/
theorem pieceCellRefinement_of_tileStructure
    (T : D.TaylorTiles ε) (G : ℕ → (ℚ → M) → ℝ)
    (hrev : ∀ i : Fin D.haar.continuous.count,
      ∀ᵐ z ∂lambda.restrict (populationSeedRootPiece P a κ lambda
        (D.haar.continuous.coefficient i).seedIndex),
        z ∈ (D.haar.continuous.coefficient i).roots)
    (hInt : ∀ i : Fin D.haar.continuous.count,
      IntegrableOn (fun z ↦
        populationAtlasTheta P a κ lambda
            (D.haar.continuous.coefficient i).seedIndex z ^ (-2 / q) *
          G (D.haar.continuous.coefficient i).seedIndex z)
        (populationSeedRootPiece P a κ lambda
          (D.haar.continuous.coefficient i).seedIndex) lambda) :
    T.PieceCellRefinement (q := q) G := by
  intro i
  have hU_sub : (⋃ k : Fin (T.partition i).count, (T.partition i).cell k) ⊆
      populationSeedRootPiece P a κ lambda
        (D.haar.continuous.coefficient i).seedIndex := by
    rw [(T.partition i).union_eq]
    exact (D.haar.continuous.coefficient i).roots_subset_piece
  have hmeasU : MeasurableSet
      (⋃ k : Fin (T.partition i).count, (T.partition i).cell k) :=
    MeasurableSet.iUnion (f := fun k : Fin (T.partition i).count ↦
      (T.partition i).cell k) (fun k ↦ (T.partition i).measurable_cell k)
  have hrev_i : ∀ᵐ z ∂lambda.restrict
      (populationSeedRootPiece P a κ lambda
        (D.haar.continuous.coefficient i).seedIndex),
      z ∈ (⋃ k : Fin (T.partition i).count, (T.partition i).cell k) := by
    simpa only [(T.partition i).union_eq] using hrev i
  have hA : lambda.restrict
      (populationSeedRootPiece P a κ lambda
        (D.haar.continuous.coefficient i).seedIndex)
      ((⋃ k : Fin (T.partition i).count, (T.partition i).cell k))ᶜ = 0 := by
    have h0 : (lambda.restrict (populationSeedRootPiece P a κ lambda
        (D.haar.continuous.coefficient i).seedIndex))
        {z | ¬ z ∈ (⋃ k : Fin (T.partition i).count, (T.partition i).cell k)} = 0 :=
      (MeasureTheory.ae_iff (μ := lambda.restrict (populationSeedRootPiece P a κ lambda
        (D.haar.continuous.coefficient i).seedIndex))).mp hrev_i
    rwa [show ((⋃ k : Fin (T.partition i).count, (T.partition i).cell k))ᶜ =
        {z | ¬ z ∈ (⋃ k : Fin (T.partition i).count, (T.partition i).cell k)} from rfl]
  have hEq : populationSeedRootPiece P a κ lambda
        (D.haar.continuous.coefficient i).seedIndex \ (⋃ k : Fin (T.partition i).count, (T.partition i).cell k) =
      ((⋃ k : Fin (T.partition i).count, (T.partition i).cell k))ᶜ ∩
        populationSeedRootPiece P a κ lambda
          (D.haar.continuous.coefficient i).seedIndex := by
    ext z
    simp [and_comm]
  have hnull1 : lambda (populationSeedRootPiece P a κ lambda
        (D.haar.continuous.coefficient i).seedIndex \ (⋃ k : Fin (T.partition i).count, (T.partition i).cell k)) = 0 := by
    rw [hEq, ← Measure.restrict_apply hmeasU.compl]
    exact hA
  have hnull2 : lambda ((⋃ k : Fin (T.partition i).count,
        (T.partition i).cell k) \ populationSeedRootPiece P a κ lambda
        (D.haar.continuous.coefficient i).seedIndex) = 0 := by
    rw [Set.sdiff_eq_empty.mpr hU_sub, measure_empty]
  have hae : populationSeedRootPiece P a κ lambda
        (D.haar.continuous.coefficient i).seedIndex =ᵐ[lambda]
      (⋃ k : Fin (T.partition i).count, (T.partition i).cell k) :=
    MeasureTheory.ae_eq_set.mpr ⟨hnull1, hnull2⟩
  rw [Measure.restrict_congr_set hae]
  exact integral_iUnion_fintype
    (fun k : Fin (T.partition i).count ↦ (T.partition i).measurable_cell k)
    (T.partition i).disjoint
    (fun k ↦ (hInt i).mono_set ((Set.subset_iUnion
      (fun k : Fin (T.partition i).count ↦ (T.partition i).cell k) k).trans hU_sub))

/-- The population covering identity from the tile structure.

Combines the proved per-piece cell refinement with the vanishing atlas tail
through the repo's campbellAveragedFrozenCost_eq_tileSum_of_cell_refinement.
The identity itself is not assumed: the only inputs are the a.e. piece/root-set
revision hrev, the integrability hInt on each retained piece, and the finite
atlas-tail collapse htail. -/
theorem populationAtlasCovering_of_tileStructure
    (T : D.TaylorTiles ε) (G : ℕ → (ℚ → M) → ℝ)
    (hrev : ∀ i : Fin D.haar.continuous.count,
      ∀ᵐ z ∂lambda.restrict (populationSeedRootPiece P a κ lambda
        (D.haar.continuous.coefficient i).seedIndex),
        z ∈ (D.haar.continuous.coefficient i).roots)
    (hInt : ∀ i : Fin D.haar.continuous.count,
      IntegrableOn (fun z ↦
        populationAtlasTheta P a κ lambda
            (D.haar.continuous.coefficient i).seedIndex z ^ (-2 / q) *
          G (D.haar.continuous.coefficient i).seedIndex z)
        (populationSeedRootPiece P a κ lambda
          (D.haar.continuous.coefficient i).seedIndex) lambda)
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
    (pieceCellRefinement_of_tileStructure (T := T) (q := q) G hrev hInt) htail

end PopulationLocalPressureCore.TaylorTiles

/-! ## 2. The canonical covering from the tile structure -/

/-- The canonical rooted covering from the tile structure.

The per-(f,t) population covering family of the canonical rooted integrand, with
the covering identity no longer assumed: the (f,t)-free a.e. revision hrev
(single hypothesis, since the seed pieces and root sets do not depend on the
probe or tilt), the per-(f,t) integrability hIntFam of the weighted canonical
integrand on each retained piece, and the per-(f,t) vanishing atlas tail
htailFam produce CanonicalRootedCovering. -/
theorem canonicalRootedCovering_of_tileStructure
    (T : D.TaylorTiles ε) {A B : Set M} (q : ℝ)
    (α β : Measure OTSelector.UnitMark)
    (coef : FinalProbeSpace A B → ℕ → (ℚ → M) → ℝ → ℝ → ℝ)
    (probeFam : FinalProbeSpace A B → ℕ → (ℚ → M) →
      MarkedCloudPoint → MarkedCloudPoint → ℝ)
    (Mst : FinalProbeSpace A B → ℝ → ℕ → (ℚ → M) →
      StationaryForwardMatching α β)
    (hrev : ∀ i : Fin D.haar.continuous.count,
      ∀ᵐ z ∂lambda.restrict (populationSeedRootPiece P a κ lambda
        (D.haar.continuous.coefficient i).seedIndex),
        z ∈ (D.haar.continuous.coefficient i).roots)
    (hIntFam : ∀ (f : FinalProbeSpace A B) (t : ℝ),
      ∀ i : Fin D.haar.continuous.count,
      IntegrableOn (fun z ↦
        populationAtlasTheta P a κ lambda
            (D.haar.continuous.coefficient i).seedIndex z ^ (-2 / q) *
          canonicalRootedIntegrand (A := A) (B := B) (P := P) (a := a)
            (κ := κ) (lambda := lambda) α β coef probeFam Mst q f t
            (D.haar.continuous.coefficient i).seedIndex z)
        (populationSeedRootPiece P a κ lambda
          (D.haar.continuous.coefficient i).seedIndex) lambda)
    (htailFam : ∀ (f : FinalProbeSpace A B) (t : ℝ),
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
  fun f t ↦
    PopulationLocalPressureCore.TaylorTiles.populationAtlasCovering_of_tileStructure
      (T := T) (q := q)
      (canonicalRootedIntegrand (A := A) (B := B) (P := P) (a := a) (κ := κ)
        (lambda := lambda) α β coef probeFam Mst q f t)
      hrev (hIntFam f t) (htailFam f t)

/-! ## 3. The lane hId with the covering family removed -/

/-- The lane hId from the tile structure.

Same as frozenCampbellMeanIdentification_sceneCloud_of_singleFamilyInputs of
FinslerOriginalCanonicalPalmFromSingleFamily, but the population covering family
hcover is removed from the binder list: it is produced from the tile structure
by canonicalRootedCovering_of_tileStructure (a.e. revision hrev, integrability
hIntFam, atlas-tail collapse htailFam). -/
theorem frozenCampbellMeanIdentification_sceneCloud_of_tileStructure
    (T : D.TaylorTiles ε) {A B : Set M}
    (pcloud qcloud : ∀ n, Fin (n + 1) → M)
    (base : ∀ n, Fin (n + 1) → T.Index → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (q : ℝ) (α β : Measure OTSelector.UnitMark)
    (coef : FinalProbeSpace A B → ℕ → (ℚ → M) → ℝ → ℝ → ℝ)
    (probeFam : FinalProbeSpace A B → ℕ → (ℚ → M) →
      MarkedCloudPoint → MarkedCloudPoint → ℝ)
    (Mst : FinalProbeSpace A B → ℝ → ℕ → (ℚ → M) →
      StationaryForwardMatching α β)
    (hrev : ∀ i : Fin D.haar.continuous.count,
      ∀ᵐ z ∂lambda.restrict (populationSeedRootPiece P a κ lambda
        (D.haar.continuous.coefficient i).seedIndex),
        z ∈ (D.haar.continuous.coefficient i).roots)
    (hIntFam : ∀ (f : FinalProbeSpace A B) (t : ℝ),
      ∀ i : Fin D.haar.continuous.count,
      IntegrableOn (fun z ↦
        populationAtlasTheta P a κ lambda
            (D.haar.continuous.coefficient i).seedIndex z ^ (-2 / q) *
          canonicalRootedIntegrand (A := A) (B := B) (P := P) (a := a)
            (κ := κ) (lambda := lambda) α β coef probeFam Mst q f t
            (D.haar.continuous.coefficient i).seedIndex z)
        (populationSeedRootPiece P a κ lambda
          (D.haar.continuous.coefficient i).seedIndex) lambda)
    (htailFam : ∀ (f : FinalProbeSpace A B) (t : ℝ),
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
                (D.haar.continuous.coefficient i).seedIndex z ∂lambda)
    (h : SinglePalmFamilyReading (A := A) (B := B) T pcloud qcloud q α β coef
      probeFam Mst)
    {Bp : ℝ} (hBp : 0 ≤ Bp)
    (hbase : ∀ (n : ℕ) (s : Fin (n + 1)) (c' : T.Index) (i j : Fin (n + 1)),
      |base n s c' i j| ≤ Bp)
    (hintC : ∀ (f : FinalProbeSpace A B) (t : ℝ) (n : ℕ) (c : T.Index),
      Integrable (T.tileLinearCostIntegrand (ε := ε) f t (sceneCloudX pcloud)
        (sceneCloudY qcloud) tileScale n c) (sceneCloudSample n))
    (hintP : ∀ (f : FinalProbeSpace A B) (t : ℝ) (n : ℕ) (c : T.Index),
      Integrable (T.tileLinearProbeIntegrand f t (sceneCloudX pcloud)
        (sceneCloudY qcloud)
        (fun f t n s c' ↦ normalizedProbe (K := A ∪ B) base t n s c') n c)
        (sceneCloudSample n))
    (hintClip : ∀ (f : FinalProbeSpace A B) (t : ℝ) (n : ℕ) (c : T.Index),
      Integrable (T.tileClippingIntegrand (ε := ε) f t (sceneCloudX pcloud)
        (sceneCloudY qcloud) tileScale
        (fun f t n s c' ↦ normalizedProbe (K := A ∪ B) base t n s c') n c)
        (sceneCloudSample n))
    (hclip : ∀ (f : FinalProbeSpace A B) (t : ℝ) (c : T.Index),
      Tendsto (fun n ↦ T.tileFixedPairClippingCorrection f t sceneCloudSample
        (sceneCloudX pcloud) (sceneCloudY qcloud) tileScale
        (fun f t n s c' ↦ normalizedProbe (K := A ∪ B) base t n s c') n c)
        atTop (𝓝 0))
    (hintEntry : ∀ (f : FinalProbeSpace A B) (t : ℝ) (n : ℕ) (c : T.Index)
      (i j : Fin (n + 1)),
      Integrable (fun s ↦ T.tileCostMatrix f t (sceneCloudX pcloud)
        (sceneCloudY qcloud) tileScale
        (fun f t n s c' ↦ normalizedProbe (K := A ∪ B) base t n s c') n c s i j)
        (sceneCloudSample n))
    (hExch : ∀ (f : FinalProbeSpace A B) (t : ℝ) (n : ℕ) (c : T.Index),
      MaskedEntryExchangeability (sceneCloudSample n)
        (T.tileCostMatrix f t (sceneCloudX pcloud) (sceneCloudY qcloud) tileScale
          (fun f t n s c' ↦ normalizedProbe (K := A ∪ B) base t n s c') n c))
    (hintCost : ∀ (f : FinalProbeSpace A B) (t : ℝ) (n : ℕ) (c : T.Index),
      Integrable (fun s ↦ ∑ i, ∑ j,
        T.tileCostMatrix f t (sceneCloudX pcloud) (sceneCloudY qcloud) tileScale
          (fun f t n s c' ↦ normalizedProbe (K := A ∪ B) base t n s c') n c s i j)
        (sceneCloudSample n))
    (hintRes : ∀ (f : FinalProbeSpace A B) (t : ℝ) (n : ℕ) (c : T.Index),
      Integrable (fun s ↦ ∑ i, ∑ j,
        (uniformTilePlan (fun n ↦ Fin (n + 1)) n s i j -
          1 / ((n + 1 : ℕ) : ℝ)) *
          T.tileCostMatrix f t (sceneCloudX pcloud) (sceneCloudY qcloud) tileScale
            (fun f t n s c' ↦ normalizedProbe (K := A ∪ B) base t n s c') n c s i j)
        (sceneCloudSample n))
    (hresv : T.TilePlanResidualVanishing (K := A ∪ B) sceneCloudSample
      (uniformTilePlan (fun n ↦ Fin (n + 1))) (sceneCloudX pcloud)
      (sceneCloudY qcloud) tileScale
      (fun f t n s c' ↦ normalizedProbe (K := A ∪ B) base t n s c'))
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _instTileStructureMetric : MetricSpace M := F.metricSpace;
      LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val))) :
    RootedTileCampbellMeanIdentification (K := A ∪ B) P a κ lambda
      (frozenRootedCostReadout (F := F) (u := u) (Seed := P) (a := a)
        (κ := κ) (lambda := lambda) (Z := ℚ → M) (A := A) (B := B)
        α β coef probeFam Mst q) q sceneCloudSample
      (hprobFrozenCostFamily (K := A ∪ B) (T := T) (sceneCloudX pcloud)
        (sceneCloudY qcloud) base (uniformTilePlan (fun n ↦ Fin (n + 1)))
        tileScale) T.Index :=
  frozenCampbellMeanIdentification_sceneCloud_of_singleFamilyInputs
    (A := A) (B := B) T pcloud qcloud base q α β coef probeFam Mst
    (canonicalRootedCovering_of_tileStructure (A := A) (B := B) T q α β coef
      probeFam Mst hrev hIntFam htailFam)
    h hBp hbase hintC hintP hintClip hclip hintEntry hExch hintCost hintRes hresv
    hF hcomplete hu ha hinj

end OTSelector.Reconstruction
