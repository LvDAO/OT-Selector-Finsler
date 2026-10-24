import OTSelector.Geometry.Finsler.Calibration.SeedRootPartition
import OTSelector.Geometry.Finsler.Calibration.RootCoefficient
import OTSelector.Reconstruction.FinslerPopulationSeedSelection

/-!
# Geometry.Finsler.Calibration.SeedRootPartition

* **Conditions:** An existing seed label reference, common label measure and actual seed image; inherited Borel hypotheses supply measurability.
* **Objects:** Finite-nonzero reference-density root sets, first-occurrence disjoint pieces and a label inverse reading the same original root.
* **Proof detail:** Intersect the actual image with RN factor bounds, apply countable disjointing and restrict the original image inverse to each selected piece.

Mathematical sources:
- [D. H. Fremlin, Measure Theory, Volume 2](https://www1.essex.ac.uk/maths/people/fremlin/chap23.pdf): Sections 232E–232I, Radon–Nikodym and Lebesgue decomposition; Section 235K, change of measure.
- [D. H. Fremlin, Measure Theory, Volume 4, Appendix](https://www1.essex.ac.uk/maths/people/fremlin/chap4a.pdf#page=32): Sections 4A3B(a)–(c), p. 32; 4A3C(a)–(f), pp. 32–33.
- [D. H. Fremlin, Measure Theory, Volume 4](https://www1.essex.ac.uk/maths/people/fremlin/chap42.pdf#page=22): Theorem 423I(a)–(b), pp. 22–23; Proposition 424G, p. 31.

Source relation (adapter): Only the exact seven selected commands are covered. Full-law coverage, pairwise-disjointness theorems and conditional recovery from the source file are not implicitly claimed.
-/

/-!
# Measurable original seed pieces of the population root law

The first seed with a finite nonzero original reference density determines a
measurable disjoint partition, covering almost every actual population root.
Its inverse reads the original label and retains every original Haar-a.e. fact.
-/

open Set Function MeasureTheory Manifold OTSelector.Geometry
open scoped Topology ContDiff ENNReal

noncomputable section
namespace OTSelector.Reconstruction

set_option backward.isDefEq.respectTransparency false

variable {E M Z : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [MeasurableSpace Z] {F : ContinuousFinslerNorm E M} {u : M → ℝ}





variable (P : ℕ → F.CalibratedSeedWindow u) (a : M → Z)
  (κ : ∀ j, Measure (P j).seed.covector.ker) (lambda : Measure Z)



omit [FiniteDimensional ℝ E] [BorelSpace E] in
/-- Distinct selected seed pieces are disjoint. -/
theorem pairwiseDisjoint_populationSeedRootPiece :
    Pairwise (Disjoint on populationSeedRootPiece P a κ lambda) :=
  disjoint_disjointed _

omit [FiniteDimensional ℝ E] [BorelSpace E] in
/-- Membership of the same root in two selected pieces forces their indices to agree. -/
theorem populationSeedRootPiece_index_eq_of_mem {z : Z} {i j : ℕ}
    (hi : z ∈ populationSeedRootPiece P a κ lambda i)
    (hj : z ∈ populationSeedRootPiece P a κ lambda j) : i = j :=
  (pairwiseDisjoint_populationSeedRootPiece P a κ lambda).eq
    (Set.not_disjoint_iff.mpr ⟨z, hi, hj⟩)





variable [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  [MeasurableSpace.CountablySeparated Z]
  (hF : F.IsSmoothStronglyConvex)
  (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
  (hu : let _instRootPieceMetric : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
  (ha : Measurable a)
  (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))

include hF hcomplete hu ha hinj





/-- Reading the retained original label on a selected piece is measurable. -/
theorem measurable_populationSeedPieceLabel (j : ℕ) :
    Measurable (populationSeedPieceLabel P a κ lambda j) :=
  (measurable_populationSeedRootLabel (P j).seed hF hcomplete hu ha hinj).comp
    measurable_subtype_coe.subtype_mk

/-- Normalization of the actual conditional law gives full-measure coverage by the pieces. -/
theorem PopulationConditionalWindowLaw.ae_mem_populationSeedRootPieces
    {η : Measure M} [IsFiniteMeasure η] {ρ : M → ℝ} {v : ℕ → E → ℝ}
    (hlaw : PopulationConditionalWindowLaw P a κ lambda η ρ v)
    (horder : let _instRootPieceOrder : MetricSpace M := F.metricSpace
      ∀ x ∈ F.potentialRegularDomain u, ∀ y ∈ F.potentialRegularDomain u,
        (a x = a y ∧ u x ≤ u y) ↔ u y - u x = dist x y)
    (hκ : ∀ j, SigmaFinite (κ j)) :
    ∀ᵐ z ∂lambda, z ∈ ⋃ j, populationSeedRootPiece P a κ lambda j := by
  filter_upwards [hlaw.ae_exists_seed_reference_ne_zero hF hcomplete hu ha hinj horder hκ]
    with z hz
  obtain ⟨j, w, hw, heq, hn, ht⟩ := hz
  change z ∈ ⋃ j, disjointed
    (fun i ↦ populationSeedReferenceRoots (P i).seed a (κ i) lambda) j
  rw [iUnion_disjointed]
  exact mem_iUnion.mpr ⟨j, ⟨⟨⟨w, hw⟩, heq⟩, hn, ht⟩⟩

/-- All original almost-everywhere seed facts hold at the actual measurable label
on every selected piece, simultaneously for the countable family of seeds. -/
theorem ae_populationSeedPieceLabel_property [SigmaFinite lambda]
    (hκ : ∀ j, SigmaFinite (κ j)) (Good : ∀ j, (P j).seed.covector.ker → Prop)
    (hgood : ∀ j, ∀ᵐ w ∂(κ j).restrict (P j).seed.labels, Good j w) :
    ∀ᵐ z ∂lambda, ∀ j, ∀ hz : z ∈ populationSeedRootPiece P a κ lambda j,
      Good j (populationSeedPieceLabel P a κ lambda j ⟨z, hz⟩) := by
  have hGood (j : ℕ) := by
    let _instRootPieceReference : SigmaFinite (κ j) := hκ j
    exact ae_populationSeedLabel_property (P j).seed hF hcomplete hu ha hinj (κ j)
      lambda (hgood j)
  filter_upwards [ae_all_iff.mpr hGood] with z hz
  intro j hj
  exact hz j (populationSeedRootPiece_subset P a κ lambda j hj).2.1
    _ (populationSeedPieceLabel P a κ lambda j ⟨z, hj⟩).property
    (populationSeedPieceLabel_root P a κ lambda j ⟨z, hj⟩)

end OTSelector.Reconstruction
