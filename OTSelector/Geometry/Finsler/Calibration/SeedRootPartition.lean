import OTSelector.Geometry.Finsler.Basic
import OTSelector.Geometry.Finsler.CalibratedLevelSeedPatch
import OTSelector.Geometry.Finsler.CalibratedSeedWindow
import OTSelector.Geometry.Finsler.Calibration.RootCoefficient
import OTSelector.Geometry.Finsler.Calibration.SeedLabelReference
import OTSelector.Geometry.Finsler.Energy.Basic
import OTSelector.Geometry.Finsler.LengthMetric
import OTSelector.Geometry.Finsler.PotentialGlobalFamily
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Reconstruction.FinslerSeedRootPartition.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Reconstruction.FinslerSeedRootPartition`; the selected original proof blocks follow. -/
section

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

/-- Actual seed roots with finite nonzero original reference density. -/
def populationSeedReferenceRoots (S : F.CalibratedLevelSeedPatch u) (a : M → Z)
    (κ : Measure S.covector.ker) (lambda : Measure Z) : Set Z :=
  {z | z ∈ populationSeedRootDomain S a ∧
    (populationSeedLabelReference S a κ).rnDeriv lambda z ≠ 0 ∧
    (populationSeedLabelReference S a κ).rnDeriv lambda z < (∞ : ℝ≥0∞)}

/-- The first actual seed with a finite nonzero reference factor owns this root. -/
def populationSeedRootPiece (P : ℕ → F.CalibratedSeedWindow u) (a : M → Z)
    (κ : ∀ j, Measure (P j).seed.covector.ker) (lambda : Measure Z) (j : ℕ) : Set Z :=
  disjointed (fun i ↦ populationSeedReferenceRoots (P i).seed a (κ i) lambda) j

variable (P : ℕ → F.CalibratedSeedWindow u) (a : M → Z)
  (κ : ∀ j, Measure (P j).seed.covector.ker) (lambda : Measure Z)

omit [FiniteDimensional ℝ E] [BorelSpace E] in
/-- Each disjoint piece retains the actual seed image and both reference-factor bounds. -/
theorem populationSeedRootPiece_subset (j : ℕ) :
    populationSeedRootPiece P a κ lambda j ⊆
      populationSeedReferenceRoots (P j).seed a (κ j) lambda :=
  disjointed_subset _ j





/-- The original label on one selected piece, with no arbitrary default label. -/
def populationSeedPieceLabel (j : ℕ) :
    populationSeedRootPiece P a κ lambda j → (P j).seed.labels :=
  fun z ↦ populationSeedRootLabel (P j).seed a
    ⟨z.val, (populationSeedRootPiece_subset P a κ lambda j z.property).1⟩

omit [FiniteDimensional ℝ E] [BorelSpace E] in
/-- This inverse reads exactly the given population root. -/
theorem populationSeedPieceLabel_root (j : ℕ)
    (z : populationSeedRootPiece P a κ lambda j) :
    a ((P j).seed.curve (populationSeedPieceLabel P a κ lambda j z) 0) = z.val :=
  apply_rangeSplitting (fun w : (P j).seed.labels ↦ a ((P j).seed.curve w 0)) _

variable [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  [MeasurableSpace.CountablySeparated Z]
  (hF : F.IsSmoothStronglyConvex)
  (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
  (hu : let _instRootPieceMetric : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
  (ha : Measurable a)
  (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))

include hF hcomplete hu ha hinj

/-- Each eligible actual seed image is measurable. -/
theorem measurableSet_populationSeedReferenceRoots (j : ℕ) :
    MeasurableSet (populationSeedReferenceRoots (P j).seed a (κ j) lambda) := by
  have hRN := (populationSeedLabelReference (P j).seed a (κ j)).measurable_rnDeriv lambda
  exact (measurableSet_populationSeedRootDomain (P j).seed hF hcomplete hu ha hinj).inter
    ((measurableSet_eq_fun hRN measurable_const).compl.inter
      (measurableSet_lt hRN measurable_const))

/-- The disjoint seed pieces are measurable in the original population root space. -/
theorem measurableSet_populationSeedRootPiece (j : ℕ) :
    MeasurableSet (populationSeedRootPiece P a κ lambda j) :=
  MeasurableSet.disjointed
    (measurableSet_populationSeedReferenceRoots P a κ lambda hF hcomplete hu ha hinj) j







end OTSelector.Reconstruction

end
end
