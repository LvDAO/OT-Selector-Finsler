import OTSelector.Geometry.Finsler.Calibration.PopulationConditionalLaw
import OTSelector.Reconstruction.FinslerSeedRootPartition
import OTSelector.Geometry.Finsler.CalibratedSeedWindowRestriction

/-!
# Refinement cover and partition of the global refined atlas

This file proves the refinement-cover/partition lemma for the global refined atlas
of `FinslerOriginalGlobalRefinedAtlas`. The original countable atlas `P` is
refined window-by-window; the refined windows form one global enumeration `P'`
with a parent map `parent : ℕ → ℕ` (the refined window `k` sits over the parent
window `parent k`).

The file provides:

* the globally disjointified refined window pieces
  `refinedWindowPiece P' k = disjointed (image of refined window) k`, with
  pairwise disjointness, measurability and union preservation;
* the **piece-level partition**: under piece-level containment of every refined
  piece in its parent piece and a cover of each parent piece by its refined pieces
  up to a correction that is null for the joint label-clock law
  `η.map (fun x ↦ (a x, u x))` (equivalently a measurable
  `λ ⊗ volume`-null set by the paper's `joint_absolutelyContinuous`), each
  parent piece differs from its refined-piece union by an `η`-null set;
* the **restriction and sum decomposition**
  `(η.restrict parentPiece).map (a,u) = Measure.sum (refined pieces' laws)`, the
  form consumed by the cube-coordinate transfer;
* the **cover equality** `⋃ refined pieces = calibratedInterior` from the parent
  atlas cover and the refined cover of every parent piece;
* the **label-side cover and belongs-to-exactly-one-window** statement on the
  population reference root space.

The residual producer input is the same one documented in the global refined
atlas: piece-level containment and the coverage of each parent piece by its
certified ball-core refined windows is producer-cover geometry; the set algebra,
disjointification and the joint-null corrections are proved here.
-/
open Set Function MeasureTheory ProbabilityTheory Manifold OTSelector.Geometry
open MeasureTheory.Measure
open Metric
open scoped Topology ContDiff ENNReal NNReal BigOperators

noncomputable section
namespace OTSelector.Reconstruction

set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

variable {E M Z : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  [MeasurableSpace Z] [MeasurableSpace.CountablySeparated Z]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}

/-! ## The globally disjointified refined pieces -/

/-- The measured image of one refined window. -/
def refinedWindowImage (P' : ℕ → F.CalibratedSeedWindow u) (k : ℕ) : Set M :=
  (P' k).toManifold '' (P' k).domain

/-- The globally disjointified pieces of the refined window family: the refined
piece `k` is the part of the `k`-th refined window image not covered by any
earlier refined window. -/
def refinedWindowPiece (P' : ℕ → F.CalibratedSeedWindow u) (k : ℕ) : Set M :=
  disjointed (refinedWindowImage P') k

/-- Each refined window image is Borel. -/
theorem measurableSet_refinedWindowImage
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _instRefinementCoverMetric : MetricSpace M := F.metricSpace
      LipschitzWith 1 u)
    (P' : ℕ → F.CalibratedSeedWindow u) (k : ℕ) :
    MeasurableSet (refinedWindowImage P' k) :=
  (P' k).measurableSet_image hF hcomplete hu

/-- Each globally disjointified refined piece is Borel. -/
theorem measurableSet_refinedWindowPiece
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _instRefinementCoverMetric : MetricSpace M := F.metricSpace
      LipschitzWith 1 u)
    (P' : ℕ → F.CalibratedSeedWindow u) (k : ℕ) :
    MeasurableSet (refinedWindowPiece P' k) :=
  MeasurableSet.disjointed
    (measurableSet_refinedWindowImage hF hcomplete hu P') k

/-- Distinct globally disjointified refined pieces are disjoint. -/
theorem pairwiseDisjoint_refinedWindowPiece (P' : ℕ → F.CalibratedSeedWindow u) :
    Pairwise (Disjoint on refinedWindowPiece P') :=
  disjoint_disjointed _

/-- The union of the globally disjointified refined pieces is the union of the
refined window images. -/
theorem iUnion_refinedWindowPiece (P' : ℕ → F.CalibratedSeedWindow u) :
    ⋃ k, refinedWindowPiece P' k = ⋃ k, refinedWindowImage P' k :=
  iUnion_disjointed

/-- A globally disjointified refined piece is contained in its refined window image. -/
theorem refinedWindowPiece_subset_image (P' : ℕ → F.CalibratedSeedWindow u) (k : ℕ) :
    refinedWindowPiece P' k ⊆ refinedWindowImage P' k :=
  disjointed_subset _ _

/-! ## The piece-level partition -/

/-- **The refinement-cover partition at piece level.**  If every globally
disjointified refined piece is contained in the parent piece over its parent
index, and every parent piece is covered by its refined pieces up to a correction
that is null for the joint label-clock law `η.map (fun x ↦ (a x, u x))`, then
every parent piece differs from its refined-piece union by an `η`-null set. -/
theorem refinementCover_piece_partition
    (P P' : ℕ → F.CalibratedSeedWindow u) (parent : ℕ → ℕ) (a : M → Z)
    (eta : Measure M) (hpair : Measurable fun x => (a x, u x))
    (hcontain : ∀ k, refinedWindowPiece P' k ⊆ populationWindowPiece P (parent k))
    {N : Set (Z × ℝ)} (hN : MeasurableSet N)
    (hNnull : (eta.map (fun x => (a x, u x))) N = 0)
    (hcover : ∀ j, (fun x => (a x, u x)) ''
      (populationWindowPiece P j \ ⋃ k ∈ {k | parent k = j}, refinedWindowPiece P' k) ⊆ N) :
    ∀ j, eta (populationWindowPiece P j \
      ⋃ k ∈ {k | parent k = j}, refinedWindowPiece P' k) = 0 := by
  intro j
  have hpre : eta (((fun x => (a x, u x)) ⁻¹' N)) = 0 := by
    rw [← Measure.map_apply hpair hN]
    exact hNnull
  exact measure_mono_null (fun x hx => hcover j ⟨x, hx, rfl⟩) hpre

/-! ## Restriction and sum decomposition over the refined pieces -/

/-- The refined pieces sitting over one parent index. -/
def refinedPiecesOver (P' : ℕ → F.CalibratedSeedWindow u) (parent : ℕ → ℕ) (j : ℕ) :
    ℕ → Set M :=
  fun k => if parent k = j then refinedWindowPiece P' k else ∅

/-- The refined pieces over a parent index are pairwise disjoint. -/
theorem pairwiseDisjoint_refinedPiecesOver
    (P' : ℕ → F.CalibratedSeedWindow u) (parent : ℕ → ℕ) (j : ℕ) :
    Pairwise (Function.onFun Disjoint (refinedPiecesOver P' parent j)) := by
  intro k l hkl
  show Disjoint (if parent k = j then refinedWindowPiece P' k else ∅)
    (if parent l = j then refinedWindowPiece P' l else ∅)
  rcases eq_or_ne (parent k) j with hk | hk
  · rcases eq_or_ne (parent l) j with hl | hl
    · rw [ite_eq_left hk, ite_eq_left hl]
      exact pairwiseDisjoint_refinedWindowPiece P' hkl
    · rw [ite_eq_left hk, ite_eq_right hl]
      exact disjoint_empty _
  · rw [ite_eq_right hk]
    exact empty_disjoint _

/-- The union of the refined pieces over one parent index is the union of the
globally disjointified refined pieces over that index. -/
theorem iUnion_refinedPiecesOver
    (P' : ℕ → F.CalibratedSeedWindow u) (parent : ℕ → ℕ) (j : ℕ) :
    ⋃ k, refinedPiecesOver P' parent j k =
      ⋃ k ∈ {k | parent k = j}, refinedWindowPiece P' k := by
  ext x
  simp only [mem_iUnion, refinedPiecesOver]
  constructor
  · rintro ⟨k, hk⟩
    by_cases hkj : parent k = j
    · refine ⟨k, hkj, ?_⟩
      rwa [ite_eq_left hkj] at hk
    · rw [ite_eq_right hkj] at hk
      exact absurd hk (by simp)
  · rintro ⟨k, hkj, hxk⟩
    exact ⟨k, by
      rw [ite_eq_left (show parent k = j from hkj)]
      exact hxk⟩

/-! ## Restriction and sum decomposition over the refined pieces -/

/-- **The restriction decomposition over the refined pieces.**  Under the
refinement-cover hypotheses, the population law restricted to a parent piece is
the sum of its restrictions to the refined pieces sitting over that parent. -/
theorem refinementCover_restrict_eq_sum
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _instRefinementCoverMetric : MetricSpace M := F.metricSpace
      LipschitzWith 1 u)
    (P P' : ℕ → F.CalibratedSeedWindow u) (parent : ℕ → ℕ) (a : M → Z)
    (eta : Measure M) (hpair : Measurable fun x => (a x, u x))
    (hcontain : ∀ k, refinedWindowPiece P' k ⊆ populationWindowPiece P (parent k))
    {N : Set (Z × ℝ)} (hN : MeasurableSet N)
    (hNnull : (eta.map (fun x => (a x, u x))) N = 0)
    (hcover : ∀ j, (fun x => (a x, u x)) ''
      (populationWindowPiece P j \ ⋃ k ∈ {k | parent k = j}, refinedWindowPiece P' k) ⊆ N)
    (j : ℕ) :
    eta.restrict (populationWindowPiece P j) =
      Measure.sum (fun k => if parent k = j then
        eta.restrict (refinedWindowPiece P' k) else 0) := by
  set U : Set M := ⋃ k ∈ {k | parent k = j}, refinedWindowPiece P' k with hUdef
  have hUsub : U ⊆ populationWindowPiece P j := by
    intro x hx
    obtain ⟨k, hkj, hxk⟩ := mem_iUnion₂.mp hx
    have := hcontain k hxk
    rwa [show parent k = j from hkj] at this
  have hnull : eta (Set.diff (populationWindowPiece P j) U) = 0 :=
    refinementCover_piece_partition P P' parent a eta hpair hcontain hN hNnull hcover j
  have hrestrict : eta.restrict (populationWindowPiece P j) = eta.restrict U := by
    ext T hT
    rw [Measure.restrict_apply hT, Measure.restrict_apply hT]
    refine le_antisymm ?_ (measure_mono (inter_subset_inter_right _ hUsub))
    calc
      eta (T ∩ populationWindowPiece P j)
          ≤ eta ((T ∩ U) ∪ (Set.diff (populationWindowPiece P j) U)) := by
            refine measure_mono ?_
            rintro x ⟨hxT, hxp⟩
            by_cases hxU : x ∈ U
            · exact Or.inl ⟨hxT, hxU⟩
            · exact Or.inr ⟨hxp, hxU⟩
      _ ≤ eta (T ∩ U) + eta (Set.diff (populationWindowPiece P j) U) := measure_union_le _ _
      _ = eta (T ∩ U) := by rw [hnull, add_zero]
  rw [hrestrict, hUdef, ← iUnion_refinedPiecesOver P' parent j]
  rw [Measure.restrict_iUnion (pairwiseDisjoint_refinedPiecesOver P' parent j)]
  · congr 1
    funext k
    by_cases hk : parent k = j
    · simp only [refinedPiecesOver, hk, ite_true]
    · simp only [refinedPiecesOver, hk, ite_false, Measure.restrict_empty]
  · intro k
    by_cases hk : parent k = j
    · simpa only [refinedPiecesOver, hk, ite_true] using
        measurableSet_refinedWindowPiece hF hcomplete hu P' k
    · simp only [refinedPiecesOver, hk, ite_false]
      exact MeasurableSet.empty

/-- **The joint-law sum decomposition.**  Mapping the parent-piece population law
to the joint label-clock law gives the sum of the refined pieces' joint laws: the
form consumed by the cube-coordinate transfer. -/
theorem refinementCover_map_eq_sum
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _instRefinementCoverMetric : MetricSpace M := F.metricSpace
      LipschitzWith 1 u)
    (P P' : ℕ → F.CalibratedSeedWindow u) (parent : ℕ → ℕ) (a : M → Z)
    (eta : Measure M) (hpair : Measurable fun x => (a x, u x))
    (hcontain : ∀ k, refinedWindowPiece P' k ⊆ populationWindowPiece P (parent k))
    {N : Set (Z × ℝ)} (hN : MeasurableSet N)
    (hNnull : (eta.map (fun x => (a x, u x))) N = 0)
    (hcover : ∀ j, (fun x => (a x, u x)) ''
      (populationWindowPiece P j \ ⋃ k ∈ {k | parent k = j}, refinedWindowPiece P' k) ⊆ N)
    (j : ℕ) :
    (eta.restrict (populationWindowPiece P j)).map (fun x => (a x, u x)) =
      Measure.sum (fun k => if parent k = j then
        (eta.restrict (refinedWindowPiece P' k)).map (fun x => (a x, u x)) else 0) := by
  rw [refinementCover_restrict_eq_sum hF hcomplete hu P P' parent a eta hpair hcontain
    hN hNnull hcover j, Measure.map_sum hpair.aemeasurable]
  congr 1
  funext k
  by_cases hk : parent k = j
  · simp only [hk, ite_true]
  · simp only [hk, ite_false, Measure.map_zero]

/-! ## The cover equality of the refined atlas -/

/-- **Cover equality of the refined atlas.**  If every refined piece sits in its
parent piece and every parent piece is covered by its refined pieces, then the
union of the globally disjointified refined pieces is the original calibrated
interior, using the parent atlas cover equality. -/
theorem refined_iUnion_eq_calibratedInterior
    (P P' : ℕ → F.CalibratedSeedWindow u) (parent : ℕ → ℕ)
    (hcontain : ∀ k, refinedWindowPiece P' k ⊆ populationWindowPiece P (parent k))
    (hcoverU : ∀ j, populationWindowPiece P j ⊆
      ⋃ k ∈ {k | parent k = j}, refinedWindowPiece P' k)
    (hP : letI : MetricSpace M := F.metricSpace
      ⋃ j, (P j).toManifold '' (P j).domain = calibratedInterior u) :
    letI : MetricSpace M := F.metricSpace
    ⋃ k, refinedWindowPiece P' k = calibratedInterior u := by
  letI : MetricSpace M := F.metricSpace
  have hparent : ⋃ j, populationWindowPiece P j =
      ⋃ j, (P j).toManifold '' (P j).domain := by
    simpa only [populationWindowPiece] using
      iUnion_disjointed (f := fun j => (P j).toManifold '' (P j).domain)
  apply le_antisymm
  · intro x hx
    obtain ⟨k, hxk⟩ := mem_iUnion.mp hx
    have hxP : x ∈ ⋃ j, populationWindowPiece P j :=
      mem_iUnion.mpr ⟨parent k, hcontain k hxk⟩
    rwa [hparent, hP] at hxP
  · rw [← hP, ← hparent]
    intro x hx
    obtain ⟨j, hxj⟩ := mem_iUnion.mp hx
    obtain ⟨k, -, hxk⟩ := mem_iUnion₂.mp (hcoverU j hxj)
    exact mem_iUnion.mpr ⟨k, hxk⟩

/-! ## The label-side cover and belongs-to-exactly-one-window form -/

/-- **Label-side refinement cover and exactly-one-window form.**  If every parent
root piece is covered by the refined root pieces over its parent index, then every
retained parent root is covered and belongs to exactly one refined piece over its
parent index (the globally disjointified refined pieces are pairwise disjoint).
This is the label-side form consumed by the cube-coordinate transfer. -/
theorem refinementCover_label_partition
    (P P' : ℕ → F.CalibratedSeedWindow u) (parent : ℕ → ℕ) (a : M → Z)
    (κ : ∀ j, Measure (P j).seed.covector.ker)
    (κ' : ∀ k, Measure (P' k).seed.covector.ker) (lambda : Measure Z)
    (hcover : ∀ j, populationSeedRootPiece P a κ lambda j ⊆
      ⋃ k ∈ {k | parent k = j}, populationSeedRootPiece P' a κ' lambda k) :
    (∀ j, populationSeedRootPiece P a κ lambda j ⊆
      ⋃ k ∈ {k | parent k = j}, populationSeedRootPiece P' a κ' lambda k) ∧
    (∀ j z, z ∈ populationSeedRootPiece P a κ lambda j →
      ∃! k, parent k = j ∧ z ∈ populationSeedRootPiece P' a κ' lambda k) := by
  refine ⟨hcover, ?_⟩
  intro j z hz
  obtain ⟨k, hkj, hzk⟩ := mem_iUnion₂.mp (hcover j hz)
  refine ⟨k, ⟨hkj, hzk⟩, ?_⟩
  rintro l ⟨hlj, hzl⟩
  by_contra hkl
  exact absurd hzl
    ((disjoint_right.mp (pairwiseDisjoint_populationSeedRootPiece P' a κ' lambda hkl)) hzk)


end OTSelector.Reconstruction
