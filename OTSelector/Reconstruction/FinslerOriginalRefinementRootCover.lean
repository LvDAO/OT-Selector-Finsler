import OTSelector.Reconstruction.FinslerOriginalRefinementGeometry
import OTSelector.Reconstruction.FinslerSeedRootPartition

/-!
# Refinement cover at population root-piece granularity

This file closes the remaining gaps of `FinslerOriginalRefinementGeometry.lean` at
the level of the original population root pieces.

## (1) Root-piece refinement and the C(b) exactly-one-window form

`RootPieceRefinement` is the root-piece analogue of `WindowRefinement`: a parent
family `S` of root sets, a refined family `T`, and a parent map, with
containment, freshness against earlier parents, sibling disjointness, cover of
every parent by its children, and a parent-major enumeration. We prove:

* `rootPiece_subset`: every globally disjointified refined root piece lies in the
  parent root piece over its parent index;
* `rootPiece_cover`: every parent root piece is covered by its refined pieces;
* `rootPiece_eq_iUnion`: the parent piece is *exactly* the union of its refined
  pieces (both inclusions together);
* `existsUnique_refinedRootPiece`: the C(b) form — every point of a parent root
  piece belongs to *exactly one* refined piece over that parent index.

For a concrete family these are the statements consumed by the kernel-marked lane
at `populationSeedRootPiece` granularity. We also record the generic
`lambda`-a.e. exactly-one-window form for the population root partition itself
(`ae_existsUnique_populationSeedRootPiece`), from the normalization law and
pairwise disjointness.

## (2) The label bridge at root-piece granularity

For the concrete chart-data construction of `FinslerOriginalRefinementGeometry`
we push the seed-label cover to the original root domains:
`refinedRootDomain_subset_parent`, `parentRootDomain_subset_union_refined` and,
under equality of the reference label laws, the reference-root cover
`parentReferenceRoots_subset_union_refined`. This gives the `S`/`T` instance of
`RootPieceRefinement` from concrete chart data plus a producer freshness/order
condition, and identifies exactly which root-level facts remain producer inputs.

## (3) Chart-data extraction

The global atlas theorem exposes only the window family, not the per-window chart
data. The precise producer map needed is recorded at the end of this file: a map
from parent indices to `CoreSectionChartData` together with the parent compact
cores and the parent patch realizations. The per-window chart construction of
`FinslerRationalLevelSeeds` supplies such data per chart; matching it to the
atlas enumeration is the remaining producer step.
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

/-! ## (1) Abstract root-piece refinement -/

/-- **A root-piece refinement.**  Parent root sets `S`, refined root sets `T`, a
parent map, containment of refined sets in their parents, freshness against
earlier parents, sibling disjointness, cover of every parent, and a parent-major
enumeration. Both families are Borel in the original label space. -/
structure RootPieceRefinement (S T : ℕ → Set Z) (parent : ℕ → ℕ) : Prop where
  measurable_S : ∀ j, MeasurableSet (S j)
  measurable_T : ∀ k, MeasurableSet (T k)
  parent_mono : ∀ k k', k < k' → parent k ≤ parent k'
  subset : ∀ k, T k ⊆ S (parent k)
  fresh : ∀ k, Disjoint (T k) (⋃ j ∈ {j | j < parent k}, S j)
  sibling : ∀ k k', parent k = parent k' → k ≠ k' → Disjoint (T k) (T k')
  cover : ∀ j, S j ⊆ ⋃ k ∈ {k | parent k = j}, T k

section RootPiece

variable {S T : ℕ → Set Z} {parent : ℕ → ℕ}

/-- **Piece-level containment for root pieces.**  A disjointified refined root
piece lies in the parent root piece over its parent index. -/
theorem rootPiece_subset (R : RootPieceRefinement S T parent) (k : ℕ) :
    disjointed T k ⊆ disjointed S (parent k) := by
  intro z hz
  have hT : z ∈ T k := disjointed_subset T k hz
  have hSparent : z ∈ S (parent k) := R.subset k hT
  have hnot : z ∉ ⋃ j ∈ {j | j < parent k}, S j := by
    intro hzearlier
    obtain ⟨i, hi, hzi⟩ := mem_iUnion₂.mp hzearlier
    exact (Set.disjoint_left.mp (R.fresh k)) hT (mem_iUnion₂.mpr ⟨i, hi, hzi⟩)
  rw [disjointed_eq_inter_compl]
  refine ⟨hSparent, ?_⟩
  simp only [mem_iInter, mem_compl_iff]
  exact fun i hi hzi => hnot (mem_iUnion₂.mpr ⟨i, hi, hzi⟩)

/-- **Parent-piece coverage for root pieces.**  Every parent root piece is
covered by its refined pieces. -/
theorem rootPiece_cover (R : RootPieceRefinement S T parent) (j : ℕ) :
    disjointed S j ⊆ ⋃ k ∈ {k | parent k = j}, disjointed T k := by
  intro z hz
  have hzS : z ∈ S j := disjointed_subset S j hz
  have hznot : z ∉ ⋃ i ∈ {i | i < j}, S i := by
    intro h
    obtain ⟨i, hi, hzi⟩ := mem_iUnion₂.mp h
    have hz' := hz
    rw [disjointed_eq_inter_compl] at hz'
    simp only [mem_inter_iff, mem_iInter, mem_compl_iff] at hz'
    exact hz'.2 i hi hzi
  obtain ⟨k, hkparent, hzk⟩ := mem_iUnion₂.mp (R.cover j hzS)
  refine mem_iUnion₂.mpr ⟨k, hkparent, ?_⟩
  rw [disjointed_eq_inter_compl]
  refine ⟨hzk, ?_⟩
  simp only [mem_iInter, mem_compl_iff]
  intro k' hk'lt hzk'
  have hmono : parent k' ≤ parent k := R.parent_mono k' k hk'lt
  rcases lt_or_eq_of_le hmono with hlt | heq
  · have hS' : z ∈ S (parent k') := R.subset k' hzk'
    exact hznot (mem_iUnion₂.mpr ⟨parent k', by simpa [show parent k = j from hkparent] using hlt, hS'⟩)
  · exact (Set.disjoint_left.mp (R.sibling k k' heq.symm (ne_of_gt hk'lt))) hzk hzk'

/-- **The parent root piece is exactly the union of its refined pieces.** -/
theorem rootPiece_eq_iUnion (R : RootPieceRefinement S T parent) (j : ℕ) :
    disjointed S j = ⋃ k ∈ {k | parent k = j}, disjointed T k := by
  ext z
  constructor
  · intro hz
    exact rootPiece_cover R j hz
  · intro hz
    obtain ⟨k, hkparent, hzk⟩ := mem_iUnion₂.mp hz
    have hsub := rootPiece_subset R k
    rw [show parent k = j from hkparent] at hsub
    exact hsub hzk

/-- **The C(b) exactly-one-window form at root-piece granularity.**  Every point
of a parent root piece belongs to exactly one refined root piece over that parent
index. -/
theorem existsUnique_refinedRootPiece (R : RootPieceRefinement S T parent)
    {j : ℕ} {z : Z} (hz : z ∈ disjointed S j) :
    ∃! k, parent k = j ∧ z ∈ disjointed T k := by
  obtain ⟨k, hkparent, hzk⟩ := mem_iUnion₂.mp (rootPiece_cover R j hz)
  refine ⟨k, ⟨hkparent, hzk⟩, ?_⟩
  rintro l ⟨hlparent, hzl⟩
  by_contra hkl
  have hTl : z ∈ T l := disjointed_subset T l hzl
  have hTk : z ∈ T k := disjointed_subset T k hzk
  exact (Set.disjoint_left.mp
    (R.sibling k l (hkparent.trans hlparent.symm) (fun hlk => hkl hlk.symm))) hTk hTl

end RootPiece

/-! ## The generic population root partition: lambda-a.e. exactly one window -/

/-- **Exactly-one-window a.e. form for the population root partition.**  Under the
normalization of the actual conditional window law, `lambda`-almost every
original root belongs to exactly one globally disjointified seed root piece. -/
theorem ae_existsUnique_populationSeedRootPiece
    (P : ℕ → F.CalibratedSeedWindow u) (a : M → Z)
    (κ : ∀ j, Measure (P j).seed.covector.ker) (lambda : Measure Z)
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : letI : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))
    {η : Measure M} [IsFiniteMeasure η] {ρ : M → ℝ} {v : ℕ → E → ℝ}
    (hlaw : PopulationConditionalWindowLaw P a κ lambda η ρ v)
    (horder : letI : MetricSpace M := F.metricSpace
      ∀ x ∈ F.potentialRegularDomain u, ∀ y ∈ F.potentialRegularDomain u,
        (a x = a y ∧ u x ≤ u y) ↔ u y - u x = dist x y)
    (hκ : ∀ j, SigmaFinite (κ j)) :
    ∀ᵐ z ∂lambda, ∃! k, z ∈ populationSeedRootPiece P a κ lambda k := by
  filter_upwards [PopulationConditionalWindowLaw.ae_mem_populationSeedRootPieces P a κ
    lambda hF hcomplete hu ha hinj hlaw horder hκ] with z hz
  obtain ⟨k, hk⟩ := mem_iUnion.mp hz
  refine ⟨k, hk, fun l hl => ?_⟩
  by_contra hne
  have hD := pairwiseDisjoint_populationSeedRootPiece P a κ lambda
    (show k ≠ l from fun h => hne h.symm)
  exact (Set.disjoint_iff.mp hD) (Set.mem_inter hk hl)



/-! ## (2) The chart-data root cover -/

variable {a : M → Z}

/-- **Root-domain containment for the chart-data refinement.**  A refined seed
patch's original root domain (the `a`-image of its initial curve points) lies in
the parent patch's root domain, because the refined labels correspond, under the
chart linear identifications, to a subset of the parent core labels and the curves
agree through the common chart datum. -/
theorem refinedRootDomain_subset_parent
    (C : CoreSectionChartData (F := F) (u := u))
    (A0 : F.CalibratedLevelSeedPatch u) (e0 : A0.covector.ker ≃L[ℝ] C.p.ker)
    {K : Set E}
    (hA0lab : A0.labels = e0 ⁻¹' (C.V ∩ C.σ ⁻¹' K))
    (hA0cur : ∀ w t, A0.curve w t = C.Γ (C.σ (e0 w)) t)
    (A : ℕ → F.CalibratedLevelSeedPatch u)
    (e : ∀ i, (A i).covector.ker ≃L[ℝ] C.p.ker)
    (hAlab : ∀ i, (A i).labels =
      (e i) ⁻¹' (C.V ∩ C.σ ⁻¹' (K ∩ closedBall (C.σ 0) (i : ℝ))))
    (hAcur : ∀ i w t, (A i).curve w t = C.Γ (C.σ (e i w)) t)
    (i : ℕ) :
    populationSeedRootDomain (A i) a ⊆ populationSeedRootDomain A0 a := by
  rintro z ⟨w, rfl⟩
  have hiff : ∀ x, x ∈ (A i).labels ↔
      (e i) x ∈ C.V ∩ C.σ ⁻¹' (K ∩ closedBall (C.σ 0) (i : ℝ)) := by
    intro x
    rw [hAlab i, Set.mem_preimage]
  have hw : (e i) (w : (A i).covector.ker) ∈
      C.V ∩ C.σ ⁻¹' (K ∩ closedBall (C.σ 0) (i : ℝ)) :=
    (hiff (w : (A i).covector.ker)).mp w.property
  have hmemK : (e i) (w : (A i).covector.ker) ∈ C.V ∩ C.σ ⁻¹' K :=
    ⟨hw.1, hw.2.1⟩
  set w0 : A0.covector.ker := e0.symm ((e i) (w : (A i).covector.ker)) with hw0
  have hw0lab : w0 ∈ A0.labels := by
    rw [hA0lab, Set.mem_preimage]
    rw [hw0, ContinuousLinearEquiv.apply_symm_apply]
    exact hmemK
  refine ⟨⟨w0, hw0lab⟩, ?_⟩
  show a (A0.curve (⟨w0, hw0lab⟩ : A0.labels) 0) = a ((A i).curve w 0)
  have harg : e0 w0 = (e i) (w : (A i).covector.ker) := by
    rw [hw0, ContinuousLinearEquiv.apply_symm_apply]
  rw [hA0cur, hAcur, harg]

/-- **Root-domain cover for the chart-data refinement.**  The parent patch's root
domain is covered by the refined root domains, because the concentric refined
cores cover the parent compact core. -/
theorem parentRootDomain_subset_union_refined
    (C : CoreSectionChartData (F := F) (u := u))
    (A0 : F.CalibratedLevelSeedPatch u) (e0 : A0.covector.ker ≃L[ℝ] C.p.ker)
    {K : Set E}
    (hA0lab : A0.labels = e0 ⁻¹' (C.V ∩ C.σ ⁻¹' K))
    (hA0cur : ∀ w t, A0.curve w t = C.Γ (C.σ (e0 w)) t)
    (A : ℕ → F.CalibratedLevelSeedPatch u)
    (e : ∀ i, (A i).covector.ker ≃L[ℝ] C.p.ker)
    (hAlab : ∀ i, (A i).labels =
      (e i) ⁻¹' (C.V ∩ C.σ ⁻¹' (K ∩ closedBall (C.σ 0) (i : ℝ))))
    (hAcur : ∀ i w t, (A i).curve w t = C.Γ (C.σ (e i w)) t) :
    populationSeedRootDomain A0 a ⊆ ⋃ i, populationSeedRootDomain (A i) a := by
  rintro z ⟨w0, rfl⟩
  have hiff0 : ∀ x, x ∈ A0.labels ↔ e0 x ∈ C.V ∩ C.σ ⁻¹' K := by
    intro x
    rw [hA0lab, Set.mem_preimage]
  have hmem : e0 (w0 : A0.covector.ker) ∈ C.V ∩ C.σ ⁻¹' K :=
    (hiff0 (w0 : A0.covector.ker)).mp w0.property
  obtain ⟨i, hi⟩ : ∃ i : ℕ, dist (C.σ (e0 (w0 : A0.covector.ker))) (C.σ 0) < (i : ℝ) :=
    exists_nat_gt _
  have hKi : C.σ (e0 (w0 : A0.covector.ker)) ∈ K ∩ closedBall (C.σ 0) (i : ℝ) :=
    ⟨hmem.2, mem_closedBall.mpr (le_of_lt hi)⟩
  have hmemKi : e0 (w0 : A0.covector.ker) ∈
      C.V ∩ C.σ ⁻¹' (K ∩ closedBall (C.σ 0) (i : ℝ)) :=
    ⟨hmem.1, hKi⟩
  set w : (A i).covector.ker := (e i).symm (e0 (w0 : A0.covector.ker)) with hw
  have hwlab : w ∈ (A i).labels := by
    rw [hAlab i, Set.mem_preimage]
    rw [hw, ContinuousLinearEquiv.apply_symm_apply]
    exact hmemKi
  refine mem_iUnion.mpr ⟨i, ⟨⟨w, hwlab⟩, ?_⟩⟩
  show a ((A i).curve (⟨w, hwlab⟩ : (A i).labels) 0) = a (A0.curve w0 0)
  have harg : (e i) w = e0 (w0 : A0.covector.ker) := by
    rw [hw, ContinuousLinearEquiv.apply_symm_apply]
  rw [hAcur, hA0cur, harg]

/-- **Reference-root cover for the chart-data refinement.**  If the refined and
parent patches push the same label reference law to the original root space, then
every parent reference root (finite nonzero original reference density) is a
refined reference root, using the root-domain cover. -/
theorem parentReferenceRoots_subset_union_refined
    (A0 : F.CalibratedLevelSeedPatch u) (a : M → Z)
    (κ0 : Measure A0.covector.ker) (lambda : Measure Z)
    (A : ℕ → F.CalibratedLevelSeedPatch u)
    (κ : ∀ i, Measure (A i).covector.ker)
    (hdom : populationSeedRootDomain A0 a ⊆ ⋃ i, populationSeedRootDomain (A i) a)
    (hlabref : ∀ i, populationSeedLabelReference (A i) a (κ i) =
      populationSeedLabelReference A0 a κ0) :
    populationSeedReferenceRoots A0 a κ0 lambda ⊆
      ⋃ i, populationSeedReferenceRoots (A i) a (κ i) lambda := by
  intro z hz
  obtain ⟨hdom0, hne, hlt⟩ := hz
  obtain ⟨i, hi⟩ := mem_iUnion.mp (hdom hdom0)
  refine mem_iUnion.mpr ⟨i, ⟨hi, ?_, ?_⟩⟩
  · rw [hlabref i]
    exact hne
  · rw [hlabref i]
    exact hlt


/-! ## (3) The producer map needed for the global atlas

The global atlas theorem `exists_global_refinedBallCore_atlas` exposes only the
window family, not the per-window chart data, so `CoreSectionChartData` cannot be
extracted from it internally. The precise producer map needed to instantiate
`RootPieceRefinement` globally is:

* `chartData : ∀ j, CoreSectionChartData (F := F) (u := u)` — the chart datum of
  the `j`-th parent window;
* `parentCore : (j : ℕ) → Set E` with `IsCompact (parentCore j)`,
  `parentCore j ⊆ (chartData j).U`, `(chartData j).σ 0 ∈ parentCore j`;
* `parentPatch : (j : ℕ) → F.CalibratedLevelSeedPatch u` and
  `parentEquiv : (j) → (parentPatch j).covector.ker ≃L[ℝ] (chartData j).p.ker`
  realizing the parent core labels and curves (the conclusions of
  `exists_levelSeedPatch_of_chartData` for the parent core, so that the parent
  window's seed patch is one of the constructor's patches);
* a parent-major enumeration of the refined windows that is *fresh*: refined
  windows attached to parent `j` do not meet root domains already used by earlier
  parents. Freshness, sibling disjointness and cover of the parent root set by
  the refined root sets are then exactly the `S`/`T` instance of
  `RootPieceRefinement` at `T := fun k ↦ populationSeedRootDomain (refinedPatch k) a`
  (or at the reference-root sets via `parentReferenceRoots_subset_union_refined`),
  giving `rootPiece_subset`, `rootPiece_cover`, `rootPiece_eq_iUnion` and
  `existsUnique_refinedRootPiece` for the population root pieces.

The per-chart construction of `FinslerRationalLevelSeeds` supplies such data per
chart; matching it to the global atlas enumeration is the remaining producer
step. -/

end OTSelector.Reconstruction
