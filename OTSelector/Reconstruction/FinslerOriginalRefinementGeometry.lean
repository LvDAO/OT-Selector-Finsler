import OTSelector.Reconstruction.FinslerOriginalRefinementCover
import OTSelector.Reconstruction.FinslerOriginalGlobalRefinedAtlas
import OTSelector.Reconstruction.FinslerOriginalRefinedSeedWindow
import OTSelector.Reconstruction.FinslerOriginalWindowRefinementCoverage
import OTSelector.Reconstruction.FinslerSeedRootPartition
import OTSelector.Geometry.Finsler.CalibratedSeedWindowRestriction

/-!
# Producer-cover geometry for the refined atlas

This file closes the geometric interface between the global refined atlas of
`FinslerOriginalGlobalRefinedAtlas` and the refinement-cover partition lemma of
`FinslerOriginalRefinementCover`.

## Part (1): the window-level refinement relation

The partition lemma consumes two producer inputs: piece-level containment
`refinedWindowPiece P' k ⊆ populationWindowPiece P (parent k)` and a cover of
each parent piece by its refined pieces up to a joint-law-null correction. We
isolate the concrete geometry that yields them in a `WindowRefinement` datum:

* `image_subset`: every refined window image lies in its parent window image;
* `fresh`: every refined window image avoids the parent images of *earlier*
  parents (the window covers only the fresh part of its parent);
* `sibling`: refined windows over the same parent have disjoint images;
* `image_cover`: the parent window image is covered by the refined window images
  over its index;
* `parent_mono`: the refined enumeration is parent-major (children of smaller
  parents come first).

From this datum we derive *exactly* the producer hypotheses of the partition
lemma, with the joint-law-null correction empty (no leftover at all): piece
containment and `populationWindowPiece P j ⊆ ⋃ refined pieces over j`.

## Part (2): the cross-atlas label bridge

For the label side we construct the per-window refinement from a common chart
core-section datum `CoreSectionChartData`: the data of the level-seed constructor
(`exists_levelSeedPatch_of_coreSection_with_coordinates`). Given a parent
compact chart core `K` inside the open chart domain, the concentric compact cores
`K ∩ closedBall (σ 0) i` cover `K`, and the constructor produces, for each `i`,
a refined seed patch whose labels are the preimage of `V ∩ σ⁻¹'(K ∩ closedBall (σ 0) i)`.
Consequently the parent labels `V ∩ σ⁻¹'K` are covered by the refined labels, and
for any window `P` whose seed labels realize the parent core, the original label
slice `seedLabelSlice a B` maps into the union of the refined labels under the
linear identifications of the chart label space.

## Remaining sub-gaps

* The `WindowRefinement` fields (freshness of the refined images inside the fresh
  part of the parent, sibling disjointness, and the image cover) are producer
  covering geometry: constructing the certified ball-core sub-windows so that they
  cover the fresh part of each parent window is not formalized; the certified
  chart-ball construction supplies label sets, not the manifold image cover.
* The chart core-section datum is the constructor input of the level-seed lane; it
  is supplied per chart by the producer cover, but this file does not extract it
  from the global atlas construction (the global atlas theorem only exposes the
  resulting window family, not the per-window chart data).
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

/-! ## (1) The window-level refinement relation -/

/-- **A geometric refinement of a countable atlas by a single global refined
family.**  The refined family is globally enumerated with a parent map, the
refined images sit in their parent images, avoid all parent images of earlier
parents, are pairwise disjoint among siblings, cover the parent image, and the
enumeration is parent-major. -/
structure WindowRefinement (F : ContinuousFinslerNorm E M) (u : M → ℝ)
    (P P' : ℕ → F.CalibratedSeedWindow u) (parent : ℕ → ℕ) : Prop where
  parent_mono : ∀ k k', k < k' → parent k ≤ parent k'
  image_subset : ∀ k, refinedWindowImage P' k ⊆
    (P (parent k)).toManifold '' (P (parent k)).domain
  fresh : ∀ k, Disjoint (refinedWindowImage P' k)
    (⋃ j ∈ {j | j < parent k}, (P j).toManifold '' (P j).domain)
  sibling : ∀ k k', parent k = parent k' → k ≠ k' →
    Disjoint (refinedWindowImage P' k) (refinedWindowImage P' k')
  image_cover : ∀ j, (P j).toManifold '' (P j).domain ⊆
    ⋃ k ∈ {k | parent k = j}, refinedWindowImage P' k

/-- The population window piece is the fresh part of the window image: the image
intersected with the complements of all earlier parent images. -/
theorem populationWindowPiece_eq_inter
    (P : ℕ → F.CalibratedSeedWindow u) (j : ℕ) :
    populationWindowPiece P j =
      (P j).toManifold '' (P j).domain ∩
        ⋂ i < j, (((P i).toManifold '' (P i).domain)ᶜ) := by
  rw [populationWindowPiece, disjointed_eq_inter_compl]

/-- **Piece-level containment from the refinement relation.**  A globally
disjointified refined piece lies in the parent piece over its parent index: it
lies in the parent image and is disjoint from every earlier parent image. -/
theorem refinement_piece_subset
    (P P' : ℕ → F.CalibratedSeedWindow u) (parent : ℕ → ℕ)
    (R : WindowRefinement F u P P' parent) (k : ℕ) :
    refinedWindowPiece P' k ⊆ populationWindowPiece P (parent k) := by
  intro x hx
  have hximg : x ∈ refinedWindowImage P' k := refinedWindowPiece_subset_image P' k hx
  have hxpar : x ∈ (P (parent k)).toManifold '' (P (parent k)).domain :=
    R.image_subset k hximg
  have hxnot : x ∉ ⋃ i ∈ {i | i < parent k}, (P i).toManifold '' (P i).domain := by
    intro hxearlier
    obtain ⟨i, hi_lt, hxi⟩ := mem_iUnion₂.mp hxearlier
    exact (Set.disjoint_left.mp (R.fresh k)) hximg (mem_iUnion₂.mpr ⟨i, hi_lt, hxi⟩)
  rw [populationWindowPiece_eq_inter]
  refine ⟨hxpar, ?_⟩
  simp only [mem_iInter, mem_compl_iff]
  intro i hi hxi
  exact hxnot (mem_iUnion₂.mpr ⟨i, hi, hxi⟩)

/-- **Parent-piece coverage from the refinement relation.**  Every parent piece is
covered by the disjointified refined pieces over its parent index. -/
theorem refinement_piece_cover
    (P P' : ℕ → F.CalibratedSeedWindow u) (parent : ℕ → ℕ)
    (R : WindowRefinement F u P P' parent) (j : ℕ) :
    populationWindowPiece P j ⊆ ⋃ k ∈ {k | parent k = j}, refinedWindowPiece P' k := by
  intro x hx
  rw [populationWindowPiece_eq_inter] at hx
  simp only [mem_inter_iff, mem_iInter, mem_compl_iff] at hx
  obtain ⟨hximg, hxnot⟩ := hx
  obtain ⟨k, hkparent, hxk⟩ := mem_iUnion₂.mp (R.image_cover j hximg)
  refine mem_iUnion₂.mpr ⟨k, hkparent, ?_⟩
  have hxk_img : x ∈ refinedWindowImage P' k := hxk
  rw [refinedWindowPiece, disjointed_eq_inter_compl]
  refine ⟨hxk_img, ?_⟩
  simp only [mem_iInter, mem_compl_iff]
  intro k' hk'lt hxk'
  have hmono : parent k' ≤ parent k := R.parent_mono k' k hk'lt
  rcases lt_or_eq_of_le hmono with hlt | heq
  · have hxpar' : x ∈ (P (parent k')).toManifold '' (P (parent k')).domain :=
      R.image_subset k' hxk'
    exact hxnot (parent k')
      (by simpa [show parent k = j from hkparent] using hlt) hxpar'
  · exact (Set.disjoint_left.mp (R.sibling k k' heq.symm (ne_of_gt hk'lt))) hxk_img hxk'

/-- **The refinement relation supplies the producer hypotheses of the partition
lemma with an empty joint-law-null correction.**  The only correction needed is
the empty set, which is measurable and carries zero joint law. -/
theorem refinement_producerCover
    (P P' : ℕ → F.CalibratedSeedWindow u) (parent : ℕ → ℕ) (a : M → Z)
    (eta : Measure M) (R : WindowRefinement F u P P' parent) :
    (∀ k, refinedWindowPiece P' k ⊆ populationWindowPiece P (parent k)) ∧
    (∀ j, (fun x => (a x, u x)) ''
      (populationWindowPiece P j \
        ⋃ k ∈ {k | parent k = j}, refinedWindowPiece P' k) ⊆ (∅ : Set (Z × ℝ))) ∧
    (eta.map (fun x => (a x, u x))) (∅ : Set (Z × ℝ)) = 0 := by
  refine ⟨refinement_piece_subset P P' parent R, ?_, by simp⟩
  intro j
  have hsub : populationWindowPiece P j \
      ⋃ k ∈ {k | parent k = j}, refinedWindowPiece P' k = ∅ :=
    Set.sdiff_eq_empty.mpr (refinement_piece_cover P P' parent R j)
  rw [hsub]
  simp

/-! ## (2) The cross-atlas label bridge -/

/-- **Common chart core-section datum.**  This packages exactly the hypotheses of
the level-seed constructor `exists_levelSeedPatch_of_coreSection_with_coordinates`
for one chart selected at `old`: the potential `G`, the Euler--Lagrange family
`Γ`, the section `σ` (the chart core section), the covector `p`, the open label
set `V`, the level `q`, and the uniform partner data on the whole open chart
domain `U`.  The constructor is then applicable to *any* compact core inside
`U` containing the section point. -/
structure CoreSectionChartData (F : ContinuousFinslerNorm E M) (u : M → ℝ) where
  old : M
  G : E → ℝ
  L : ℝ≥0
  U : Set E
  U_open : IsOpen U
  U_target : U ⊆ (extChartAt 𝓘(ℝ, E) old).target
  Γ : E → ℝ → M
  δ : ℝ
  δ_pos : 0 < δ
  p : E →L[ℝ] ℝ
  V : Set p.ker
  V_open : IsOpen V
  σ : p.ker → E
  G_contDiff : ContDiff ℝ 1 G
  G_lip : LipschitzWith L (fderiv ℝ G)
  match_U : EqOn (fderiv ℝ G) (fderiv ℝ (u ∘ (extChartAt 𝓘(ℝ, E) old).symm)) U
  val_U : EqOn G (u ∘ (extChartAt 𝓘(ℝ, E) old).symm) U
  actual_U : ∀ y ∈ U,
    HasFDerivAt (u ∘ (extChartAt 𝓘(ℝ, E) old).symm) (fderiv ℝ G y) y
  EL_U : ∀ x ∈ U, F.IsEulerLagrangeOn (Γ x) univ
  init_U : ∀ x ∈ U, Γ x 0 = (extChartAt 𝓘(ℝ, E) old).symm x
  mom_U : ∀ x ∈ U, F.chartMomentumFamily old Γ (x, 0) = (x, fderiv ℝ G x)
  partners_U : letI : MetricSpace M := F.metricSpace; ∀ x ∈ U, ∃ a b : M,
    dist a ((extChartAt 𝓘(ℝ, E) old).symm x) = δ ∧
    u ((extChartAt 𝓘(ℝ, E) old).symm x) - u a = δ ∧
    dist ((extChartAt 𝓘(ℝ, E) old).symm x) b = δ ∧
    u b - u ((extChartAt 𝓘(ℝ, E) old).symm x) = δ
  σ_contDiff : ContDiffOn ℝ 1 σ V
  σ_mapsTo : MapsTo σ V U
  σ_inj : InjOn σ V
  dim : Module.finrank ℝ p.ker + 1 = Module.finrank ℝ E
  zero_V : (0 : p.ker) ∈ V
  covector_eq : p = fderiv ℝ G (σ 0)
  σ_deriv : HasFDerivAt σ p.ker.subtypeL 0
  σ_imm : ∀ w ∈ V, Function.Injective (fderiv ℝ σ w)
  q : ℚ
  G_level : ∀ w ∈ V, G (σ w) = (q : ℝ)

/-- **The level-seed constructor from a common chart datum.**  For every compact
core `K` inside the open chart domain `U` and containing the section point
`σ 0`, the constructor produces a seed patch whose labels are the preimage of
`V ∩ σ⁻¹'K` in the chart label space. -/
theorem exists_levelSeedPatch_of_chartData
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : letI : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (C : CoreSectionChartData (F := F) (u := u))
    {K : Set E} (hK : IsCompact K) (hKU : K ⊆ C.U) (hcenter : C.σ 0 ∈ K) :
    ∃ A : F.CalibratedLevelSeedPatch u, ∃ e : A.covector.ker ≃L[ℝ] C.p.ker,
      A.openLabels = e ⁻¹' C.V ∧ A.labels = e ⁻¹' (C.V ∩ C.σ ⁻¹' K) ∧
      (∀ w t, A.curve w t = C.Γ (C.σ (e w)) t) ∧ A.level = C.q := by
  letI : MetricSpace M := F.metricSpace
  obtain ⟨A, e, h1, h2, h3, h4, -⟩ :=
    hF.exists_levelSeedPatch_of_coreSection_with_coordinates hcomplete C.old hu
      (K := K) (U := C.U) hK C.U_open hKU C.U_target
      (G := C.G) (L := C.L) C.G_contDiff C.G_lip
      (C.match_U.mono hKU) (C.val_U.mono hKU)
      (fun y hy => C.actual_U y (hKU hy))
      (Γ := C.Γ) C.EL_U C.init_U C.mom_U C.δ_pos
      (fun x hx => C.partners_U x (hKU hx))
      (p := C.p) (V := C.V) (σ := C.σ) C.V_open C.σ_contDiff C.σ_mapsTo
      C.σ_inj C.dim C.zero_V hcenter C.covector_eq C.σ_deriv C.σ_imm C.q C.G_level
  exact ⟨A, e, h1, h2, h3, h4⟩

/-- **The countable refined patch family covering a parent core.**  The concentric
compact cores `K ∩ closedBall (σ 0) i` cover the parent compact core `K`, and
each carries a refined seed patch whose labels are the preimage of
`V ∩ σ⁻¹'(K ∩ closedBall (σ 0) i)`.  Consequently the parent label set
`V ∩ σ⁻¹'K` is covered by the refined label sets, identified with the common
chart label space by the linear equivalences. -/
theorem exists_refinedPatchFamily_of_chartData
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : letI : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (C : CoreSectionChartData (F := F) (u := u))
    {K : Set E} (hK : IsCompact K) (hKU : K ⊆ C.U) (hKcenter : C.σ 0 ∈ K) :
    ∃ A : ℕ → F.CalibratedLevelSeedPatch u,
      ∃ e : ∀ i, (A i).covector.ker ≃L[ℝ] C.p.ker,
        (∀ i, (A i).labels =
          (e i) ⁻¹' (C.V ∩ C.σ ⁻¹' (K ∩ closedBall (C.σ 0) (i : ℝ)))) ∧
        (C.V ∩ C.σ ⁻¹' K) ⊆ ⋃ i, (e i) '' ((A i).labels) := by
  have hKc : ∀ i : ℕ, IsCompact (K ∩ closedBall (C.σ 0) (i : ℝ)) :=
    fun i => hK.inter_right isClosed_closedBall
  have hKcU : ∀ i : ℕ, K ∩ closedBall (C.σ 0) (i : ℝ) ⊆ C.U :=
    fun i x hx => hKU hx.1
  have hcent : ∀ i : ℕ, C.σ 0 ∈ K ∩ closedBall (C.σ 0) (i : ℝ) :=
    fun i => ⟨hKcenter, mem_closedBall_self (by positivity)⟩
  choose A e hprops using fun i =>
    exists_levelSeedPatch_of_chartData hF hcomplete hu C (hKc i) (hKcU i) (hcent i)
  have hlabels : ∀ i, (A i).labels = (e i) ⁻¹' (C.V ∩ C.σ ⁻¹' (K ∩ closedBall (C.σ 0) (i : ℝ))) :=
    fun i => (hprops i).2.1
  refine ⟨A, e, hlabels, ?_⟩
  intro w hw
  obtain ⟨hwV, hwK⟩ := hw
  obtain ⟨i, hi⟩ : ∃ i : ℕ, dist (C.σ w) (C.σ 0) < (i : ℝ) := exists_nat_gt _
  refine mem_iUnion.mpr ⟨i, ?_⟩
  have hmem : w ∈ C.V ∩ C.σ ⁻¹' (K ∩ closedBall (C.σ 0) (i : ℝ)) :=
    ⟨hwV, hwK, mem_closedBall.mpr (le_of_lt hi)⟩
  have hlab : (e i).symm w ∈ (A i).labels := by
    rw [hlabels i]
    simpa using hmem
  exact by simpa using mem_image_of_mem (e i) hlab

/-- **The cross-atlas label bridge at the parent window.**  If the parent window's
seed labels realize the parent core `V ∩ σ⁻¹'K` under a linear identification
`e₀` of the parent label space with the chart label space, then the image of the
original geometric label slice `seedLabelSlice a B` under `e₀` is covered by the
refined seed patches' labels, identified with the chart label space by their own
linear equivalences. This is the label-side refinement cover consumed by the
cross-atlas slice transfer. -/
theorem seedLabelSlice_refinedCover_of_chartData
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : letI : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (C : CoreSectionChartData (F := F) (u := u))
    {K : Set E} (hK : IsCompact K) (hKU : K ⊆ C.U) (hKcenter : C.σ 0 ∈ K)
    (P : F.CalibratedSeedWindow u) (a : M → Z) (B : Set Z)
    {e₀ : P.seed.covector.ker ≃L[ℝ] C.p.ker}
    (hseed : P.seed.labels = e₀ ⁻¹' (C.V ∩ C.σ ⁻¹' K)) :
    ∃ (A : ℕ → F.CalibratedLevelSeedPatch u)
      (e : ∀ i, (A i).covector.ker ≃L[ℝ] C.p.ker),
      (∀ i, (A i).labels =
        (e i) ⁻¹' (C.V ∩ C.σ ⁻¹' (K ∩ closedBall (C.σ 0) (i : ℝ)))) ∧
      e₀ '' (P.seedLabelSlice a B) ⊆
        ⋃ i, (e i) '' ((A i).labels) := by
  obtain ⟨A, e, hlabels, hcover⟩ :=
    exists_refinedPatchFamily_of_chartData hF hcomplete hu C hK hKU hKcenter
  refine ⟨A, e, hlabels, ?_⟩
  have hslice : P.seedLabelSlice a B ⊆ P.seed.labels := by
    intro w hw
    exact hw.1.1
  have himg : e₀ '' P.seed.labels = C.V ∩ C.σ ⁻¹' K := by
    rw [hseed, image_preimage_eq _ e₀.surjective]
  calc e₀ '' (P.seedLabelSlice a B) ⊆ e₀ '' P.seed.labels := image_mono hslice
    _ = C.V ∩ C.σ ⁻¹' K := himg
    _ ⊆ ⋃ i, (e i) '' ((A i).labels) := hcover


/-! ## Closing the producer interface -/

/-- **The geometric refinement relation discharges the producer hypotheses of the
refinement-cover sum decomposition.**  Instantiated with the empty joint-law-null
correction, the window-level refinement datum yields the C(a) sum decomposition
of `FinslerOriginalRefinementCover.refinementCover_map_eq_sum` outright. -/
theorem windowRefinement_refinementCover_map_eq_sum
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : letI : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (P P' : ℕ → F.CalibratedSeedWindow u) (parent : ℕ → ℕ) (a : M → Z)
    (eta : Measure M) (hpair : Measurable fun x => (a x, u x))
    (R : WindowRefinement F u P P' parent) (j : ℕ) :
    (eta.restrict (populationWindowPiece P j)).map (fun x => (a x, u x)) =
      Measure.sum (fun k => if parent k = j then
        (eta.restrict (refinedWindowPiece P' k)).map (fun x => (a x, u x)) else 0) :=
  refinementCover_map_eq_sum hF hcomplete hu P P' parent a eta hpair
    (refinement_piece_subset P P' parent R)
    (N := ∅) MeasurableSet.empty (by simp)
    (fun j => (refinement_producerCover P P' parent a eta R).2.1 j) j

end OTSelector.Reconstruction
