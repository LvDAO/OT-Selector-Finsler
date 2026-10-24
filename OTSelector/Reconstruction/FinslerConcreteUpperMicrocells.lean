import OTSelector.Reconstruction.FinslerConcreteUpperShapeAtlas
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metric
import Mathlib.Analysis.SpecificLimits.Basic

/-!
A prescribed sequence of increasingly fine uniform grids covers an original
compact measurable cell by finitely many disjoint microboxes. The total added
ORIGINAL Haar mass tends to zero, even when the retained cell has empty interior.
-/
open Set MeasureTheory Filter Metric BoxIntegral
open scoped Topology ENNReal
noncomputable section
namespace OTSelector.Reconstruction
set_option maxHeartbeats 1800000
set_option linter.unusedSectionVars false

variable {ι : Type*} [Fintype ι]

/-- Literal original grid microboxes that meet the compact retained set. -/
def compactMicrocellIndices (B : Box ι) (K : Set (ι → ℝ)) (n : ℕ) [NeZero n] : Finset (ι → ℤ) := by
  classical
  exact (unitPartition.admissibleIndex n B).filter (fun ν ↦ ((unitPartition.box n ν : Set (ι → ℝ)) ∩ K).Nonempty)

/-- Finite microboxes meeting a compact set cover it and add only points within
one actual mesh diameter. The grid order is prescribed, not chosen afterward. -/
theorem compactMicrocell_cover_and_near (B : Box ι) (hB : hasIntegralVertices B)
    {K : Set (ι → ℝ)} (hKB : K ⊆ B) (n : ℕ) [NeZero n] :
    K ⊆ ⋃ ν ∈ compactMicrocellIndices B K n, (unitPartition.box n ν : Set (ι → ℝ)) ∧
    (⋃ ν ∈ compactMicrocellIndices B K n, (unitPartition.box n ν : Set (ι → ℝ))) ⊆
      Metric.cthickening (1 / (n : ℝ)) K := by
  classical
  constructor
  · intro x hx
    refine mem_iUnion₂.mpr ⟨unitPartition.index n x, ?_, ?_⟩
    · exact Finset.mem_filter.mpr ⟨unitPartition.mem_admissibleIndex_of_mem_box n hB (hKB hx),
        ⟨x, (unitPartition.mem_box_iff_index).mpr rfl, hx⟩⟩
    · exact (unitPartition.mem_box_iff_index).mpr rfl
  · intro x hx
    obtain ⟨ν, hν, hxν⟩ := mem_iUnion₂.mp hx
    obtain ⟨y, hyν, hyK⟩ := (Finset.mem_filter.mp hν).2
    apply Metric.mem_cthickening_of_dist_le x y (1 / (n : ℝ)) K hyK
    exact (Metric.dist_le_diam_of_mem (Box.isBounded_Icc _)
      (Box.coe_subset_Icc hxν) (Box.coe_subset_Icc hyν)).trans (unitPartition.diam_boxIcc n ν)

/-- Every prescribed grid order tending to infinity has a finite disjoint
cover of the original compact set whose added original measure tends to zero.
No boundary-null or interior assumption on that set is used. -/
theorem exists_compact_microcell_covers_hole_mass_tendsto_zero
    (μ : Measure (ι → ℝ)) [IsFiniteMeasureOnCompacts μ]
    {K : Set (ι → ℝ)} (hK : IsCompact K)
    (order : ℕ → ℕ) [∀ N, NeZero (order N)] (horder : Tendsto order atTop atTop) :
    ∃ C : ℕ → Finset (ι → ℤ),
      (∀ N, K ⊆ ⋃ ν ∈ C N, (unitPartition.box (order N) ν : Set (ι → ℝ))) ∧
      (∀ N, Set.PairwiseDisjoint (↑(C N) : Set (ι → ℤ))
        (fun ν ↦ (unitPartition.box (order N) ν : Set (ι → ℝ)))) ∧
      (∀ N ν, ν ∈ C N → ((unitPartition.box (order N) ν : Set (ι → ℝ)) ∩ K).Nonempty) ∧
      Tendsto (fun N ↦ μ ((⋃ ν ∈ C N, (unitPartition.box (order N) ν : Set (ι → ℝ))) \ K))
        atTop (𝓝 0) := by
  classical
  obtain ⟨B, hB, hKB⟩ := BoxIntegral.le_hasIntegralVertices_of_isBounded hK.isBounded
  let C := fun N ↦ compactMicrocellIndices B K (order N)
  have hnear (N) := compactMicrocell_cover_and_near B hB hKB (order N)
  refine ⟨C, fun N ↦ (hnear N).1, ?_, ?_, ?_⟩
  · intro N ν hν ν' hν' hne
    exact unitPartition.disjoint.mp hne
  · intro N ν hν
    exact (Finset.mem_filter.mp hν).2
  · have hmesh : Tendsto (fun N ↦ 1 / (order N : ℝ)) atTop (𝓝 0) :=
      tendsto_one_div_atTop_nhds_zero_nat.comp horder
    have houter := (tendsto_measure_cthickening_of_isCompact (μ := μ) hK).comp hmesh
    have hsub := ENNReal.Tendsto.sub houter (tendsto_const_nhds (x := μ K)) (Or.inr hK.measure_lt_top.ne)
    have hhole : Tendsto (fun N ↦ μ (Metric.cthickening (1 / (order N : ℝ)) K \ K))
        atTop (𝓝 0) := by
      simp_rw [measure_sdiff (Metric.self_subset_cthickening K) hK.measurableSet.nullMeasurableSet hK.measure_lt_top.ne]
      simpa only [tsub_self, Function.comp_apply] using hsub
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hhole (fun _ ↦ bot_le)
    intro N
    exact measure_mono (sdiff_subset_sdiff_left (hnear N).2)


/-- Every original finite measurable cell admits deterministic retained pieces
on any prescribed increasingly fine grids. The original mass discarded is
uniformly small and the original added full-box mass vanishes. The retained
cell may have empty interior or positive boundary measure. -/
theorem exists_original_measurable_microcell_approximation
    (μ : Measure (ι → ℝ)) [IsLocallyFiniteMeasure μ]
    {s : Set (ι → ℝ)} (hs : MeasurableSet s) (hfinite : μ s ≠ ∞)
    {ε : ℝ≥0∞} (hε : 0 < ε)
    (order : ℕ → ℕ) [∀ N, NeZero (order N)] (horder : Tendsto order atTop atTop) :
    ∃ (K : Set (ι → ℝ)) (C : ℕ → Finset (ι → ℤ)), K ⊆ s ∧ IsCompact K ∧
      (∀ N, K ⊆ ⋃ ν ∈ C N, (unitPartition.box (order N) ν : Set (ι → ℝ))) ∧
      (∀ N, Set.PairwiseDisjoint (↑(C N) : Set (ι → ℤ))
        (fun ν ↦ (unitPartition.box (order N) ν : Set (ι → ℝ)))) ∧
      (∀ N, μ (s \ ⋃ ν ∈ C N, (unitPartition.box (order N) ν : Set (ι → ℝ))) < ε) ∧
      Tendsto (fun N ↦ μ ((⋃ ν ∈ C N, (unitPartition.box (order N) ν : Set (ι → ℝ))) \ s))
        atTop (𝓝 0) := by
  obtain ⟨K, hKs, hK, hsmall⟩ := hs.exists_isCompact_sdiff_lt hfinite hε.ne'
  obtain ⟨C, hcover, hdisjoint, hmeet, hhole⟩ :=
    exists_compact_microcell_covers_hole_mass_tendsto_zero μ hK order horder
  refine ⟨K, C, hKs, hK, hcover, hdisjoint, ?_, ?_⟩
  · intro N
    exact (measure_mono (sdiff_subset_sdiff_right (hcover N))).trans_lt hsmall
  · apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hhole (fun _ ↦ bot_le)
    intro N
    exact measure_mono (sdiff_subset_sdiff_right hKs)


open Function ProbabilityTheory Manifold OTSelector.Geometry
open scoped ContDiff
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {P : ℕ → F.CalibratedSeedWindow u} {a : M → (ℚ → M)}
  {κ : ∀ j, Measure (P j).seed.covector.ker} {lambda : Measure (ℚ → M)}
  [IsFiniteMeasure lambda] [∀ j, SigmaFinite (κ j)]
  {η₀ η₁ : Measure M} [IsFiniteMeasure η₀] [IsFiniteMeasure η₁]
  {ρ₀ ρ₁ : M → ℝ} {v : ℕ → E → ℝ} {b : (ℚ → M) × ℝ → M}
  {Good : (ℚ → M) → Prop} {r : ℝ} {δ loss : ℝ≥0∞}

/-- An actual original measurable Finsler cell has deterministic prescribed
microgrids with uniformly small ORIGINAL root loss and vanishing model filling
volume. The original label map and reference root are preserved. -/
theorem PopulationLocalPressureCore.exists_cell_microscopic_coordinate_cubes
    (D : PopulationLocalPressureCore P a κ lambda η₀ η₁ ρ₀ ρ₁ v b Good r δ loss)
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _inst : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))
    (i : Fin D.haar.continuous.count) {L : Set (ℚ → M)} (hL : MeasurableSet L)
    (hsub : L ⊆ (D.haar.continuous.coefficient i).roots)
    {q : ℕ} (e : (P (D.haar.continuous.coefficient i).seedIndex).seed.covector.ker ≃L[ℝ]
      (Fin q → ℝ)) {ε : ℝ≥0∞} (hε : 0 < ε)
    (order : ℕ → ℕ) [∀ N, NeZero (order N)] (horder : Tendsto order atTop atTop) :
    let Seed := (P (D.haar.continuous.coefficient i).seedIndex).seed
    let coord := OTSelector.Probability.atlasSeedCoord Seed e a
    ∃ C : ℕ → Finset (Fin q → ℤ),
      (∀ N, Set.PairwiseDisjoint (↑(C N) : Set (Fin q → ℤ))
        (fun ν ↦ (unitPartition.box (order N) ν : Set (Fin q → ℝ)))) ∧
      (∀ N, lambda (L \ coord ⁻¹' (⋃ ν ∈ C N,
        (unitPartition.box (order N) ν : Set (Fin q → ℝ)))) < ε) ∧
      Tendsto (fun N ↦ volume ((⋃ ν ∈ C N,
        (unitPartition.box (order N) ν : Set (Fin q → ℝ))) \ (coord '' L))) atTop (𝓝 0) := by
  classical
  letI : MetricSpace M := F.metricSpace
  letI : ProperSpace M := F.properSpace_of_complete hcomplete
  letI : PolishSpace M := inferInstance
  letI : BorelSpace (ℚ → M) := inferInstance
  let Seed := (P (D.haar.continuous.coefficient i).seedIndex).seed
  let R := populationSeedRootLabelValue Seed a
  let coord := OTSelector.Probability.atlasSeedCoord Seed e a
  let s := coord '' L
  have hcoord : Measurable coord :=
    OTSelector.Probability.measurable_atlasSeedCoord Seed hF hcomplete hu ha hinj e
  have hs : MeasurableSet s := by
    have hR := D.haar.measurable_cell_label_image hcomplete i hL hsub
    have h := e.toHomeomorph.measurableEmbedding.measurableSet_image.mpr hR
    change MeasurableSet (e '' (R '' L)) at h
    change MeasurableSet ((fun z ↦ e (R z)) '' L)
    simpa only [image_image] using h
  have hsubI : L ⊆ (D.haar.intensity i).roots := by rwa [D.haar.intensity_roots]
  have hcompact : IsCompact (e '' (R '' (D.haar.intensity i).roots)) :=
    (D.haar.intensity i).compact_labels.image e.continuous
  have hbounded : Bornology.IsBounded s := hcompact.isBounded.subset (by
    rintro _ ⟨z, hz, rfl⟩
    exact mem_image_of_mem e (mem_image_of_mem R (hsubI hz)))
  let original := (lambda.restrict L).map coord
  haveI : IsFiniteMeasure original := inferInstance
  let combined := original + (volume : Measure (Fin q → ℝ))
  haveI : IsFiniteMeasureOnCompacts combined := ⟨fun K hK ↦ by
    rw [show combined K = original K + volume K from Measure.add_apply _ _ _]
    exact ENNReal.add_lt_top.mpr ⟨measure_lt_top original K, hK.measure_lt_top⟩⟩
  have hfinite : combined s ≠ (∞ : ℝ≥0∞) := by
    rw [show combined s = original s + volume s from Measure.add_apply _ _ _]
    exact ENNReal.add_ne_top.mpr ⟨measure_ne_top _ _, hbounded.measure_lt_top.ne⟩
  obtain ⟨K, C, hKs, hK, hcover, hdisjoint, hsmall, hhole⟩ :=
    exists_original_measurable_microcell_approximation combined hs hfinite hε order horder
  refine ⟨C, hdisjoint, ?_, ?_⟩
  · intro N
    let cubes := ⋃ ν ∈ C N, (unitPartition.box (order N) ν : Set (Fin q → ℝ))
    have hcubes : MeasurableSet cubes := MeasurableSet.iUnion fun ν ↦
      MeasurableSet.iUnion fun _ ↦ (unitPartition.box (order N) ν).measurableSet_coe
    have hloss : original (s \ cubes) < ε :=
      (le_add_right le_rfl).trans_lt (hsmall N)
    have heq : coord ⁻¹' (s \ cubes) ∩ L = L \ coord ⁻¹' cubes := by
      ext z
      exact ⟨fun hz ↦ ⟨hz.2, hz.1.2⟩,
        fun hz ↦ ⟨⟨mem_image_of_mem coord hz.1, hz.2⟩, hz.1⟩⟩
    rw [show original (s \ cubes) = (lambda.restrict L).map coord (s \ cubes) from rfl,
      Measure.map_apply hcoord (hs.diff hcubes), Measure.restrict_apply (hcoord (hs.diff hcubes)), heq] at hloss
    exact hloss
  · apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hhole (fun _ ↦ bot_le)
    intro N
    exact le_add_left le_rfl

end OTSelector.Reconstruction
