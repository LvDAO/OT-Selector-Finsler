import OTSelector.Reconstruction.FinslerConcreteUpperMicrocells

/-! Original label mass and physical coordinate volume are both controlled by
the same actual compact inner approximation before prescribed grid covering. -/
open Set MeasureTheory Filter Metric BoxIntegral Function ProbabilityTheory Manifold OTSelector.Geometry
open scoped Topology ENNReal ContDiff BigOperators
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
/-- The literal half-open boxes have exactly their original total coordinate
volume, with no equal-volume assumption supplied by the caller. -/
theorem unitPartition_finite_union_volume (q n : ℕ) [NeZero n]
    (C : Finset (Fin q → ℤ)) :
    volume.real (⋃ ν ∈ C, (unitPartition.box n ν : Set (Fin q → ℝ))) =
      (C.card : ℝ) * ((n : ℝ)⁻¹) ^ q := by
  classical
  have hdisj : PairwiseDisjoint (↑C : Set (Fin q → ℤ))
      (fun ν ↦ (unitPartition.box n ν : Set (Fin q → ℝ))) := by
    intro ν hν ν' hν' hne
    exact unitPartition.disjoint.mp hne
  rw [measureReal_biUnion_finset hdisj (fun ν _ ↦ (unitPartition.box n ν).measurableSet_coe)
    (fun ν _ ↦ by
      rw [unitPartition.volume_box]
      exact ENNReal.div_ne_top ENNReal.one_ne_top
        (pow_ne_zero _ (by exact_mod_cast (NeZero.ne n))))]
  simp [measureReal_def, unitPartition.volume_box, one_div, inv_pow]

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
theorem PopulationLocalPressureCore.exists_cell_microscopic_cubes_with_two_mass_controls
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
      (∀ N, volume ((coord '' L) \ (⋃ ν ∈ C N,
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
  refine ⟨C, hdisjoint, ?_, ?_, ?_⟩
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
  · intro N
    exact (le_add_left le_rfl).trans_lt (hsmall N)
  · apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hhole (fun _ ↦ bot_le)
    intro N
    exact le_add_left le_rfl


end OTSelector.Reconstruction
