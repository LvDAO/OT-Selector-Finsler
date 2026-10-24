import OTSelector.MeasureTheory.FineCubeApproximation
import OTSelector.Reconstruction.FinslerCoefficientCoreFrozenLaw
import OTSelector.Probability.FinslerAtlasCoordinateLaw

/-!
Actual original population pressure cells admit finite disjoint equal
coordinate-cube approximations. The original root measure and conditional
clock laws are retained on the inverse images of the cubes. The added frozen
Lebesgue mass and discarded original root mass are both explicitly small.
-/

open Set Function MeasureTheory ProbabilityTheory Manifold OTSelector.Geometry BoxIntegral
open scoped Topology ContDiff ENNReal symmDiff

noncomputable section
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

namespace OTSelector.Reconstruction

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

/-- A literal measurable cell of the original Finsler pressure core can be
approximated by finitely many disjoint equal coordinate cubes. They remain
inside the actual seed's open label chart. Both the original root-mass loss
and the Lebesgue shape error are small; no cube-shape assumption is an input. -/
theorem PopulationLocalPressureCore.exists_cell_coordinate_cubes
    (D : PopulationLocalPressureCore P a κ lambda η₀ η₁ ρ₀ ρ₁ v b Good r δ loss)
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _instShapeAtlasMetric : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))
    (i : Fin D.haar.continuous.count) {L : Set (ℚ → M)} (hL : MeasurableSet L)
    (hsub : L ⊆ (D.haar.continuous.coefficient i).roots)
    {q : ℕ} (e : (P (D.haar.continuous.coefficient i).seedIndex).seed.covector.ker ≃L[ℝ]
      (Fin q → ℝ)) {ε : ℝ≥0∞} (hε : 0 < ε) {mesh : ℝ} (hmesh : 0 < mesh) :
    let S := (P (D.haar.continuous.coefficient i).seedIndex).seed
    let coord := OTSelector.Probability.atlasSeedCoord S e a
    ∃ n : ℕ, ∃ hn : NeZero n, ∃ C : Finset (Fin q → ℤ),
      (1 / (n : ℝ) < mesh) ∧
      Set.PairwiseDisjoint (↑C : Set (Fin q → ℤ))
        (fun ν ↦ ((unitPartition.box n ν) : Set (Fin q → ℝ))) ∧
      (⋃ ν ∈ C, ((unitPartition.box n ν) : Set (Fin q → ℝ))) ⊆ e '' S.openLabels ∧
      lambda (L \ coord ⁻¹' (⋃ ν ∈ C,
        ((unitPartition.box n ν) : Set (Fin q → ℝ)))) < ε ∧
      volume ((⋃ ν ∈ C, ((unitPartition.box n ν) : Set (Fin q → ℝ))) ∆
        (coord '' L)) < ε := by
  classical
  letI : MetricSpace M := F.metricSpace
  letI : ProperSpace M := F.properSpace_of_complete hcomplete
  letI : PolishSpace M := inferInstance
  letI : BorelSpace (ℚ → M) := inferInstance
  let S := (P (D.haar.continuous.coefficient i).seedIndex).seed
  let R := populationSeedRootLabelValue S a
  let coord := OTSelector.Probability.atlasSeedCoord S e a
  have hcoord : Measurable coord :=
    OTSelector.Probability.measurable_atlasSeedCoord S hF hcomplete hu ha hinj e
  have hsubI : L ⊆ (D.haar.intensity i).roots := by rwa [D.haar.intensity_roots]
  have himage : MeasurableSet (coord '' L) := by
    have hR := D.haar.measurable_cell_label_image hcomplete i hL hsub
    have h := e.toHomeomorph.measurableEmbedding.measurableSet_image.mpr hR
    change MeasurableSet (e '' (R '' L)) at h
    change MeasurableSet ((fun z ↦ e (R z)) '' L)
    simpa only [image_image] using h
  have hcompact : IsCompact (e '' (R '' (D.haar.intensity i).roots)) :=
    (D.haar.intensity i).compact_labels.image e.continuous
  obtain ⟨radius, hradius⟩ := hcompact.isBounded.subset_ball 0
  let V := (e '' S.openLabels) ∩ Metric.ball 0 radius
  have hV : IsOpen V := (e.toHomeomorph.isOpenMap S.openLabels S.openLabels_open).inter
    Metric.isOpen_ball
  have hsV : coord '' L ⊆ V := by
    rintro _ ⟨z, hz, rfl⟩
    have hlabel : R z ∈ S.labels := (D.haar.intensity i).labels_subset
      (mem_image_of_mem R (hsubI hz))
    exact ⟨⟨R z, S.labels_subset hlabel, rfl⟩,
      hradius (mem_image_of_mem e (mem_image_of_mem R (hsubI hz)))⟩
  have hvol : (volume : Measure (Fin q → ℝ)) V < (∞ : ℝ≥0∞) := (Metric.isBounded_ball.subset inter_subset_right).measure_lt_top
  let μ : Measure (Fin q → ℝ) := (lambda.restrict L).map coord
  obtain ⟨n, hn, C, hnm, hdisj, hCV, hmass, hshape⟩ :=
    exists_grid_cubes_approx_original_and_volume μ himage hV hsV hvol hε hmesh
  refine ⟨n, hn, C, hnm, hdisj, hCV.trans inter_subset_left, ?_, hshape⟩
  let cubes : Set (Fin q → ℝ) := ⋃ ν ∈ C, ((unitPartition.box n ν) : Set (Fin q → ℝ))
  have hcubes : MeasurableSet cubes := MeasurableSet.iUnion fun ν ↦
    MeasurableSet.iUnion fun _ ↦ (unitPartition.box n ν).measurableSet_coe
  have heq : coord ⁻¹' (cubes ∆ (coord '' L)) ∩ L = L \ coord ⁻¹' cubes := by
    ext z
    constructor
    · intro hz
      rcases hz.1 with hz' | hz'
      · exact False.elim (hz'.2 (mem_image_of_mem coord hz.2))
      · exact ⟨hz.2, hz'.2⟩
    · intro hz
      exact ⟨Or.inr ⟨mem_image_of_mem coord hz.1, hz.2⟩, hz.1⟩
  rw [show μ (cubes ∆ (coord '' L)) =
      (lambda.restrict L).map coord (cubes ∆ (coord '' L)) from rfl,
    Measure.map_apply hcoord (hcubes.symmDiff himage),
    Measure.restrict_apply (hcoord (hcubes.symmDiff himage)), heq] at hmass
  exact hmass

end OTSelector.Reconstruction
