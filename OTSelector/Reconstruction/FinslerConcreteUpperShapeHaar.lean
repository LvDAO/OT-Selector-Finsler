import OTSelector.Probability.FinslerAtlasCubeInputs
import OTSelector.Reconstruction.FinslerConcreteUpperShapeAtlas

/-!
Original finite Finsler cell laws are compared with frozen products on full
coordinate cube unions. The reference root, raw intensity and conditional
clock laws are the original ones; shape mismatch remains an explicit original
Haar mass.
-/

open Set Function MeasureTheory ProbabilityTheory Manifold OTSelector.Geometry
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


/-- The actual finite cell-shape producer controls original root loss and Haar
symmetric difference simultaneously. Finiteness of the full cube reference is
proved, so it can be normalized and used in the two-color law comparison. -/
theorem PopulationLocalPressureCore.exists_cell_coordinate_cubes_haar_error
    (D : PopulationLocalPressureCore P a κ lambda η₀ η₁ ρ₀ ρ₁ v b Good r δ loss)
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _instShapeHaarMetric : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))
    (i : Fin D.haar.continuous.count) {L : Set (ℚ → M)} (hL : MeasurableSet L)
    (hsub : L ⊆ (D.haar.continuous.coefficient i).roots)
    {q : ℕ} (e : (P (D.haar.continuous.coefficient i).seedIndex).seed.covector.ker ≃L[ℝ]
      (Fin q → ℝ))
    [(κ (D.haar.continuous.coefficient i).seedIndex).IsAddHaarMeasure]
    {ε : ℝ≥0∞} (hε : 0 < ε) {mesh : ℝ} (hmesh : 0 < mesh) :
    let C := D.haar.continuous.coefficient i
    let S := (P C.seedIndex).seed
    let R := populationSeedRootLabelValue S a
    let coord := OTSelector.Probability.atlasSeedCoord S e a
    ∃ n : ℕ, ∃ hn : NeZero n, ∃ cells : Finset (Fin q → ℤ),
      let cubes := ⋃ ν ∈ cells, ((BoxIntegral.unitPartition.box n ν) : Set (Fin q → ℝ))
      (1 / (n : ℝ) < mesh) ∧
      Set.PairwiseDisjoint (↑cells : Set (Fin q → ℤ))
        (fun ν ↦ ((BoxIntegral.unitPartition.box n ν) : Set (Fin q → ℝ))) ∧
      cubes ⊆ e '' S.openLabels ∧
      lambda (L \ coord ⁻¹' cubes) < ε ∧
      (κ C.seedIndex) ((R '' L) ∆ (e ⁻¹' cubes)) < ε ∧
      IsFiniteMeasure ((κ C.seedIndex).restrict (e ⁻¹' cubes)) := by
  classical
  let C := D.haar.continuous.coefficient i
  let S := (P C.seedIndex).seed
  let R := populationSeedRootLabelValue S a
  let coord := OTSelector.Probability.atlasSeedCoord S e a
  obtain ⟨c, hc0, hctop, hmap⟩ :=
    OTSelector.Probability.map_eq_smul_volume_of_isAddHaarMeasure P κ C.seedIndex e
  let tolerance := min ε (min (ε / c) 1)
  have htolerance : 0 < tolerance := lt_min hε (lt_min (ENNReal.div_pos hε.ne' hctop) zero_lt_one)
  obtain ⟨n, hn, cells, hnm, hdisj, hchart, hmass, hshape⟩ :=
    D.exists_cell_coordinate_cubes hF hcomplete hu ha hinj i hL hsub e htolerance hmesh
  dsimp only
  let cubes := ⋃ ν ∈ cells, ((BoxIntegral.unitPartition.box n ν) : Set (Fin q → ℝ))
  have hcubes : MeasurableSet cubes := MeasurableSet.iUnion fun ν ↦
    MeasurableSet.iUnion fun _ ↦ (BoxIntegral.unitPartition.box n ν).measurableSet_coe
  have himage : MeasurableSet (coord '' L) := by
    have hR := D.haar.measurable_cell_label_image hcomplete i hL hsub
    have h := e.toHomeomorph.measurableEmbedding.measurableSet_image.mpr hR
    change MeasurableSet (e '' (R '' L)) at h
    change MeasurableSet ((fun z ↦ e (R z)) '' L)
    simpa only [image_image] using h
  have himageEq : coord '' L = e '' (R '' L) := (image_image e R L).symm
  have hpre : e ⁻¹' (cubes ∆ (coord '' L)) = (R '' L) ∆ (e ⁻¹' cubes) := by
    rw [preimage_symmDiff, himageEq, e.injective.preimage_image]
    exact symmDiff_comm _ _
  have hhaar : (κ C.seedIndex) ((R '' L) ∆ (e ⁻¹' cubes)) =
      c * volume (cubes ∆ (coord '' L)) := by
    rw [← hpre, ← Measure.map_apply e.continuous.measurable (hcubes.symmDiff himage),
      hmap, Measure.smul_apply, smul_eq_mul]
  have hsmallHaar : (κ C.seedIndex) ((R '' L) ∆ (e ⁻¹' cubes)) < ε := by
    rw [hhaar]
    calc
      c * volume (cubes ∆ (coord '' L)) < c * (ε / c) := by
        simpa only [mul_comm] using ENNReal.mul_lt_mul_left hc0 hctop
          (hshape.trans_le ((min_le_right _ _).trans (min_le_left _ _)))
      _ = ε := ENNReal.mul_div_cancel hc0 hctop
  have hfinite : IsFiniteMeasure ((κ C.seedIndex).restrict (e ⁻¹' cubes)) := by
    have hsm : (κ C.seedIndex) (R '' L) ≠ (∞ : ℝ≥0∞) := by
      haveI := D.cell_haar_finite hF hcomplete hu ha hinj i hL hsub
      simpa only [Measure.restrict_apply_univ] using
        (measure_ne_top ((κ C.seedIndex).restrict (R '' L)) univ)
    have hvolume : volume (cubes ∆ (coord '' L)) ≠ (∞ : ℝ≥0∞) :=
      ne_top_of_lt ((hshape.trans_le ((min_le_right _ _).trans (min_le_right _ _))).trans
        ENNReal.one_lt_top)
    have hdiff : (κ C.seedIndex) ((R '' L) ∆ (e ⁻¹' cubes)) ≠ (∞ : ℝ≥0∞) := by
      rw [hhaar]
      exact ENNReal.mul_ne_top hctop hvolume
    have hsubC : e ⁻¹' cubes ⊆ (R '' L) ∪ ((R '' L) ∆ (e ⁻¹' cubes)) := by
      intro x hx
      by_cases hs : x ∈ R '' L
      · exact Or.inl hs
      · exact Or.inr (Or.inr ⟨hx, hs⟩)
    constructor
    rw [Measure.restrict_apply_univ]
    exact ((measure_mono hsubC).trans (measure_union_le _ _)).trans_lt
      (ENNReal.add_lt_top.mpr ⟨hsm.lt_top, hdiff.lt_top⟩)

  exact ⟨n, hn, cells, hnm, hdisj, hchart, hmass.trans_le (min_le_left _ _), hsmallHaar, hfinite⟩

end OTSelector.Reconstruction
