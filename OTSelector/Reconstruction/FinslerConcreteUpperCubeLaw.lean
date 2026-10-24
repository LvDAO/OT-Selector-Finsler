import OTSelector.Reconstruction.FinslerConcreteUpperShapeLawAtlas
import OTSelector.Reconstruction.FinslerConcreteUpperShapeHaar

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


/-- Positive original cells admit frozen full-cube probability references with
an explicit law discrepancy. The reference mass is proved positive from the
original population mass, not added as an input. -/
theorem PopulationLocalPressureCore.exists_normalized_original_cell_cube_laws
    (D : PopulationLocalPressureCore P a κ lambda η₀ η₁ ρ₀ ρ₁ v b Good r δ loss)
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _instCubeLawMetric : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))
    (i : Fin D.haar.continuous.count) {L : Set (ℚ → M)} (hL : MeasurableSet L)
    (hsub : L ⊆ (D.haar.continuous.coefficient i).roots)
    (z₀ : ℚ → M) (hz₀ : z₀ ∈ (D.haar.continuous.coefficient i).roots)
    {tolerance : ℝ} (htolerance : 0 ≤ tolerance)
    (hcell : D.FrozenCellVariationBound hF hcomplete hu ha hinj i L hL hsub z₀ tolerance)
    (hLmass : 0 < lambda.real L)
    {q : ℕ} (e : (P (D.haar.continuous.coefficient i).seedIndex).seed.covector.ker ≃L[ℝ]
      (Fin q → ℝ))
    [(κ (D.haar.continuous.coefficient i).seedIndex).IsAddHaarMeasure]
    {error mesh : ℝ} (herror : 0 < error) (hmesh : 0 < mesh) :
    let C := D.haar.continuous.coefficient i
    let S := (P C.seedIndex).seed
    let R := populationSeedRootLabelValue S a
    let coord := OTSelector.Probability.atlasSeedCoord S e a
    let μ := (κ C.seedIndex).restrict (R '' L)
    let ρ := populationSeedPieceHaarDensity P a κ lambda C.seedIndex
    let _instCellHaar := D.cell_haar_finite hF hcomplete hu ha hinj i hL hsub
    let _instCellIntensity := D.cell_intensity_finite hF hcomplete hu ha hinj i hL hsub
    ∃ n : ℕ, ∃ hn : NeZero n, ∃ cells : Finset (Fin q → ℤ),
      let cubes := ⋃ ν ∈ cells, ((BoxIntegral.unitPartition.box n ν) : Set (Fin q → ℝ))
      ∃ hfinite : IsFiniteMeasure ((κ C.seedIndex).restrict (e ⁻¹' cubes)),
      let _instRefHaar := hfinite
      (1 / (n : ℝ) < mesh) ∧
      Set.PairwiseDisjoint (↑cells : Set (Fin q → ℤ))
        (fun ν ↦ ((BoxIntegral.unitPartition.box n ν) : Set (Fin q → ℝ))) ∧
      cubes ⊆ e '' S.openLabels ∧
      lambda (L \ coord ⁻¹' cubes) < ENNReal.ofReal error ∧
      (∀ color : Fin 2,
        IsProbabilityMeasure (normalizedFiniteLaw (μ.withDensity ρ ⊗ₘ
          populationSeedCoordinateClockKernel S a ha
            (populationTwoColorClockKernel u a η₀ η₁ color))) ∧
        IsProbabilityMeasure (normalizedFiniteLaw ((D.rootIntensity i z₀).toNNReal •
          ((κ C.seedIndex).restrict (e ⁻¹' cubes)).prod
            (populationTwoColorClockKernel u a η₀ η₁ color z₀))) ∧
        (((normalizedFiniteLaw (μ.withDensity ρ ⊗ₘ populationSeedCoordinateClockKernel S a ha
            (populationTwoColorClockKernel u a η₀ η₁ color))).toSignedMeasure -
          (normalizedFiniteLaw ((D.rootIntensity i z₀).toNNReal •
            ((κ C.seedIndex).restrict (e ⁻¹' cubes)).prod
              (populationTwoColorClockKernel u a η₀ η₁ color z₀))).toSignedMeasure).totalVariation.real
            univ) ≤
          2 * (2 * tolerance * D.rootIntensity i z₀ * (κ C.seedIndex).real (R '' L) +
            D.rootIntensity i z₀ * error) / lambda.real L) := by
  classical
  let C := D.haar.continuous.coefficient i
  let S := (P C.seedIndex).seed
  let R := populationSeedRootLabelValue S a
  let μ := (κ C.seedIndex).restrict (R '' L)
  let ρ := populationSeedPieceHaarDensity P a κ lambda C.seedIndex
  haveI := D.cell_haar_finite hF hcomplete hu ha hinj i hL hsub
  haveI := D.cell_intensity_finite hF hcomplete hu ha hinj i hL hsub
  have hsm : (κ C.seedIndex) (R '' L) ≠ (∞ : ℝ≥0∞) := by
    simpa only [μ, Measure.restrict_apply_univ] using (measure_ne_top μ univ)
  have hsm0 : (κ C.seedIndex) (R '' L) ≠ 0 := by
    intro hzero
    have hμzero : μ = 0 := Measure.restrict_eq_zero.mpr hzero
    have hmass := (D.haar.cell_masses hF hcomplete hu ha hinj i hL hsub).1
    change (μ.withDensity ρ) univ = lambda L at hmass
    rw [hμzero] at hmass
    simp only [withDensity_zero_left] at hmass
    change (0 : ℝ≥0∞) = lambda L at hmass
    have h := congrArg ENNReal.toReal hmass
    have h' : (0 : ℝ) = lambda.real L := by simpa only [measureReal_def, ENNReal.toReal_zero] using h
    linarith
  let shapeError := min (ENNReal.ofReal error) ((κ C.seedIndex) (R '' L))
  have hshapeError : 0 < shapeError := lt_min (ENNReal.ofReal_pos.mpr herror)
    (pos_iff_ne_zero.mpr hsm0)
  obtain ⟨n, hn, cells, hnm, hdisj, hchart, hloss, hshape, hfinite⟩ :=
    D.exists_cell_coordinate_cubes_haar_error hF hcomplete hu ha hinj i hL hsub e hshapeError hmesh
  let cubes := ⋃ ν ∈ cells, ((BoxIntegral.unitPartition.box n ν) : Set (Fin q → ℝ))
  let cubeLabels := e ⁻¹' cubes
  haveI := hfinite
  have hcubes : MeasurableSet cubes := MeasurableSet.iUnion fun ν ↦
    MeasurableSet.iUnion fun _ ↦ (BoxIntegral.unitPartition.box n ν).measurableSet_coe
  have hcubeLabels : MeasurableSet cubeLabels := hcubes.preimage e.continuous.measurable
  have hC0 : (κ C.seedIndex) cubeLabels ≠ 0 := by
    intro hzero
    have hsubshape : R '' L ⊆ cubeLabels ∪ ((R '' L) ∆ cubeLabels) := by
      intro x hx
      by_cases hxc : x ∈ cubeLabels
      · exact Or.inl hxc
      · exact Or.inr (Or.inl ⟨hx, hxc⟩)
    have hle := (measure_mono (μ := κ C.seedIndex) hsubshape).trans
      (measure_union_le cubeLabels ((R '' L) ∆ cubeLabels))
    rw [hzero, zero_add] at hle
    exact (not_lt_of_ge hle) (hshape.trans_le (min_le_right _ _))
  have hreferencePositive : 0 < D.rootIntensity i z₀ := by
    have hzI : z₀ ∈ (D.haar.intensity i).roots := by rwa [D.haar.intensity_roots]
    have hlow := ((D.haar.intensity i).bounds (R z₀) (mem_image_of_mem R hzI)).1
    exact (D.haar.intensity i).lower_pos.trans_le hlow
  have hCpos : 0 < (κ C.seedIndex).real cubeLabels := ENNReal.toReal_pos hC0 (by
    simpa only [Measure.restrict_apply_univ] using
      (measure_ne_top ((κ C.seedIndex).restrict cubeLabels) univ))
  have hFpos : 0 < D.rootIntensity i z₀ * (κ C.seedIndex).real cubeLabels :=
    mul_pos hreferencePositive hCpos
  have hshapeR : (κ C.seedIndex).real ((R '' L) ∆ cubeLabels) ≤ error := by
    have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top
      (hshape.trans_le (min_le_left _ _)).le
    simpa only [measureReal_def, C, S, R, cubeLabels, cubes,
      ENNReal.toReal_ofReal herror.le] using h
  dsimp only
  refine ⟨n, hn, cells, hfinite, hnm, hdisj, hchart,
    hloss.trans_le (min_le_left _ _), fun color ↦ ?_⟩
  let clock := populationSeedCoordinateClockKernel S a ha
    (populationTwoColorClockKernel u a η₀ η₁ color)
  let ν := populationTwoColorClockKernel u a η₀ η₁ color z₀
  let actual := μ.withDensity ρ ⊗ₘ clock
  let frozen := (D.rootIntensity i z₀).toNNReal • ((κ C.seedIndex).restrict cubeLabels).prod ν
  have hactualMass : actual.real univ = lambda.real L := by
    dsimp only [actual, measureReal_def]
    rw [Measure.compProd_apply_univ,
      (D.haar.cell_masses hF hcomplete hu ha hinj i hL hsub).1]
  have hfrozenMass : frozen.real univ = D.rootIntensity i z₀ * (κ C.seedIndex).real cubeLabels := by
    rw [show frozen = (D.rootIntensity i z₀).toNNReal •
      ((κ C.seedIndex).restrict cubeLabels).prod ν from rfl,
      measureReal_nnreal_smul_apply, Real.coe_toNNReal _ hreferencePositive.le]
    congr 1
    have hprod := Measure.prod_prod (μ := (κ C.seedIndex).restrict cubeLabels) (ν := ν) univ univ
    simpa only [measureReal_def, univ_prod_univ, measure_univ, mul_one, Measure.restrict_apply_univ] using
      congrArg ENNReal.toReal hprod
  refine ⟨normalizedFiniteLaw_probability actual (hactualMass.symm ▸ hLmass),
    normalizedFiniteLaw_probability frozen (hfrozenMass.symm ▸ hFpos), ?_⟩
  have hnorm := D.normalized_cell_cubeShape_variation_le hF hcomplete hu ha hinj i hL hsub
    z₀ htolerance hcell cubeLabels hcubeLabels hLmass hFpos color
  refine hnorm.trans (div_le_div_of_nonneg_right ?_ hLmass.le)
  gcongr

end OTSelector.Reconstruction
