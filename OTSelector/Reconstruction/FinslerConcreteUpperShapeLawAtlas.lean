import OTSelector.MeasureTheory.NormalizedCellShapeVariation
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

/-- Replace the retained original label shape by a full cube union in the
actual frozen-cell law. The two-color law estimate comes from the original
Taylor freezing data and pays only the original Haar shape mismatch. -/
theorem PopulationLocalPressureCore.frozen_cell_cubeShape_variation_le
    (D : PopulationLocalPressureCore P a κ lambda η₀ η₁ ρ₀ ρ₁ v b Good r δ loss)
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _instShapeLawMetric : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))
    (i : Fin D.haar.continuous.count) {L : Set (ℚ → M)} (hL : MeasurableSet L)
    (hsub : L ⊆ (D.haar.continuous.coefficient i).roots)
    (z₀ : ℚ → M) (tolerance : ℝ)
    (hcell : D.FrozenCellVariationBound hF hcomplete hu ha hinj i L hL hsub z₀ tolerance)
    (cubes : Set (P (D.haar.continuous.coefficient i).seedIndex).seed.covector.ker)
    (hcubes : MeasurableSet cubes)
    [IsFiniteMeasure ((κ (D.haar.continuous.coefficient i).seedIndex).restrict cubes)] :
    let C := D.haar.continuous.coefficient i
    let S := (P C.seedIndex).seed
    let R := populationSeedRootLabelValue S a
    let μ := (κ C.seedIndex).restrict (R '' L)
    let ρ := populationSeedPieceHaarDensity P a κ lambda C.seedIndex
    let _instCellHaar := D.cell_haar_finite hF hcomplete hu ha hinj i hL hsub
    let _instCellIntensity := D.cell_intensity_finite hF hcomplete hu ha hinj i hL hsub
    ∀ color : Fin 2,
      ((μ.withDensity ρ ⊗ₘ populationSeedCoordinateClockKernel S a ha
          (populationTwoColorClockKernel u a η₀ η₁ color)).toSignedMeasure -
        ((D.rootIntensity i z₀).toNNReal •
          ((κ C.seedIndex).restrict cubes).prod
            (populationTwoColorClockKernel u a η₀ η₁ color z₀)).toSignedMeasure).totalVariation
          univ ≤
        ENNReal.ofReal (2 * tolerance * D.rootIntensity i z₀) * (κ C.seedIndex) (R '' L) +
          ENNReal.ofReal (D.rootIntensity i z₀) * (κ C.seedIndex) ((R '' L) ∆ cubes) := by
  let C := D.haar.continuous.coefficient i
  let S := (P C.seedIndex).seed
  let R := populationSeedRootLabelValue S a
  let μ := (κ C.seedIndex).restrict (R '' L)
  let ρ := populationSeedPieceHaarDensity P a κ lambda C.seedIndex
  haveI := D.cell_haar_finite hF hcomplete hu ha hinj i hL hsub
  haveI := D.cell_intensity_finite hF hcomplete hu ha hinj i hL hsub
  dsimp only
  intro color
  let clock := populationSeedCoordinateClockKernel S a ha
    (populationTwoColorClockKernel u a η₀ η₁ color)
  let ν := populationTwoColorClockKernel u a η₀ η₁ color z₀
  let actual := μ.withDensity ρ ⊗ₘ clock
  let frozenCell := (D.rootIntensity i z₀).toNNReal • μ.prod ν
  let frozenCubes := (D.rootIntensity i z₀).toNNReal • ((κ C.seedIndex).restrict cubes).prod ν
  have hraw : (actual.toSignedMeasure - frozenCell.toSignedMeasure).totalVariation univ ≤
      ENNReal.ofReal (2 * tolerance * D.rootIntensity i z₀) * (κ C.seedIndex) (R '' L) :=
    hcell color
  have hdensity : 0 ≤ D.rootIntensity i z₀ := ENNReal.toReal_nonneg
  have hshape := totalVariation_frozen_product_shape_eq (κ C.seedIndex) ν
    (D.haar.measurable_cell_label_image hcomplete i hL hsub) hcubes
    (D.rootIntensity i z₀).toNNReal
  change (frozenCell.toSignedMeasure - frozenCubes.toSignedMeasure).totalVariation univ =
    ((D.rootIntensity i z₀).toNNReal : ℝ≥0∞) * (κ C.seedIndex) ((R '' L) ∆ cubes) at hshape
  have hsplit : actual.toSignedMeasure - frozenCubes.toSignedMeasure =
      (actual.toSignedMeasure - frozenCell.toSignedMeasure) +
        (frozenCell.toSignedMeasure - frozenCubes.toSignedMeasure) := by abel
  change (actual.toSignedMeasure - frozenCubes.toSignedMeasure).totalVariation univ ≤ _
  rw [hsplit]
  have htriangle := VectorMeasure.variation_add_le (μ :=
    actual.toSignedMeasure - frozenCell.toSignedMeasure)
    (ν := frozenCell.toSignedMeasure - frozenCubes.toSignedMeasure) univ
  simp only [← SignedMeasure.totalVariation_eq_variation] at htriangle
  have hshapeBound := hshape.le
  rw [ENNReal.coe_nnreal_eq, Real.coe_toNNReal _ hdensity] at hshapeBound
  exact htriangle.trans (add_le_add hraw hshapeBound)


/-- Normalizing the original two-color cell law against a full cube reference
retains its actual population mass in the denominator. The density and mark
oscillation on the retained cell and its Haar shape error remain separate. -/
theorem PopulationLocalPressureCore.normalized_cell_cubeShape_variation_le
    (D : PopulationLocalPressureCore P a κ lambda η₀ η₁ ρ₀ ρ₁ v b Good r δ loss)
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _instShapeLawMetric : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))
    (i : Fin D.haar.continuous.count) {L : Set (ℚ → M)} (hL : MeasurableSet L)
    (hsub : L ⊆ (D.haar.continuous.coefficient i).roots)
    (z₀ : ℚ → M) {tolerance : ℝ} (htolerance : 0 ≤ tolerance)
    (hcell : D.FrozenCellVariationBound hF hcomplete hu ha hinj i L hL hsub z₀ tolerance)
    (cubes : Set (P (D.haar.continuous.coefficient i).seedIndex).seed.covector.ker)
    (hcubes : MeasurableSet cubes)
    [IsFiniteMeasure ((κ (D.haar.continuous.coefficient i).seedIndex).restrict cubes)]
    (hLmass : 0 < lambda.real L)
    (hfrozenmass : 0 < D.rootIntensity i z₀ *
      (κ (D.haar.continuous.coefficient i).seedIndex).real cubes) :
    let C := D.haar.continuous.coefficient i
    let S := (P C.seedIndex).seed
    let R := populationSeedRootLabelValue S a
    let μ := (κ C.seedIndex).restrict (R '' L)
    let ρ := populationSeedPieceHaarDensity P a κ lambda C.seedIndex
    let _instCellHaar := D.cell_haar_finite hF hcomplete hu ha hinj i hL hsub
    let _instCellIntensity := D.cell_intensity_finite hF hcomplete hu ha hinj i hL hsub
    ∀ color : Fin 2,
      (((normalizedFiniteLaw (μ.withDensity ρ ⊗ₘ populationSeedCoordinateClockKernel S a ha
          (populationTwoColorClockKernel u a η₀ η₁ color))).toSignedMeasure -
        (normalizedFiniteLaw ((D.rootIntensity i z₀).toNNReal •
          ((κ C.seedIndex).restrict cubes).prod
            (populationTwoColorClockKernel u a η₀ η₁ color z₀))).toSignedMeasure).totalVariation.real univ) ≤
        2 * (2 * tolerance * D.rootIntensity i z₀ * (κ C.seedIndex).real (R '' L) +
          D.rootIntensity i z₀ * (κ C.seedIndex).real ((R '' L) ∆ cubes)) / lambda.real L := by
  let C := D.haar.continuous.coefficient i
  let S := (P C.seedIndex).seed
  let R := populationSeedRootLabelValue S a
  let μ := (κ C.seedIndex).restrict (R '' L)
  let ρ := populationSeedPieceHaarDensity P a κ lambda C.seedIndex
  haveI := D.cell_haar_finite hF hcomplete hu ha hinj i hL hsub
  haveI := D.cell_intensity_finite hF hcomplete hu ha hinj i hL hsub
  dsimp only
  intro color
  let clock := populationSeedCoordinateClockKernel S a ha
    (populationTwoColorClockKernel u a η₀ η₁ color)
  let ν := populationTwoColorClockKernel u a η₀ η₁ color z₀
  let actual := μ.withDensity ρ ⊗ₘ clock
  let frozenCubes := (D.rootIntensity i z₀).toNNReal • ((κ C.seedIndex).restrict cubes).prod ν
  have hdensity : 0 ≤ D.rootIntensity i z₀ := ENNReal.toReal_nonneg
  have hactualmass : actual.real univ = lambda.real L := by
    dsimp only [actual, measureReal_def]
    rw [Measure.compProd_apply_univ,
      (D.haar.cell_masses hF hcomplete hu ha hinj i hL hsub).1]
  have hfrozenmass' : frozenCubes.real univ =
      D.rootIntensity i z₀ * (κ C.seedIndex).real cubes := by
    rw [show frozenCubes = (D.rootIntensity i z₀).toNNReal •
      ((κ C.seedIndex).restrict cubes).prod ν from rfl,
      measureReal_nnreal_smul_apply, Real.coe_toNNReal _ hdensity]
    congr 1
    dsimp only [measureReal_def]
    have hprod := Measure.prod_prod (μ := (κ C.seedIndex).restrict cubes) (ν := ν) univ univ
    simpa only [univ_prod_univ, measure_univ, mul_one, Measure.restrict_apply_univ] using
      congrArg ENNReal.toReal hprod
  have hraw := D.frozen_cell_cubeShape_variation_le hF hcomplete hu ha hinj i hL hsub
    z₀ tolerance hcell cubes hcubes color
  have hsm : (κ C.seedIndex) (R '' L) ≠ (∞ : ℝ≥0∞) := by
    simpa only [μ, Measure.restrict_apply_univ] using (measure_ne_top μ univ)
  have hCm : (κ C.seedIndex) cubes ≠ (∞ : ℝ≥0∞) := by
    simpa only [Measure.restrict_apply_univ] using
      (measure_ne_top ((κ C.seedIndex).restrict cubes) univ)
  have hdiff : (κ C.seedIndex) ((R '' L) ∆ cubes) ≠ (∞ : ℝ≥0∞) := ne_top_of_le_ne_top
    (ENNReal.add_ne_top.mpr ⟨hsm, hCm⟩)
    ((measure_mono Set.symmDiff_subset_union).trans (measure_union_le _ _))
  have htop₁ : ENNReal.ofReal (2 * tolerance * D.rootIntensity i z₀) *
      (κ C.seedIndex) (R '' L) ≠ (∞ : ℝ≥0∞) := ENNReal.mul_ne_top ENNReal.ofReal_ne_top hsm
  have htop₂ : ENNReal.ofReal (D.rootIntensity i z₀) *
      (κ C.seedIndex) ((R '' L) ∆ cubes) ≠ (∞ : ℝ≥0∞) := ENNReal.mul_ne_top ENNReal.ofReal_ne_top hdiff
  have hrawR := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨htop₁, htop₂⟩) hraw
  simp only [ENNReal.toReal_add htop₁ htop₂, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal hdensity,
    ENNReal.toReal_ofReal (show 0 ≤ 2 * tolerance * D.rootIntensity i z₀ by positivity)] at hrawR
  have hnorm := totalVariation_normalized_le_twice_raw actual frozenCubes
    (hactualmass.symm ▸ hLmass) (hfrozenmass'.symm ▸ hfrozenmass)
  rw [hactualmass] at hnorm
  exact hnorm.trans (div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left hrawR (by norm_num)) hLmass.le)

end OTSelector.Reconstruction
