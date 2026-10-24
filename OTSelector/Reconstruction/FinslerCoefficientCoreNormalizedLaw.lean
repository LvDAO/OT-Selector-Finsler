import OTSelector.Reconstruction.FinslerCoefficientCoreFrozenLaw
import OTSelector.Probability.WeightedMarkNormalization
import OTSelector.Probability.CommonSubmeasureSampling

/-!
# Normalized original laws and common mass on actual Taylor cells

Every estimate uses the same original cell, intensity, and conditional marks.
The raw laws are normalized only after their common null-cell criterion.
-/

open Set MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace OTSelector.Reconstruction

open Function Manifold OTSelector.Geometry
open scoped Topology ContDiff

noncomputable section
set_option backward.isDefEq.respectTransparency false

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

variable (D : PopulationLocalPressureCore P a κ lambda η₀ η₁ ρ₀ ρ₁ v b Good r δ loss)
  (hF : F.IsSmoothStronglyConvex)
  (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
  (hu : let _instFrozenMetric : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
  (ha : Measurable a)
  (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))

include hF hcomplete hu ha hinj

omit hF hcomplete hu ha hinj in
/-- Both original color laws retain their raw masses and admit controlled
normalization and a common probability part on this actual cell. -/
def PopulationLocalPressureCore.FrozenCellNormalizationData
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _instFrozenMetric : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))
    (i : Fin D.haar.continuous.count) (L : Set (ℚ → M)) (hL : MeasurableSet L)
    (hsub : L ⊆ (D.haar.continuous.coefficient i).roots) (z₀ : ℚ → M) (η : ℝ) : Prop :=
    let C := D.haar.continuous.coefficient i
    let S := (P C.seedIndex).seed
    let R := populationSeedRootLabelValue S a
    let μ := (κ C.seedIndex).restrict (R '' L)
    let ρ := populationSeedPieceHaarDensity P a κ lambda C.seedIndex
    let _instCellHaar := D.cell_haar_finite hF hcomplete hu ha hinj i hL hsub
    let _instCellIntensity := D.cell_intensity_finite hF hcomplete hu ha hinj i hL hsub
    ∀ color : Fin 2,
      FiniteLawFreezingBound
        (μ.withDensity ρ ⊗ₘ populationSeedCoordinateClockKernel S a ha
          (populationTwoColorClockKernel u a η₀ η₁ color))
        ((D.rootIntensity i z₀).toNNReal •
          μ.prod (populationTwoColorClockKernel u a η₀ η₁ color z₀)) η

/-- The actual root cell inherits both mass and full variation estimates from
the original intensity and conditional laws. -/
theorem PopulationLocalPressureCore.frozen_cell_normalization_data
    (i : Fin D.haar.continuous.count) {L : Set (ℚ → M)} (hL : MeasurableSet L)
    (hsub : L ⊆ (D.haar.continuous.coefficient i).roots)
    {z₀ : ℚ → M} (hz₀ : z₀ ∈ (D.haar.continuous.coefficient i).roots)
    {η : ℝ} (hη : 0 ≤ η)
    (hclose : ∀ z ∈ L, |D.rootIntensity i z - D.rootIntensity i z₀| ≤
      η * D.rootIntensity i z₀)
    (hmark : ∀ z ∈ L, ∀ color : Fin 2,
      ((populationTwoColorClockKernel u a η₀ η₁ color z).toSignedMeasure -
        (populationTwoColorClockKernel u a η₀ η₁ color z₀).toSignedMeasure).totalVariation
          univ ≤ ENNReal.ofReal η) :
    D.FrozenCellNormalizationData hF hcomplete hu ha hinj i L hL hsub z₀ η := by
  let _instFrozenMetric : MetricSpace M := F.metricSpace
  let _instFrozenProper : ProperSpace M := F.properSpace_of_complete hcomplete
  let _instFrozenPolish : PolishSpace M := inferInstance
  let C := D.haar.continuous.coefficient i
  let S := (P C.seedIndex).seed
  let R := populationSeedRootLabelValue S a
  let μ := (κ C.seedIndex).restrict (R '' L)
  let ρ := populationSeedPieceHaarDensity P a κ lambda C.seedIndex
  let _instCellHaar := D.cell_haar_finite hF hcomplete hu ha hinj i hL hsub
  let _instCellIntensity := D.cell_intensity_finite hF hcomplete hu ha hinj i hL hsub
  intro color
  let k := populationTwoColorClockKernel u a η₀ η₁ color
  let k' := populationSeedCoordinateClockKernel S a ha k
  have hρ : Measurable ρ :=
    measurable_populationSeedPieceHaarDensity P a κ lambda hF hcomplete hu ha hinj C.seedIndex
  have hclose' : ∀ᵐ w ∂μ, |(ρ w).toReal - D.rootIntensity i z₀| ≤
      η * D.rootIntensity i z₀ := by
    have himage : MeasurableSet (R '' L) :=
      D.haar.measurable_cell_label_image hcomplete i hL hsub
    filter_upwards [ae_restrict_mem himage] with w hw
    obtain ⟨z, hz, rfl⟩ := hw
    exact hclose z hz
  refine ⟨weighted_compProd_mass_error μ k' (k z₀) hρ ENNReal.toReal_nonneg hclose', ?_⟩
  have hraw := D.frozen_cell_totalVariation_le hF hcomplete hu ha hinj i hL hsub
    hz₀ hη hclose hmark color
  have hraw' : ((μ.withDensity ρ ⊗ₘ k').toSignedMeasure -
      ((D.rootIntensity i z₀).toNNReal • μ.prod (k z₀)).toSignedMeasure).totalVariation
        univ ≤ ENNReal.ofReal (2 * η * D.rootIntensity i z₀) * μ univ := by
    simpa only [μ, ρ, k', k, C, S, R, Measure.restrict_apply_univ] using hraw
  have hb := ENNReal.toReal_mono
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top μ univ)) hraw'
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by
    exact mul_nonneg (mul_nonneg (by norm_num) hη) ENNReal.toReal_nonneg)] at hb
  have hprod : (μ.prod (k z₀)).real univ = μ.real univ := by
    rw [measureReal_def, ← univ_prod_univ, Measure.prod_prod,
      measure_univ (μ := k z₀), mul_one]
    rfl
  have hρ₀ : 0 ≤ D.rootIntensity i z₀ := ENNReal.toReal_nonneg
  change _ ≤ 2 * η * ((D.rootIntensity i z₀).toNNReal • μ.prod (k z₀)).real univ
  rw [measureReal_nnreal_smul_apply, Real.coe_toNNReal _ hρ₀, hprod]
  simpa only [measureReal_def, mul_assoc] using hb

/-- One finite measurable Taylor partition simultaneously controls the raw mass,
normalized-law variation, and common-part residuals for both original colors. -/
theorem PopulationLocalPressureCore.exists_normalized_frozen_taylor_partition
    (i : Fin D.haar.continuous.count) {ε η : ℝ} (hε : 0 < ε) (hη : 0 < η) :
    ∃ T : (D.haar.continuous.coefficient i).TaylorRootCover ε,
      ∃ Q : FiniteRootNeighborhoodPartition (D.haar.continuous.coefficient i).roots
        T.centers T.neighborhood,
        ∀ j : Fin Q.count, D.FrozenCellNormalizationData hF hcomplete hu ha hinj i
          (Q.cell j) (Q.measurable_cell j) ((Q.cell_subset j).trans inter_subset_left)
          (Q.center j) η := by
  let _instFrozenMetric : MetricSpace M := F.metricSpace
  let _instFrozenProper : ProperSpace M := F.properSpace_of_complete hcomplete
  let _instFrozenPolish : PolishSpace M := inferInstance
  obtain ⟨T, hT⟩ := D.exists_taylorRootCover_with_intensity_and_variation
    hF hcomplete hu ha hinj i hε hη
  obtain ⟨Q⟩ := T.nonempty_partition
  refine ⟨T, Q, fun j ↦ ?_⟩
  apply D.frozen_cell_normalization_data hF hcomplete hu ha hinj i
    (Q.measurable_cell j) ((Q.cell_subset j).trans inter_subset_left)
    (T.subset (Q.center_mem j)) hη.le
  · exact fun z hz ↦ (hT (Q.center j) (Q.center_mem j) z (Q.cell_subset j hz)).1
  · exact fun z hz ↦ (hT (Q.center j) (Q.center_mem j) z (Q.cell_subset j hz)).2

/-- A cell of positive original root mass admits common sampling for each color.
The two marginals are its actual and frozen normalized laws, with no condition
on realized empirical cell counts. -/
theorem PopulationLocalPressureCore.FrozenCellNormalizationData.common_sampling
    (i : Fin D.haar.continuous.count) {L : Set (ℚ → M)} (hL : MeasurableSet L)
    (hsub : L ⊆ (D.haar.continuous.coefficient i).roots) (z₀ : ℚ → M)
    {η : ℝ} (hη : 0 ≤ η) (hη1 : η < 1)
    (hdata : D.FrozenCellNormalizationData hF hcomplete hu ha hinj i L hL hsub z₀ η)
    (hmass : 0 < lambda.real L) :
    let C := D.haar.continuous.coefficient i
    let S := (P C.seedIndex).seed
    let R := populationSeedRootLabelValue S a
    let μ := (κ C.seedIndex).restrict (R '' L)
    let ρ := populationSeedPieceHaarDensity P a κ lambda C.seedIndex
    ∀ color : Fin 2, ∃ π : Measure ((S.covector.ker × ℝ) × (S.covector.ker × ℝ)),
      IsProbabilityMeasure π ∧
      π.map Prod.fst = normalizedFiniteLaw
        (μ.withDensity ρ ⊗ₘ populationSeedCoordinateClockKernel S a ha
          (populationTwoColorClockKernel u a η₀ η₁ color)) ∧
      π.map Prod.snd = normalizedFiniteLaw
        ((D.rootIntensity i z₀).toNNReal •
          μ.prod (populationTwoColorClockKernel u a η₀ η₁ color z₀)) ∧
      π {p | p.1 ≠ p.2} ≤ ENNReal.ofReal (3 * η / (1 - η)) := by
  let _instFrozenMetric : MetricSpace M := F.metricSpace
  let _instFrozenProper : ProperSpace M := F.properSpace_of_complete hcomplete
  let _instFrozenPolish : PolishSpace M := inferInstance
  let C := D.haar.continuous.coefficient i
  let S := (P C.seedIndex).seed
  let R := populationSeedRootLabelValue S a
  let μ := (κ C.seedIndex).restrict (R '' L)
  let ρ := populationSeedPieceHaarDensity P a κ lambda C.seedIndex
  let _instCellHaar := D.cell_haar_finite hF hcomplete hu ha hinj i hL hsub
  let _instCellIntensity := D.cell_intensity_finite hF hcomplete hu ha hinj i hL hsub
  dsimp only
  intro color
  let k := populationTwoColorClockKernel u a η₀ η₁ color
  let α := μ.withDensity ρ ⊗ₘ populationSeedCoordinateClockKernel S a ha k
  let β := (D.rootIntensity i z₀).toNNReal • μ.prod (k z₀)
  have hc : FiniteLawFreezingBound α β η := hdata color
  have hα : 0 < α.real univ := by
    have hm := (D.haar.cell_masses hF hcomplete hu ha hinj i hL hsub).1
    change (μ.withDensity ρ) univ = lambda L at hm
    simpa only [α, measureReal_def, Measure.compProd_apply_univ, hm] using hmass
  have hβ : 0 < β.real univ := by
    by_contra hn
    have hz : β.real univ = 0 := le_antisymm (le_of_not_gt hn) measureReal_nonneg
    have he := hc.mass_error
    rw [hz, sub_zero, mul_zero, abs_of_pos hα] at he
    exact (not_le_of_gt hα) he
  exact hc.exists_normalized_common_sampling hη hη1 hβ

end
end OTSelector.Reconstruction
