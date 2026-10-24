import OTSelector.MeasureTheory.Lp.RandomCellAverage
import OTSelector.Probability.StationaryHyperplaneInvariantProjection
import OTSelector.Probability.StationaryWeightedAverage

/-!
Conditions: A probability-preserving measurable spatial action, an original L2 observable and finite-dimensional parameter map L; the mean-limit statements additionally retain the explicit strong continuity along L and zero invariant projection hypotheses.

Objects: Actual scalar scene-field representatives, their true second moments and finite-cell integral/L2 Bochner identities, with vanishing averaged second moment under arbitrary scale-dependent offsets.

Proof detail: Use stationarity to identify every scalar section second moment with the original L2 norm, apply Fubini/Bochner section integration and then invoke the already proved weighted face mean-ergodic result for the indicator of the finite cell.

References: Rick Durrett: Section 1.7, Theorem 1.7.2, p. 38; Sheldon Axler: Section 8B, Definition 8.34, p. 227; Theorem 8.37 and proof, p. 228.
Relation: A scalar realization/integration adapter for a genuine Hilbert-space weighted mean theorem. The continuous weighted multi-parameter face limit is a local derived result, not a verbatim discrete stationary-sequence theorem or a mixing assumption.
-/

/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Reconstruction.OriginalStationaryScalarFaceCell.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Reconstruction.OriginalStationaryScalarFaceCell`; the selected original proof blocks follow. -/
section

/-! Actual scene realizations of stationary face cells and their vanishing second moments. -/
open Set Function Filter MeasureTheory
open scoped ENNReal BigOperators InnerProductSpace Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OTSelector.Reconstruction
open OTSelector.Probability

variable {ι G Ω : Type*} [Fintype ι]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [MeasurableSpace G] [BorelSpace G]
  [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
  (T : G → Ω → Ω) (hT : ∀ a, MeasurePreserving (T a) μ μ)
  (hzero : T 0 = id) (haddT : ∀ a b ω, T a (T b ω) = T (a+b) ω)
  (L : (ι → ℝ) →ₗ[ℝ] G)

/-- The scalar field is the chosen original L2 observable of the literal
translated scene, with arbitrary scale-dependent physical offset. -/
def stationaryScalarFaceReadout (offset : ℝ → G) (x : Lp ℝ 2 μ)
    (R : ℝ) (y : ι → ℝ) (ω : Ω) : ℝ :=
  x (T (offset R + L (R • y)) ω)

omit [IsProbabilityMeasure μ] in
/-- Each real scale has a jointly measurable actual scene/face realization. -/
theorem measurable_stationaryScalarFaceReadout
    (hTjoint : Measurable (fun p : G × Ω ↦ T p.1 p.2))
    (offset : ℝ → G) (x : Lp ℝ 2 μ) (R : ℝ) :
    Measurable (Function.uncurry (stationaryScalarFaceReadout μ T L offset x R)) := by
  have harg : Measurable (fun p : (ι → ℝ) × Ω ↦ (offset R + L (R • p.1), p.2)) := by
    have hc : Continuous (fun y : ι → ℝ ↦ offset R + L (R • y)) :=
      continuous_const.add (L.continuous_of_finiteDimensional.comp
        (show Continuous (fun y : ι → ℝ ↦ R • y) by fun_prop))
    exact (hc.measurable.comp measurable_fst).prodMk measurable_snd
  exact (Lp.stronglyMeasurable x).measurable.comp (hTjoint.comp harg)

omit [Fintype ι] [MeasurableSpace G] [BorelSpace G]
  [IsProbabilityMeasure μ] in
/-- The literal translated scalar field represents the actual Koopman orbit
at every fixed face point, under the same original probability law. -/
theorem stationaryScalarFaceReadout_ae_eq_koopman
    (offset : ℝ → G) (x : Lp ℝ 2 μ) (R : ℝ) (y : ι → ℝ) :
    stationaryScalarFaceReadout μ T L offset x R y =ᵐ[μ]
      (stationaryKoopman μ T hT hzero haddT (offset R + L (R • y)) x : Ω → ℝ) :=
  (Lp.coeFn_compMeasurePreserving x (hT (offset R + L (R • y)))).symm

include hT hzero haddT

omit [Fintype ι] [MeasurableSpace G] [BorelSpace G]
  [IsProbabilityMeasure μ] in
/-- Every literal stationary face sample retains exactly the original second moment. -/
theorem integral_sq_stationaryScalarFaceReadout
    (offset : ℝ → G) (x : Lp ℝ 2 μ) (R : ℝ) (y : ι → ℝ) :
    (∫ ω, (stationaryScalarFaceReadout μ T L offset x R y ω)^2 ∂μ) = ‖x‖^2 := by
  calc
    _ = ∫ ω, ((stationaryKoopman μ T hT hzero haddT (offset R + L (R • y)) x) ω)^2 ∂μ :=
      integral_congr_ae ((stationaryScalarFaceReadout_ae_eq_koopman μ T hT hzero haddT L offset x R y).fun_comp
        (fun r : ℝ ↦ r^2))
    _ = ‖stationaryKoopman μ T hT hzero haddT (offset R + L (R • y)) x‖^2 :=
      integral_sq_L2_representative _
    _ = _ := by rw [(stationaryKoopman μ T hT hzero haddT _).norm_map]

/-- The actual face/scene scalar field has an integrable square on every
finite original face cell, produced by stationarity and the original L2 moment. -/
theorem integrable_sq_stationaryScalarFaceReadout_prod
    (hTjoint : Measurable (fun p : G × Ω ↦ T p.1 p.2))
    (offset : ℝ → G) (x : Lp ℝ 2 μ) (R : ℝ)
    {A : Set (ι → ℝ)} (hAfinite : volume A ≠ ∞) :
    Integrable (fun p : (ι → ℝ) × Ω ↦
      (stationaryScalarFaceReadout μ T L offset x R p.1 p.2)^2)
      ((volume.restrict A).prod μ) := by
  let : IsFiniteMeasure (volume.restrict A) := isFiniteMeasure_restrict.mpr hAfinite
  have hm := (measurable_stationaryScalarFaceReadout μ T L hTjoint offset x R).pow_const 2
  apply (integrable_prod_iff hm.aestronglyMeasurable).mpr
  refine ⟨Filter.Eventually.of_forall (fun y ↦ ?_), ?_⟩
  · exact ((Lp.memLp x).comp_measurePreserving (hT (offset R + L (R • y)))).integrable_sq
  · have he : (fun y ↦ ∫ ω, ‖(stationaryScalarFaceReadout μ T L offset x R y ω)^2‖ ∂μ) =
        (fun _ : ι → ℝ ↦ ‖x‖^2) := by
      funext y
      simp only [Real.norm_eq_abs, abs_pow, sq_abs]
      exact integral_sq_stationaryScalarFaceReadout μ T hT hzero haddT L offset x R y
    change Integrable (fun y ↦ ∫ ω, ‖(stationaryScalarFaceReadout μ T L offset x R y ω)^2‖ ∂μ)
      (volume.restrict A)
    rw [he]
    exact integrable_const _

/-- Exact actual expected face energy, including the literal spatial cell volume. -/
theorem integral_stationaryScalarFaceReadout_sq_average
    (hTjoint : Measurable (fun p : G × Ω ↦ T p.1 p.2))
    (offset : ℝ → G) (x : Lp ℝ 2 μ) (R : ℝ)
    {A : Set (ι → ℝ)} (hAfinite : volume A ≠ ∞) :
    (∫ ω, (∫ y in A, (stationaryScalarFaceReadout μ T L offset x R y ω)^2) ∂μ) =
      volume.real A * ‖x‖^2 := by
  have hi := integrable_sq_stationaryScalarFaceReadout_prod μ T hT hzero haddT L
    hTjoint offset x R hAfinite
  rw [← integral_integral_swap hi]
  simp only [integral_sq_stationaryScalarFaceReadout μ T hT hzero haddT L offset x R,
    integral_const, measureReal_restrict_apply_univ, smul_eq_mul]

variable (hcont : ∀ x : Lp ℝ 2 μ,
  Continuous (fun y : ι → ℝ ↦ stationaryKoopman μ T hT hzero haddT (L y) x))
include hT hzero haddT hcont

omit [MeasurableSpace G] [BorelSpace G] [IsProbabilityMeasure μ] in
private theorem integrable_stationaryFaceCell_orbit
    (offset : ℝ → G) (x : Lp ℝ 2 μ) (R : ℝ)
    {A : Set (ι → ℝ)} (hAfinite : volume A ≠ ∞) :
    Integrable (fun y ↦ stationaryKoopman μ T hT hzero haddT (offset R + L (R • y)) x)
      (volume.restrict A) := by
  let : IsFiniteMeasure (volume.restrict A) := isFiniteMeasure_restrict.mpr hAfinite
  have hc : Continuous
      (fun y ↦ stationaryKoopman μ T hT hzero haddT (offset R + L (R • y)) x) := by
    have hc := ((stationaryKoopman μ T hT hzero haddT (offset R)).continuous.comp
      ((hcont x).comp (show Continuous (fun y : ι → ℝ ↦ R • y) by fun_prop)))
    simpa only [Function.comp_def, stationaryKoopman_add] using hc
  apply Integrable.of_bound hc.aestronglyMeasurable ‖x‖
  exact Filter.Eventually.of_forall (fun y ↦
    ((stationaryKoopman μ T hT hzero haddT (offset R + L (R • y))).norm_map x).le)

omit hcont in
/-- The true random cell integral is square integrable, with no sample-value bound. -/
theorem integrable_sq_stationaryScalarFaceCell_average
    (hTjoint : Measurable (fun p : G × Ω ↦ T p.1 p.2))
    (offset : ℝ → G) (x : Lp ℝ 2 μ) (R : ℝ)
    {A : Set (ι → ℝ)} (hAfinite : volume A ≠ ∞) :
    Integrable (fun ω ↦ (∫ y in A, stationaryScalarFaceReadout μ T L offset x R y ω)^2) μ := by
  let : IsFiniteMeasure (volume.restrict A) := isFiniteMeasure_restrict.mpr hAfinite
  exact integrable_sq_finiteCell_average (volume.restrict A) μ
    (measurable_stationaryScalarFaceReadout μ T L hTjoint offset x R)
    (stationaryScalarFaceReadout_ae_eq_koopman μ T hT hzero haddT L offset x R)
    (norm_nonneg x) (fun y ↦
      ((stationaryKoopman μ T hT hzero haddT (offset R + L (R • y))).norm_map x).le)

/-- Exact second moment of the literal original scene cell average. -/
theorem integral_sq_stationaryScalarFaceCell_average_eq
    (hTjoint : Measurable (fun p : G × Ω ↦ T p.1 p.2))
    (offset : ℝ → G) (x : Lp ℝ 2 μ) (R : ℝ)
    {A : Set (ι → ℝ)} (hAfinite : volume A ≠ ∞) :
    (∫ ω, (∫ y in A, stationaryScalarFaceReadout μ T L offset x R y ω)^2 ∂μ) =
      ‖∫ y in A, stationaryKoopman μ T hT hzero haddT (offset R + L (R • y)) x‖^2 := by
  let : IsFiniteMeasure (volume.restrict A) := isFiniteMeasure_restrict.mpr hAfinite
  exact integral_sq_finiteCell_average_eq_norm_sq (volume.restrict A) μ
    (integrable_stationaryFaceCell_orbit μ T hT hzero haddT L hcont offset x R hAfinite)
    (measurable_stationaryScalarFaceReadout μ T L hTjoint offset x R)
    (stationaryScalarFaceReadout_ae_eq_koopman μ T hT hzero haddT L offset x R)
    (norm_nonneg x) (fun y ↦
      ((stationaryKoopman μ T hT hzero haddT (offset R + L (R • y))).norm_map x).le)

/-- The actual scalar second moment vanishes on every fixed finite-measure
face cell. The limit follows from the existing genuine weighted face theorem,
not from an assumed scalar rate, mixing, or an assumed compactness conclusion. -/
theorem tendsto_integral_sq_stationaryScalarFaceCell_average_zero
    (hTjoint : Measurable (fun p : G × Ω ↦ T p.1 p.2))
    (offset : ℝ → G) {x : Lp ℝ 2 μ}
    (hx : (translationFixedSubspace (stationaryKoopman μ T hT hzero haddT) L.range).starProjection x = 0)
    {A : Set (ι → ℝ)} (hA : MeasurableSet A) (hAfinite : volume A ≠ ∞) :
    Tendsto (fun R : ℝ ↦ ∫ ω,
      (∫ y in A, stationaryScalarFaceReadout μ T L offset x R y ω)^2 ∂μ) atTop (𝓝 0) := by
  let w : (ι → ℝ) → ℝ := A.indicator (fun _ ↦ 1)
  have hw : Integrable w volume :=
    (integrableOn_const hAfinite).integrable_indicator hA
  have hlim := tendsto_stationaryWeightedFaceAverage_zero
    (stationaryKoopman μ T hT hzero haddT) (stationaryKoopman_add μ T hT hzero haddT)
    L hcont hw hx offset
  have he (R : ℝ) : (∫ y, w y • stationaryKoopman μ T hT hzero haddT
      (offset R + L (R • y)) x) =
      ∫ y in A, stationaryKoopman μ T hT hzero haddT (offset R + L (R • y)) x := by
    rw [← integral_indicator hA]
    congr 1
    funext y
    by_cases hy : y ∈ A <;> simp [w, hy]
  simp only [he] at hlim
  have hnorm := hlim.norm.pow 2
  simp only [norm_zero, zero_pow (by norm_num : 2 ≠ 0)] at hnorm
  apply hnorm.congr'
  filter_upwards [] with R
  exact (integral_sq_stationaryScalarFaceCell_average_eq μ T hT hzero haddT L hcont
    hTjoint offset x R hAfinite).symm

end OTSelector.Reconstruction

end
end
