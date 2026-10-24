import OTSelector.Reconstruction.FinslerRelativeLawLegalBinomialVarying
import OTSelector.Reconstruction.FinslerConcreteUpperClassPressure
import OTSelector.Reconstruction.MarkedStationaryValueLegalAffineDensity
import OTSelector.Probability.MicroscopicGridScale

/-! Actual original finite-class full cubes at the prescribed integer microscopic scale. -/
open Set Function MeasureTheory ProbabilityTheory Filter Matrix Manifold OTSelector.Geometry
open scoped Topology ContDiff ENNReal NNReal Matrix.Norms.Operator BigOperators
  BoundedContinuousFunction Classical unitInterval
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
set_option linter.unusedSectionVars false

/-- Original homogeneous full-cube probability, clipped only for the finitely
many initial boxes whose proposed mass can exceed one. -/
def microscopicCubeProbability (q : ℕ) (density : ℝ≥0) (L : ℝ) (N : ℕ) : I :=
  ⟨min ((density : ℝ) * microscopicGridSide q L N ^ q) 1,
    le_min (mul_nonneg density.coe_nonneg (pow_nonneg (microscopicGridSide_nonneg q L N) q))
      (by norm_num), min_le_right _ _⟩

theorem microscopicCubeProbability_eventually_eq {q : ℕ} (hq : 0 < q)
    (density : ℝ≥0) {L : ℝ} (hL : 0 < L) :
    ∀ᶠ N : ℕ in atTop, (microscopicCubeProbability q density L N : ℝ) =
      (density : ℝ) * microscopicGridSide q L N ^ q := by
  have hside := (tendsto_microscopicGridSide hq hL).comp tendsto_natCast_atTop_atTop
  have hmass : Tendsto (fun N : ℕ ↦ (density : ℝ) * microscopicGridSide q L N ^ q)
      atTop (𝓝 0) := by
    simpa only [Function.comp_def, zero_pow hq.ne', mul_zero] using (hside.pow q).const_mul (density : ℝ)
  filter_upwards [hmass.eventually (Iio_mem_nhds (by norm_num : (0:ℝ) < 1))] with N hN
  exact min_eq_left hN.le

theorem tendsto_microscopicCubeProbability_mean {q : ℕ} (hq : 0 < q)
    (density : ℝ≥0) {L : ℝ} (hL : 0 < L) :
    Tendsto (fun N : ℕ ↦ (N : ℝ) * (microscopicCubeProbability q density L N : ℝ))
      atTop (𝓝 ((density : ℝ) * L ^ q)) := by
  apply Tendsto.congr' _ ((tendsto_microscopicGrid_density_mass hq hL (density : ℝ)).comp
    tendsto_natCast_atTop_atTop)
  filter_upwards [microscopicCubeProbability_eventually_eq hq density hL] with N hN
  simp only [Function.comp_def]
  rw [hN]
  ring

variable {E M Z : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [MeasurableSpace M] [TopologicalSpace Z] [MeasurableSpace Z]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {P : ℕ → F.CalibratedSeedWindow u} {a : M → Z}
  {κ : ∀ j, Measure (P j).seed.covector.ker} {lambda : Measure Z}
  {η₀ η₁ : Measure M} [IsFiniteMeasure η₀] [IsFiniteMeasure η₁] {δ : ℝ≥0∞}

/-- Full original binomial microcubes converge to the actual density-scaled
legal class pressure. The original fixed pair weights, physical coefficient,
probe and integer-grid rounding are all instantiated in the conclusion. -/
theorem OriginalPopulationCoefficientCore.tendsto_clockClass_fullCube_binomial
    (C : OriginalPopulationCoefficientCore P a κ lambda η₀ η₁ δ)
    {range : Set ℝ} {width : ℝ} (Q : FiniteScalarBins range width)
    (z₀ : Z) (hz₀ : z₀ ∈ C.roots) (f : M × M →ᵇ ℝ)
    (P₀ : Fin Q.count → Fin Q.count → ℝ)
    (hP₀ : ∀ j k, 0 ≤ P₀ j k) (hmass : 0 < ∑ j, ∑ k, P₀ j k)
    (hq : 0 < Module.finrank ℝ (P C.seedIndex).seed.covector.ker)
    (density : ℝ≥0) (hdensity : 0 < density) {L : ℝ} (hL : 0 < L) (tilt : ℝ) :
    let π := clockClassJointProbability P₀ hP₀ hmass
    let α := π.map measurable_fst.aemeasurable
    let β := π.map measurable_snd.aemeasurable
    let q := Module.finrank ℝ (P C.seedIndex).seed.covector.ker
    Tendsto (fun N : ℕ ↦ ∫ cloud : TwoMarkedCloudSpace q (Fin Q.count) (Fin Q.count),
      finiteClassLegalTilted q (C.clockClassAllowed Q) 1
        (fun j k v ↦ (N : ℝ) ^ (2 / (q : ℝ)) * microscopicGridSide q L N ^ 2 *
          C.clockClassKinetic Q z₀ j k v) (C.clockClassProbe Q z₀ hz₀ f) tilt cloud
        ∂twoMarkedCountLaw q (α : Measure _) (β : Measure _)
          (ProbabilityTheory.binomial N (microscopicCubeProbability q density L N))) atTop
      (𝓝 (finiteClassLegalPressure q (C.clockClassAllowed Q) (α : Measure _) (β : Measure _)
        (density * ⟨L ^ q, pow_nonneg hL.le q⟩)
        (C.densityClockClassKinetic Q z₀ density) (C.clockClassProbe Q z₀ hz₀ f) tilt)) := by
  let π := clockClassJointProbability P₀ hP₀ hmass
  let α := π.map measurable_fst.aemeasurable
  let β := π.map measurable_snd.aemeasurable
  let q := Module.finrank ℝ (P C.seedIndex).seed.covector.ker
  obtain ⟨source, target, hcode, _⟩ := C.exists_clockClass_strict_clocks Q
  obtain ⟨K, hK, hbound⟩ := C.exists_clockClassKinetic_bound Q z₀ hz₀
  let r : ℝ≥0 := density * ⟨L ^ q, pow_nonneg hL.le q⟩
  have hr : Tendsto (fun N : ℕ ↦ (N : ℝ) * (microscopicCubeProbability q density L N : ℝ))
      atTop (𝓝 (r : ℝ)) := tendsto_microscopicCubeProbability_mean hq density hL
  have hscale : Tendsto (fun N : ℕ ↦ (N : ℝ) ^ (2 / (q : ℝ)) *
      microscopicGridSide q L N ^ 2) atTop (𝓝 (L ^ 2)) :=
    (tendsto_microscopicGrid_quadratic hq hL).comp tendsto_natCast_atTop_atTop
  have hlim := tendsto_legalMarkedTilted_binomial_multiplier
    (kin := C.clockClassKinetic Q z₀)
    (probe := C.clockClassProbe Q z₀ hz₀ f) q
    (measurable_of_countable source) (measurable_of_countable target)
    (α : Measure _) (β : Measure _) hK (norm_nonneg f)
    (C.measurable_clockClassKinetic Q z₀) hbound
    (C.measurable_clockClassProbe Q z₀ hz₀ f) (C.clockClassProbe_abs_le Q z₀ hz₀ f)
    _ hscale (microscopicCubeProbability q density L) r hr tilt
  have hcancel : (r : ℝ) ^ (2 / (q : ℝ)) *
      (density : ℝ) ^ (-(2 / (q : ℝ))) = L ^ 2 := by
    change ((density : ℝ) * L ^ q) ^ (2 / (q : ℝ)) * _ = _
    rw [mul_comm (density : ℝ) (L ^ q),
      rpow_positive_density_cancel (pow_nonneg hL.le q) (by exact_mod_cast hdensity)]
    simpa only [one_mul, Real.one_rpow] using
      rpow_affine_intensity q hq (by norm_num : (0:ℝ) ≤ 1) hL.le
  have hvalue (cloud : TwoMarkedCloudSpace q (Fin Q.count) (Fin Q.count)) :
      legalMarkedTilted q source target 1
        (fun j k v ↦ L ^ 2 * C.clockClassKinetic Q z₀ j k v)
        (C.clockClassProbe Q z₀ hz₀ f) tilt cloud =
      legalMarkedTilted q source target r (C.densityClockClassKinetic Q z₀ density)
        (C.clockClassProbe Q z₀ hz₀ f) tilt cloud := by
    apply PartialMatching.legalMaximumValue_congr_on_allowed
    intro j k _
    simp only [mKineticCost, Real.one_rpow, one_mul,
      OriginalPopulationCoefficientCore.densityClockClassKinetic, q, neg_div]
    rw [← mul_assoc, hcancel]
  have hpressure : (∫ cloud, legalMarkedTilted q source target 1
      (fun j k v ↦ L ^ 2 * C.clockClassKinetic Q z₀ j k v)
      (C.clockClassProbe Q z₀ hz₀ f) tilt cloud ∂twoMarkedCloudLaw q _ _ (α : Measure _) (β : Measure _) r) =
      finiteClassLegalPressure q (C.clockClassAllowed Q) (α : Measure _) (β : Measure _)
        r (C.densityClockClassKinetic Q z₀ density) (C.clockClassProbe Q z₀ hz₀ f) tilt := by
    rw [finiteClassLegalPressure_eq_clock q _ source target hcode]
    exact integral_congr_ae (.of_forall hvalue)
  rw [hpressure] at hlim
  convert hlim using 1
  funext N
  apply integral_congr_ae
  filter_upwards [] with cloud
  exact finiteClassLegalTilted_eq_clock q _ source target hcode _ _ _ _ cloud

end OTSelector.Reconstruction
