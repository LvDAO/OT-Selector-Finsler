import OTSelector.Reconstruction.FinslerConcreteUpperClassPressure

/-! The microscopic side limit keeps the actual original spatial density in
the pressure weight and its reciprocal power in the kinetic coefficient. -/
open Set Function MeasureTheory ProbabilityTheory Filter Manifold OTSelector.Geometry
open scoped Topology ContDiff ENNReal NNReal BigOperators Classical BoundedContinuousFunction
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false

/-- Changing from intensity normalization to the actual microscopic side
pays the original density exactly. The limit is taken only after the sample
limit which supplied the finite-intensity pressure. -/
theorem tendsto_pressure_density_scaled_side
    {q : ℕ} (hq : 0 < q) {density : ℝ≥0} (hdensity : 0 < density)
    {pressure : ℝ≥0 → ℝ} {p : ℝ}
    (hp : Tendsto (fun r : ℝ ↦ pressure (Real.toNNReal r) / r) atTop (𝓝 p)) :
    Tendsto (fun L : ℝ ↦ pressure (density * Real.toNNReal (L ^ q)) / L ^ q)
      atTop (𝓝 ((density : ℝ) * p)) := by
  have hd : (0 : ℝ) < density := by exact_mod_cast hdensity
  have hpow : Tendsto (fun L : ℝ ↦ L ^ q) atTop atTop := by
    simpa only [Real.rpow_natCast] using (tendsto_rpow_atTop (by exact_mod_cast hq : (0 : ℝ) < q))
  have hmass : Tendsto (fun L : ℝ ↦ (density : ℝ) * L ^ q) atTop atTop :=
    hpow.const_mul_atTop hd
  have h := (hp.comp hmass).const_mul (density : ℝ)
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with L hL
  have hpL : L ^ q ≠ 0 := (pow_pos hL q).ne'
  have hdL : (density : ℝ) * L ^ q ≠ 0 := mul_ne_zero hd.ne' hpL
  simp only [Function.comp_def]
  rw [Real.toNNReal_mul (le_of_lt hd), Real.toNNReal_coe]
  field_simp

variable {E M Z : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [MeasurableSpace M] [TopologicalSpace Z] [MeasurableSpace Z]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {P : ℕ → F.CalibratedSeedWindow u} {a : M → Z}
  {κ : ∀ j, Measure (P j).seed.covector.ker} {lambda : Measure Z}
  {η₀ η₁ : Measure M} [IsFiniteMeasure η₀] [IsFiniteMeasure η₁] {δ : ℝ≥0∞}

/-- The actual original coefficient model has its physical density-weighted
microscopic-side pressure limit. The unit-intensity pressure uses the genuine
inverse density power in its kinetic term; the physical density is retained
in the limiting volume weight. -/
theorem OriginalPopulationCoefficientCore.exists_physical_density_clockClassPressure_limit
    (C : OriginalPopulationCoefficientCore P a κ lambda η₀ η₁ δ)
    {range : Set ℝ} {width : ℝ} (Q : FiniteScalarBins range width)
    (z₀ : Z) (hz₀ : z₀ ∈ C.roots) (f : M × M →ᵇ ℝ)
    (P₀ : Fin Q.count → Fin Q.count → ℝ)
    (hP₀ : ∀ j k, 0 ≤ P₀ j k)
    (hzero : ∀ j k, ¬C.clockClassAllowed Q j k → P₀ j k = 0)
    (hmass : 0 < ∑ j, ∑ k, P₀ j k)
    (density : ℝ≥0) (hdensity : 0 < density)
    (hq : 4 < Module.finrank ℝ (P C.seedIndex).seed.covector.ker) :
    let π := clockClassJointProbability P₀ hP₀ hmass
    let α := π.map measurable_fst.aemeasurable
    let β := π.map measurable_snd.aemeasurable
    let q := Module.finrank ℝ (P C.seedIndex).seed.covector.ker
    let kin := C.densityClockClassKinetic Q z₀ density
    let probe := C.clockClassProbe Q z₀ hz₀ f
    ∃ p : ℝ → ℝ,
      (∀ t, Tendsto (fun L : ℝ ↦ finiteClassLegalPressure q (C.clockClassAllowed Q)
        (α : Measure _) (β : Measure _) (density * Real.toNNReal (L ^ q)) kin probe t / L ^ q)
        atTop (𝓝 ((density : ℝ) * p t))) ∧
      ConcaveOn ℝ univ p ∧ LipschitzWith ⟨‖f‖, norm_nonneg f⟩ p := by
  obtain ⟨p,hp,hintensity,huniform,hconc,hlip⟩ :=
    C.exists_density_clockClassPressure_limit Q z₀ hz₀ f P₀ hP₀ hzero hmass density
      (by exact_mod_cast hdensity) hq
  refine ⟨p,?_,hconc,hlip⟩
  intro t
  let π := clockClassJointProbability P₀ hP₀ hmass
  let α := π.map measurable_fst.aemeasurable
  let β := π.map measurable_snd.aemeasurable
  exact tendsto_pressure_density_scaled_side
    (q := Module.finrank ℝ (P C.seedIndex).seed.covector.ker) (by omega) hdensity
    (pressure := fun r ↦ finiteClassLegalPressure _ (C.clockClassAllowed Q)
      (α : Measure _) (β : Measure _) r (C.densityClockClassKinetic Q z₀ density)
        (C.clockClassProbe Q z₀ hz₀ f) t) (hintensity t)

end OTSelector.Reconstruction
