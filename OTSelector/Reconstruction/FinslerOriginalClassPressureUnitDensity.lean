import OTSelector.Reconstruction.FinslerOriginalPressureKineticScaling

/-! One actual unit-density legal pressure determines every physical-density
pressure of the same original frozen coefficient and retained class law. -/
open Set Function MeasureTheory ProbabilityTheory Filter Manifold OTSelector.Geometry
open scoped Topology ContDiff ENNReal NNReal BigOperators BoundedContinuousFunction Classical
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1800000

variable {E M Z : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [MeasurableSpace M] [TopologicalSpace Z] [MeasurableSpace Z]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {P : ℕ → F.CalibratedSeedWindow u} {a : M → Z}
  {κ : ∀ j, Measure (P j).seed.covector.ker} {lambda : Measure Z}
  {η₀ η₁ : Measure M} [IsFiniteMeasure η₀] [IsFiniteMeasure η₁] {δ : ℝ≥0∞}

/-- One original unit-density pressure controls all positive retained physical
densities. The original class mask, conditional class plan, frozen geometric
kinetic coefficient and physical probe stay fixed. The only density-dependent
operations are the original point intensity and inverse quadratic kinetic scale. -/
theorem OriginalPopulationCoefficientCore.exists_clockClassPressure_unit_density
    (C : OriginalPopulationCoefficientCore P a κ lambda η₀ η₁ δ)
    {range : Set ℝ} {width : ℝ} (Q : FiniteScalarBins range width)
    (z₀ : Z) (hz₀ : z₀ ∈ C.roots) (f : M × M →ᵇ ℝ)
    (P₀ : Fin Q.count → Fin Q.count → ℝ)
    (hP₀ : ∀ j k, 0 ≤ P₀ j k)
    (hzero : ∀ j k, ¬C.clockClassAllowed Q j k → P₀ j k = 0)
    (hmass : 0 < ∑ j, ∑ k, P₀ j k)
    (hq : 4 < Module.finrank ℝ (P C.seedIndex).seed.covector.ker) :
    let π := clockClassJointProbability P₀ hP₀ hmass
    let α := π.map measurable_fst.aemeasurable
    let β := π.map measurable_snd.aemeasurable
    let q := Module.finrank ℝ (P C.seedIndex).seed.covector.ker
    let kin := C.clockClassKinetic Q z₀
    let probe := C.clockClassProbe Q z₀ hz₀ f
    ∃ p : ℝ → ℝ,
      (∀ t, Tendsto (fun R ↦ finiteClassLegalScalePressure q (C.clockClassAllowed Q)
        (α : Measure _) (β : Measure _) kin probe R t) atTop (𝓝 (p t))) ∧
      (∀ density : ℝ≥0, 0 < density → ∀ t,
        Tendsto (fun L : ℝ ↦ finiteClassLegalPressure q (C.clockClassAllowed Q)
          (α : Measure _) (β : Measure _) (density * Real.toNNReal (L ^ q))
          (C.densityClockClassKinetic Q z₀ density) probe t / L ^ q)
          atTop (𝓝 ((density : ℝ) ^ (1 - 2 / (q : ℝ)) *
            p (t * (density : ℝ) ^ (2 / (q : ℝ)))))) ∧
      ConcaveOn ℝ univ p ∧ LipschitzWith ⟨‖f‖, norm_nonneg f⟩ p := by
  let π := clockClassJointProbability P₀ hP₀ hmass
  let α := π.map measurable_fst.aemeasurable
  let β := π.map measurable_snd.aemeasurable
  let q := Module.finrank ℝ (P C.seedIndex).seed.covector.ker
  obtain ⟨p,hp,hconc,hlip⟩ := C.exists_clockClassPressure_limit Q z₀ hz₀ f P₀ hP₀ hzero hmass hq
  have hnested : ∀ j j', (∀ k, C.clockClassAllowed Q j k → C.clockClassAllowed Q j' k) ∨
      (∀ k, C.clockClassAllowed Q j' k → C.clockClassAllowed Q j k) :=
    C.clockClassAllowed_rows_nested Q
  have hintensity := tendsto_finiteClassLegalPressure_div_of_nested
    (C.clockClassAllowed Q) hnested q (by omega) (α : Measure _) (β : Measure _)
    (C.clockClassKinetic Q z₀) (C.clockClassProbe Q z₀ hz₀ f) p hp
  refine ⟨p,hp,?_,hconc,hlip⟩
  intro density hdensity t
  exact tendsto_finiteClassLegalPressure_physical_density q (by omega) (C.clockClassAllowed Q)
    (α : Measure _) (β : Measure _) (C.clockClassKinetic Q z₀) (C.clockClassProbe Q z₀ hz₀ f)
    p hintensity density hdensity t

/-- Any actual physical-density limit equals the canonical unit-density
representation, by uniqueness of the original real side-length limit. -/
theorem original_physical_pressure_limit_eq_unit_density
    {q : ℕ} (hq : 0 < q) {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    (allowed : A → B → Prop)
    (α : Measure A) [IsProbabilityMeasure α] (β : Measure B) [IsProbabilityMeasure β]
    (kin : A → B → (Fin q → ℝ) → ℝ) (probe : A → B → ℝ)
    (p : ℝ → ℝ)
    (hp : ∀ t, Tendsto (fun r : ℝ ↦
      finiteClassLegalPressure q allowed α β (Real.toNNReal r) kin probe t / r)
      atTop (𝓝 (p t)))
    (density : ℝ≥0) (hdensity : 0 < density) {t limit : ℝ}
    (hlimit : Tendsto (fun L : ℝ ↦ finiteClassLegalPressure q allowed α β
        (density * Real.toNNReal (L ^ q))
        (fun a b v ↦ (density : ℝ) ^ (-2 / (q : ℝ)) * kin a b v) probe t / L ^ q)
      atTop (𝓝 limit)) :
    limit = (density : ℝ) ^ (1 - 2 / (q : ℝ)) * p (t * (density : ℝ) ^ (2 / (q : ℝ))) :=
  tendsto_nhds_unique hlimit
    (tendsto_finiteClassLegalPressure_physical_density q hq allowed α β kin probe p hp
      density hdensity t)

end OTSelector.Reconstruction
