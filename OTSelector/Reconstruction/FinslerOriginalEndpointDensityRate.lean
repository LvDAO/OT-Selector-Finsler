import OTSelector.Reconstruction.SeedEndpointPhysicalDensityRate
import OTSelector.Reconstruction.FinslerOriginalConditionalMoments

/-! Sharp original-clock endpoint density rates, from the original physical
population density and the same selected actual endpoint Jacobi frame. -/
open Set Matrix Module Manifold MeasureTheory
open scoped Topology ContDiff Matrix.Norms.Operator ENNReal
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Geometry ContinuousFinslerNorm
set_option backward.isDefEq.respectTransparency false

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ} {S : CalibratedLevelSeedPatch F u}
  {w : S.covector.ker} {μ ν σ : Measure ℝ}

omit [BorelSpace E] in
/-- Retain the literal original conditional measure and its physical density in a
specified endpoint chart. The determinant bound is derived from the original data. -/
theorem OriginalSeedConditionalMoments.original_density_in_endpointChart
    (D : OriginalSeedConditionalMoments S w μ ν)
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {endpoint l h : ℝ} (G : SeedEndpointChart S D.comparison endpoint)
    (hI : ∀ t ∈ Icc l h, (w, t) ∈ G.geometry.U)
    (hsub : Ioo l h ⊆ Ioo D.lo D.hi)
    {ρ : M → ℝ} {v : M → E → ℝ} (c : ℝ≥0∞)
    (hρ : Continuous ρ) (hρ0 : ∀ x, 0 ≤ ρ x)
    (hv : ∀ old, ContinuousOn (v old) (extChartAt 𝓘(ℝ, E) old).target)
    (hv0 : ∀ old, ∀ y ∈ (extChartAt 𝓘(ℝ, E) old).target, 0 ≤ v old y)
    (hdensity : PopulationSeedClockDensity S w
      (σ.map (fun x : ℝ ↦ x - S.level)) ρ v c.toReal) :
    (σ.map (fun x : ℝ ↦ x - S.level)).restrict (Ioo l h) =
      (volume.restrict (Ioo l h)).withDensity (fun t ↦
        ENNReal.ofReal (c.toReal * populationSeedChartDensity S ρ v G.center w t)) ∧
    ∃ K : ℝ, 0 < K ∧ ∀ t ∈ Ioo l h,
      0 ≤ c.toReal * populationSeedChartDensity S ρ v G.center w t ∧
      c.toReal * populationSeedChartDensity S ρ v G.center w t ≤
        K * |(G.jacobiPositionMatrix (Module.finBasis ℝ S.covector.ker) (G.clock t)).det| := by
  have hactive : Ioo D.lo D.hi ⊆ interior (S.calibrationTimes w) := by
    simpa only [interior_Icc] using interior_mono D.support.calibrated
  refine ⟨hdensity G.center G.label_mem (Ioo l h) measurableSet_Ioo
    (fun t ht ↦ ⟨hactive (hsub ht),
      G.time_mem_ball_of_mem_source (hI t (Ioo_subset_Icc_self ht))⟩), ?_⟩
  apply G.exists_original_density_determinant_bound hF
    (Module.finBasis ℝ S.covector.ker) hw D.curve_eq hI ?_ c hρ hρ0 (hv G.old) (hv0 G.old)
  intro t ht
  have hx := G.geometry.curve_source (w, t) (hI t (Ioo_subset_Icc_self ht))
  rw [← D.curve_eq] at hx
  exact ⟨_, D.phase_jet G.old t hx⟩

omit [BorelSpace E] in
/-- The original input law has its actual left endpoint density rate. The
endpoint chart and the physical-time rate are produced internally. -/
theorem OriginalSeedConditionalMoments.exists_original_left_density_rate
    (D : OriginalSeedConditionalMoments S w μ ν)
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {ρ : M → ℝ} {v : M → E → ℝ} (c : ℝ≥0∞)
    (hρ : Continuous ρ) (hρ0 : ∀ x, 0 ≤ ρ x)
    (hv : ∀ old, ContinuousOn (v old) (extChartAt 𝓘(ℝ, E) old).target)
    (hv0 : ∀ old, ∀ y ∈ (extChartAt 𝓘(ℝ, E) old).target, 0 ≤ v old y)
    (hdensity : PopulationSeedClockDensity S w
      (σ.map (fun x : ℝ ↦ x - S.level)) ρ v c.toReal) :
    ∃ (G : SeedEndpointChart S D.comparison D.lo) (h ε K : ℝ),
      D.lo < h ∧ h < D.hi ∧ (∀ t ∈ Icc D.lo h, (w, t) ∈ G.geometry.U) ∧
      0 < ε ∧ ε < h - D.lo ∧ 0 < K ∧
      (σ.map (fun x : ℝ ↦ x - S.level)).restrict (Ioo D.lo h) =
        (volume.restrict (Ioo D.lo h)).withDensity (fun t ↦
          ENNReal.ofReal (c.toReal * populationSeedChartDensity S ρ v G.center w t)) ∧
      ∀ r ∈ Ioo 0 ε,
        0 ≤ c.toReal * populationSeedChartDensity S ρ v G.center w (D.lo + r) ∧
        c.toReal * populationSeedChartDensity S ρ v G.center w (D.lo + r) ≤
          K * r ^ Module.finrank ℝ (LinearMap.ker
            (G.jacobiPositionMatrix (Module.finBasis ℝ S.covector.ker)
              (G.clock D.lo)).mulVecLin) := by
  obtain ⟨G, _, h, _, hlo, hhi, _, _, hI, _⟩ :=
    S.exists_seedEndpointCharts D.comparison hF hw D.curve_eq D.support.lt
  have hdata := D.original_density_in_endpointChart hF hw G hI
    (fun _ ht ↦ ⟨ht.1, ht.2.trans hhi⟩) c hρ hρ0 hv hv0 hdensity
  obtain ⟨_, P, A, B, C, H⟩ :=
    G.physical_clock_system hF (Module.finBasis ℝ S.covector.ker) hlo hI
  obtain ⟨ε, K, hε, hεh, hK, hbound⟩ := H.exists_left_density_power_bound hlo hdata.2
  exact ⟨G, h, ε, K, hlo, hhi, hI, hε, hεh, hK, hdata.1, hbound⟩

omit [BorelSpace E] in
/-- The original input law also has its actual right endpoint density rate,
retaining its own selected original chart and its exact physical density. -/
theorem OriginalSeedConditionalMoments.exists_original_right_density_rate
    (D : OriginalSeedConditionalMoments S w μ ν)
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {ρ : M → ℝ} {v : M → E → ℝ} (c : ℝ≥0∞)
    (hρ : Continuous ρ) (hρ0 : ∀ x, 0 ≤ ρ x)
    (hv : ∀ old, ContinuousOn (v old) (extChartAt 𝓘(ℝ, E) old).target)
    (hv0 : ∀ old, ∀ y ∈ (extChartAt 𝓘(ℝ, E) old).target, 0 ≤ v old y)
    (hdensity : PopulationSeedClockDensity S w
      (σ.map (fun x : ℝ ↦ x - S.level)) ρ v c.toReal) :
    ∃ (G : SeedEndpointChart S D.comparison D.hi) (l ε K : ℝ),
      D.lo < l ∧ l < D.hi ∧ (∀ t ∈ Icc l D.hi, (w, t) ∈ G.geometry.U) ∧
      0 < ε ∧ ε < D.hi - l ∧ 0 < K ∧
      (σ.map (fun x : ℝ ↦ x - S.level)).restrict (Ioo l D.hi) =
        (volume.restrict (Ioo l D.hi)).withDensity (fun t ↦
          ENNReal.ofReal (c.toReal * populationSeedChartDensity S ρ v G.center w t)) ∧
      ∀ r ∈ Ioo 0 ε,
        0 ≤ c.toReal * populationSeedChartDensity S ρ v G.center w (D.hi - r) ∧
        c.toReal * populationSeedChartDensity S ρ v G.center w (D.hi - r) ≤
          K * r ^ Module.finrank ℝ (LinearMap.ker
            (G.jacobiPositionMatrix (Module.finBasis ℝ S.covector.ker)
              (G.clock D.hi)).mulVecLin) := by
  obtain ⟨_, G, _, l, _, _, hlo, hhi, _, hI⟩ :=
    S.exists_seedEndpointCharts D.comparison hF hw D.curve_eq D.support.lt
  have hdata := D.original_density_in_endpointChart hF hw G hI
    (fun _ ht ↦ ⟨hlo.trans ht.1, ht.2⟩) c hρ hρ0 hv hv0 hdensity
  obtain ⟨_, P, A, B, C, H⟩ :=
    G.physical_clock_system hF (Module.finBasis ℝ S.covector.ker) hhi hI
  obtain ⟨ε, K, hε, hεh, hK, hbound⟩ := H.exists_right_density_power_bound hhi hdata.2
  exact ⟨G, l, ε, K, hlo, hhi, hI, hε, hεh, hK, hdata.1, hbound⟩

end OTSelector.Reconstruction
