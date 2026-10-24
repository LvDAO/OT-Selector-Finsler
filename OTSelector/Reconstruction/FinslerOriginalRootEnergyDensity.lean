import OTSelector.Reconstruction.OriginalAllocationRootEnergy
import OTSelector.Reconstruction.FinslerPhysicalSceneEnergy

/-! Original general Finsler data produce integrable original-root energy
without any conditional density lower bound or prescribed balance. -/
open Set Function MeasureTheory ProbabilityTheory Manifold Metric OTSelector.Geometry
open scoped Topology ContDiff ENNReal NNReal
noncomputable section
universe u v
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
variable {Z : Type*} [MeasurableSpace Z]

variable {E : Type u} {M : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  {F : ContinuousFinslerNorm E M}

/-- The original Finsler populations produce one energy constant. Every
actual zero-tilt allocation optimum has a canonical integrable source-root
energy density bounded by this same constant, uniformly in sample size.
Each root-set integral equals its unchanged original physical energy. -/
theorem exists_finsler_original_root_energy_density
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hdim : 6 ≤ Module.finrank ℝ E)
    (m : Measure E) [m.IsAddHaarMeasure] (volM : Measure M)
    (ρ₀ ρ₁ : M → ℝ) {K₀ K₁ : ℝ≥0}
    (hρ₀ : let _inst : MetricSpace M := F.metricSpace; LipschitzWith K₀ ρ₀)
    (hρ₁ : let _inst : MetricSpace M := F.metricSpace; LipschitzWith K₁ ρ₁)
    (hρ₀nonneg : ∀ x, 0 ≤ ρ₀ x) (hρ₁nonneg : ∀ x, 0 ≤ ρ₁ x)
    [IsProbabilityMeasure (volM.withDensity (fun x ↦ ENNReal.ofReal (ρ₀ x)))]
    [IsProbabilityMeasure (volM.withDensity (fun x ↦ ENNReal.ofReal (ρ₁ x)))]
    (v : M → E → ℝ)
    (hv : ∀ old, ContinuousOn (v old) (extChartAt 𝓘(ℝ, E) old).target)
    (hvnonneg : ∀ old, ∀ y ∈ (extChartAt 𝓘(ℝ, E) old).target, 0 ≤ v old y)
    (hvolume : ∀ old : M, let χ := extChartAt 𝓘(ℝ, E) old
      (volM.restrict χ.source).map χ = (m.restrict χ.target).withDensity
        (fun y ↦ ENNReal.ofReal (v old y)))
    {A B : Set M} (hA : IsCompact A) (hB : IsCompact B) (hAB : Disjoint A B)
    (hμ : ∀ᵐ x ∂volM.withDensity (fun x ↦ ENNReal.ofReal (ρ₀ x)), x ∈ A)
    (hν : ∀ᵐ x ∂volM.withDensity (fun x ↦ ENNReal.ofReal (ρ₁ x)), x ∈ B) :
    let μ := volM.withDensity (fun x ↦ ENNReal.ofReal (ρ₀ x))
    let ν := volM.withDensity (fun x ↦ ENNReal.ofReal (ρ₁ x))
    let _inst : MetricSpace M := F.metricSpace
    ∃ (pot : M → ℝ) (C : ℝ), LipschitzWith 1 pot ∧ 0 < C ∧
      ∀ (n : ℕ) (allocation : ((Fin (n + 1) → M) × (Fin (n + 1) → ℝ)) →
          M → Fin (n + 1) → ℝ),
        (∀ j, Measurable (fun z : ((Fin (n + 1) → M) ×
          (Fin (n + 1) → ℝ)) × M ↦ allocation z.1 z.2 j)) →
        (∀ᵐ z ∂((Measure.pi (fun _ : Fin (n + 1) ↦ ν)).prod (dirichletOne n)),
          IsOptimalSemidiscreteAllocation μ z.2
            (fun s j ↦ ((n + 1 : ℕ) : ℝ) ^
              (2 / ((Module.finrank ℝ E - 1 : ℕ) : ℝ)) *
              ((F.lengthEDist s (z.1 j)).toReal - pot (z.1 j) + pot s)) (allocation z)) →
        ∀ (label : M → Z), Measurable label →
        ∃ f : Z → ℝ, Measurable f ∧ (∀ z, 0 ≤ f z) ∧
          Integrable f (μ.map label) ∧ (∫ z, f z ∂μ.map label) ≤ C ∧
          ∀ K : Set Z, MeasurableSet K →
            (∫ z in K, f z ∂μ.map label) =
              (∫⁻ z, ∫⁻ p in (fun p : M × M ↦ label p.1) ⁻¹' K,
                ENNReal.ofReal (((n + 1 : ℕ) : ℝ) ^
                  (2 / ((Module.finrank ℝ E - 1 : ℕ) : ℝ)) *
                  ((F.lengthEDist p.1 p.2).toReal - pot p.2 + pot p.1))
                ∂physicalSceneGlobalAllocationFamily μ allocation (fun z ↦ z.1) z
                ∂((Measure.pi (fun _ : Fin (n + 1) ↦ ν)).prod (dirichletOne n))).toReal := by
  let μ := volM.withDensity (fun x ↦ ENNReal.ofReal (ρ₀ x))
  let ν := volM.withDensity (fun x ↦ ENNReal.ofReal (ρ₁ x))
  let _inst : MetricSpace M := F.metricSpace
  let _instProper : ProperSpace M := F.properSpace_of_complete hcomplete
  let _instPolish : PolishSpace M := inferInstance
  obtain ⟨pot, C, hpot, hC, henergy⟩ :=
    exists_finsler_lipschitz_population_dirichlet_plan_energy hF hcomplete hdim m volM
      ρ₀ ρ₁ hρ₀ hρ₁ hρ₀nonneg hρ₁nonneg v hv hvnonneg hvolume hA hB hAB hμ hν
  refine ⟨pot, C, hpot, hC, ?_⟩
  intro n allocation hmeas hopt label hlabel
  have hfeas := hopt.mono (fun _ hz ↦ hz.1)
  have hbound := henergy n (fun _ _ ↦ 0) 0 measurable_const (by simp) 0
    (fun Y p ↦ allocation (Y, p)) hmeas hfeas (by
      filter_upwards [hopt] with z hz
      simpa only [zero_mul, add_zero] using hz.2)
  simp only [abs_zero, mul_zero, add_zero, NNReal.coe_zero] at hbound
  exact exists_originalAllocation_rootEnergyDensity μ ν n allocation hmeas hfeas
    label hlabel _ ((F.measurable_distance_slack hpot).const_mul _).ennreal_ofReal hC.le hbound

end OTSelector.Reconstruction
