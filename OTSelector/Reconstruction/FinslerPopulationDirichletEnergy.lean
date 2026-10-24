import OTSelector.Reconstruction.PopulationDirichletTiltedEnergy
import OTSelector.Reconstruction.FinslerPhysicalUpperEnergy
import OTSelector.Reconstruction.FinslerPhysicalSemidiscretePressure
import OTSelector.Geometry.Finsler.SlackAtomlessness
import OTSelector.Geometry.Finsler.DistanceLocalizationSupportBound
import OTSelector.MeasureTheory.CompactSupportedIntegrability

/-!
# The physical Dirichlet tilted allocation energy

The original nonnegative Lipschitz Finsler populations produce one potential and
one constant such that every measurable tilted semidiscrete optimum in the
original Dirichlet environment has expected base slack energy at most
`C + 2 |t| G`.  The atomlessness, measurability and integrability inputs are all
derived from the original geometry and density data.
-/

open Set Function MeasureTheory ProbabilityTheory Manifold Metric OTSelector.Geometry
open scoped Topology ContDiff ENNReal NNReal

noncomputable section
universe u v
namespace OTSelector.Reconstruction
open OTSelector.Probability

set_option backward.isDefEq.respectTransparency false

variable {E : Type u} {M : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  {F : ContinuousFinslerNorm E M}

/-- Original Lipschitz physical populations produce a potential and a uniform
Dirichlet tilted allocation energy bound for every sample size, probe and tilt. -/
theorem exists_finsler_lipschitz_population_dirichlet_energy
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
      ∀ (n : ℕ) (probe : M → M → ℝ) (G : ℝ≥0),
        Measurable (Function.uncurry probe) → (∀ x y, |probe x y| ≤ G) →
        ∀ t : ℝ,
        ∀ (A : (Fin (n + 1) → M) → (Fin (n + 1) → ℝ) →
            M → Fin (n + 1) → ℝ),
          (∀ j, Measurable (fun z : ((Fin (n + 1) → M) ×
            (Fin (n + 1) → ℝ)) × M ↦ A z.1.1 z.1.2 z.2 j)) →
          (∀ᵐ z ∂((Measure.pi (fun _ : Fin (n + 1) ↦ ν)).prod
            (dirichletOne n)), IsSemidiscreteAllocation μ z.2 (A z.1 z.2)) →
          (∀ᵐ z ∂((Measure.pi (fun _ : Fin (n + 1) ↦ ν)).prod
            (dirichletOne n)), ∀ b, IsSemidiscreteAllocation μ z.2 b →
              semidiscreteAllocationCost μ
                (fun s j ↦ ((n + 1 : ℕ) : ℝ) ^
                    (2 / ((Module.finrank ℝ E - 1 : ℕ) : ℝ)) *
                    ((F.lengthEDist s (z.1 j)).toReal - pot (z.1 j) + pot s) +
                  t * probe s (z.1 j)) (A z.1 z.2) ≤
              semidiscreteAllocationCost μ
                (fun s j ↦ ((n + 1 : ℕ) : ℝ) ^
                    (2 / ((Module.finrank ℝ E - 1 : ℕ) : ℝ)) *
                    ((F.lengthEDist s (z.1 j)).toReal - pot (z.1 j) + pot s) +
                  t * probe s (z.1 j)) b) →
          Integrable (fun z ↦ semidiscreteAllocationCost μ
            (fun s j ↦ ((n + 1 : ℕ) : ℝ) ^
                (2 / ((Module.finrank ℝ E - 1 : ℕ) : ℝ)) *
                ((F.lengthEDist s (z.1 j)).toReal - pot (z.1 j) + pot s))
            (A z.1 z.2))
            ((Measure.pi (fun _ : Fin (n + 1) ↦ ν)).prod (dirichletOne n)) ∧
          (∫ z, semidiscreteAllocationCost μ
            (fun s j ↦ ((n + 1 : ℕ) : ℝ) ^
                (2 / ((Module.finrank ℝ E - 1 : ℕ) : ℝ)) *
                ((F.lengthEDist s (z.1 j)).toReal - pot (z.1 j) + pot s))
            (A z.1 z.2)
            ∂((Measure.pi (fun _ : Fin (n + 1) ↦ ν)).prod (dirichletOne n))) ≤
            C + 2 * |t| * (G : ℝ) := by
  let μ := volM.withDensity (fun x ↦ ENNReal.ofReal (ρ₀ x))
  let ν := volM.withDensity (fun x ↦ ENNReal.ofReal (ρ₁ x))
  let _inst : MetricSpace M := F.metricSpace
  let _instProper : ProperSpace M := F.properSpace_of_complete hcomplete
  let _instPolish : PolishSpace M := inferInstance
  let _instStandard : StandardBorelSpace M := inferInstance
  let _instMeasEq : MeasurableEq M := inferInstance
  obtain ⟨pot, C, hu, hC, hbound, _⟩ :=
    exists_finsler_lipschitz_population_uniform_energy hF hcomplete hdim m volM
      ρ₀ ρ₁ hρ₀ hρ₁ hρ₀nonneg hρ₁nonneg v hv hvnonneg hvolume hA hB hAB hμ hν
  have hdim2 : 2 ≤ Module.finrank ℝ E := by omega
  have hρ₀L : LipschitzWith K₀ ρ₀ := hρ₀
  have hρ₁L : LipschitzWith K₁ ρ₁ := hρ₁
  have hμchart : ∀ old : M, ((μ : Measure M).restrict
      (extChartAt 𝓘(ℝ, E) old).source).map (extChartAt 𝓘(ℝ, E) old) ≪ m :=
    chartwise_ac_withDensity_of_volume_density volM m hρ₀L.continuous.measurable hρ₀nonneg
      v hv hvolume
  have hνchart : ∀ old : M, ((ν : Measure M).restrict
      (extChartAt 𝓘(ℝ, E) old).source).map (extChartAt 𝓘(ℝ, E) old) ≪ m :=
    chartwise_ac_withDensity_of_volume_density volM m hρ₁L.continuous.measurable hρ₁nonneg
      v hv hvolume
  let _instDiffuse : NullSingletonClass ν :=
    nullSingletonClass_of_chartwise_ac m ν hdim2 hνchart
  let cost : M → M → ℝ := fun x y ↦
    (F.lengthEDist x y).toReal - pot y + pot x
  have hcostm : Measurable (Function.uncurry cost) :=
    F.measurable_distance_slack hu
  have hcost : Integrable (Function.uncurry cost) (μ.prod ν) :=
    integrable_continuous_of_compact_carriers μ ν hA hB hμ hν
      (F.continuous_distance_slack hu)
  have hhat : ∀ y z, y ≠ z →
      NullSingletonClass (μ.map (fun x ↦ cost x y - cost x z)) := by
    intro y z hyz
    have h := hF.nullSingletonClass_map_scaled_distanceSlack_sub m μ hdim2 hμchart
      hcomplete pot (one_ne_zero) hyz
    simpa only [cost, one_mul, F.metricSpace_dist] using h
  exact ⟨pot, C, hu, hC, fun n probe G hprobeM hprobe t A hAmeas ha hopt =>
    integral_bipartite_dirichlet_tilted_allocation_energy_le
      (S := M) (T := M) (m := n) (q := Module.finrank ℝ E - 1)
      (μ := μ) (ν := ν) hbound hcostm hcost hhat hprobeM G hprobe t A
      hAmeas ha (by
        filter_upwards [hopt] with z hz
        exact fun b hb ↦ by simpa only [cost] using hz b hb)⟩

end OTSelector.Reconstruction
