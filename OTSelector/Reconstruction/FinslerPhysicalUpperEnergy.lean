import OTSelector.Reconstruction.FinslerPopulationPhysicalTypes
import OTSelector.Reconstruction.PopulationUniformEnergyBound
import OTSelector.Reconstruction.PopulationTypedSubplanCompetitor
import OTSelector.Reconstruction.PopulationTypedSubplanPressure

/-!
# Original Lipschitz Finsler populations have uniformly bounded empirical energy

The original physical densities produce the potential, whole optimal face,
finite full-mass atlas and actual marked competitor. No geometric labels,
conditional laws, endpoint rank, sample law or cost bound are supplied.
-/

open Set Function MeasureTheory ProbabilityTheory Manifold Metric OTSelector.Geometry
open scoped Topology ContDiff ENNReal NNReal
noncomputable section
universe u v
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false

variable {E : Type u} {M : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  {F : ContinuousFinslerNorm E M}

/-- The original physical hypotheses in dimension at least six produce one
potential and one uniform expected-energy constant for every sample size and
all measurable fractional optima at every bounded probe tilt. -/
theorem exists_finsler_lipschitz_population_uniform_energy
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
      PopulationUniformEnergyBound μ ν (Module.finrank ℝ E - 1)
        (fun x y ↦ (F.lengthEDist x y).toReal - pot y + pot x) C ∧
      ∀ π : Measure (M × M), IsOptimalCoupling edist μ ν π →
        ∃ (T : Type (max u v)) (hT : Fintype T),
          let _inst : Fintype T := hT
          Nonempty (PopulationTypedCostData π μ ν T (Module.finrank ℝ E - 1)
            (fun x y ↦ (F.lengthEDist x y).toReal - pot y + pot x)) := by
  let μ := volM.withDensity (fun x ↦ ENNReal.ofReal (ρ₀ x))
  let ν := volM.withDensity (fun x ↦ ENNReal.ofReal (ρ₁ x))
  let _inst : MetricSpace M := F.metricSpace
  let _instProper : ProperSpace M := F.properSpace_of_complete hcomplete
  obtain ⟨pot, hu, hdata⟩ := exists_finsler_lipschitz_population_typed_cost_data hF hcomplete
    m volM ρ₀ ρ₁ hρ₀ hρ₁ hρ₀nonneg hρ₁nonneg v hv hvnonneg hvolume hA hB hAB hμ hν
  obtain ⟨π, hπ⟩ := exists_isOptimalCoupling_edist_of_compact_carrier μ ν (hA.union hB)
    (hμ.mono fun _ hx ↦ Or.inl hx) (hν.mono fun _ hx ↦ Or.inr hx)
  let _instMapProbability : IsProbabilityMeasure (π.map Prod.fst) :=
    hπ.1.1.symm ▸ inferInstance
  let _instPlanProbability : IsProbabilityMeasure π :=
    Measure.isProbabilityMeasure_of_map Prod.fst
  obtain ⟨T, hT, ⟨D⟩⟩ := hdata π hπ
  let _instT : Fintype T := hT
  let _instMeasurableT : MeasurableSpace (Option T) := ⊤
  obtain ⟨C, hC, hbound⟩ := D.exists_population_uniform_energy_bound (by omega) hπ.1
  exact ⟨pot, C, hu, hC, hbound, hdata⟩

end OTSelector.Reconstruction
