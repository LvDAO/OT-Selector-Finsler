import OTSelector.Reconstruction.FinslerPopulationMomentAtlas
import OTSelector.Reconstruction.FinslerPopulationWholePairTypes

/-!
# Original physical populations produce the complete finite matching data

One original potential and label system are retained for the entire optimal face.
Every optimal coupling supplies actual finite RN types, common cube coordinates
and the original distance cost bounds. All geometric and conditional data come
from the physical populations and their chart volume densities.
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

/-- The original whole-face representation produces calibration and finite matching
data for every original optimizer, using its unchanged potential and labels. -/
theorem exists_populationTypedCostData_of_original_optimal_face
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    {pot : M → ℝ}
    (hu : let _inst : MetricSpace M := F.metricSpace; LipschitzWith 1 pot)
    {a : M → (ℚ → M)} (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain pot ↦ (a x.val, pot x.val)))
    (horder : let _inst : MetricSpace M := F.metricSpace
      ∀ x ∈ F.potentialRegularDomain pot, ∀ y ∈ F.potentialRegularDomain pot,
        (a x = a y ∧ pot x ≤ pot y) ↔ pot y - pot x = dist x y)
    {A B : Set M} (hA : IsCompact A) (hB : IsCompact B) (hAB : Disjoint A B)
    {μ ν : Measure M} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμA : ∀ᵐ x ∂μ, x ∈ A) (hνB : ∀ᵐ y ∂ν, y ∈ B)
    (hμreg : ∀ᵐ x ∂μ, x ∈ F.potentialRegularDomain pot)
    (hνreg : ∀ᵐ y ∂ν, y ∈ F.potentialRegularDomain pot) :
    let _inst : MetricSpace M := F.metricSpace
    let _instProper : ProperSpace M := F.properSpace_of_complete hcomplete
    let _instBorel : StandardBorelSpace M := inferInstance
    let _instNonempty : Nonempty M := nonempty_of_isProbabilityMeasure μ
    ∀ (_hface : ∀ π : Measure (M × M), IsOptimalCoupling edist μ ν π ↔
      ∃ k : Kernel (ℚ → M) (M × M), IsMarkovKernel k ∧ k ∘ₘ μ.map a = π ∧
        ∀ᵐ z ∂μ.map a, Vlasov.IsCoupling (k z)
          (condDistrib id a μ z) (condDistrib id a ν z) ∧
          ∀ᵐ p ∂k z, p.1 ∈ F.potentialRegularDomain pot ∧
            p.2 ∈ F.potentialRegularDomain pot ∧ a p.1 = a p.2 ∧ pot p.1 ≤ pot p.2)
      (π : Measure (M × M)), IsOptimalCoupling edist μ ν π →
      ∃ (T : Type (max u v)) (hT : Fintype T),
        let _inst : Fintype T := hT
        Nonempty (PopulationTypedCostData π μ ν T (Module.finrank ℝ E - 1)
          (fun x y ↦ (F.lengthEDist x y).toReal - pot y + pot x)) := by
  let _inst : MetricSpace M := F.metricSpace
  let _instProper : ProperSpace M := F.properSpace_of_complete hcomplete
  let _instBorel : StandardBorelSpace M := inferInstance
  let _instNonempty : Nonempty M := nonempty_of_isProbabilityMeasure μ
  dsimp only
  intro hface π hπ
  have _instMapProbability : IsProbabilityMeasure (π.map Prod.fst) :=
    hπ.1.1.symm ▸ inferInstance
  have _instPlanProbability : IsProbabilityMeasure π :=
    Measure.isProbabilityMeasure_of_map Prod.fst
  obtain ⟨k, _, hcomp, hsupp⟩ := (hface π).mp hπ
  have hcalset : MeasurableSet {p : M × M | pot p.2 - pot p.1 = dist p.1 p.2} :=
    measurableSet_eq_fun
      ((hu.continuous.measurable.comp measurable_snd).sub
        (hu.continuous.measurable.comp measurable_fst))
      (continuous_fst.dist continuous_snd).measurable
  have hcal : ∀ᵐ p ∂π, pot p.2 - pot p.1 = dist p.1 p.2 := by
    rw [← hcomp]
    apply Measure.ae_comp_of_ae_ae hcalset
    filter_upwards [hsupp] with z hz
    exact hz.2.mono fun p hp ↦
      (horder p.1 hp.1 p.2 hp.2.1).mp ⟨hp.2.2.1, hp.2.2.2⟩
  exact exists_populationTypedCostData_of_calibrated_coupling hF hcomplete hu ha hinj
    horder hA hB hAB hμA hνB hμreg hνreg π hπ.1 hcal

/-- Original nonnegative Lipschitz physical probabilities construct a single optimal
potential whose entire optimal face admits finite actual marked matching data.
The bounds are fixed before the sample size; no geometric label, calibration,
conditional-law or sample-cost hypothesis is supplied. -/
theorem exists_finsler_lipschitz_population_typed_cost_data
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (m : Measure E) [m.IsAddHaarMeasure] (ωM : Measure M)
    (ρ₀ ρ₁ : M → ℝ) {K₀ K₁ : ℝ≥0}
    (hρ₀ : let _inst : MetricSpace M := F.metricSpace; LipschitzWith K₀ ρ₀)
    (hρ₁ : let _inst : MetricSpace M := F.metricSpace; LipschitzWith K₁ ρ₁)
    (hρ₀nonneg : ∀ x, 0 ≤ ρ₀ x) (hρ₁nonneg : ∀ x, 0 ≤ ρ₁ x)
    [IsProbabilityMeasure (ωM.withDensity (fun x ↦ ENNReal.ofReal (ρ₀ x)))]
    [IsProbabilityMeasure (ωM.withDensity (fun x ↦ ENNReal.ofReal (ρ₁ x)))]
    (v : M → E → ℝ)
    (hv : ∀ old, ContinuousOn (v old) (extChartAt 𝓘(ℝ, E) old).target)
    (hvnonneg : ∀ old, ∀ y ∈ (extChartAt 𝓘(ℝ, E) old).target, 0 ≤ v old y)
    (hvolume : ∀ old : M, let χ := extChartAt 𝓘(ℝ, E) old
      (ωM.restrict χ.source).map χ = (m.restrict χ.target).withDensity
        (fun y ↦ ENNReal.ofReal (v old y)))
    {A B : Set M} (hA : IsCompact A) (hB : IsCompact B) (hAB : Disjoint A B)
    (hμ : ∀ᵐ x ∂ωM.withDensity (fun x ↦ ENNReal.ofReal (ρ₀ x)), x ∈ A)
    (hν : ∀ᵐ x ∂ωM.withDensity (fun x ↦ ENNReal.ofReal (ρ₁ x)), x ∈ B) :
    let μ := ωM.withDensity (fun x ↦ ENNReal.ofReal (ρ₀ x))
    let ν := ωM.withDensity (fun x ↦ ENNReal.ofReal (ρ₁ x))
    let _inst : MetricSpace M := F.metricSpace
    ∃ pot : M → ℝ, LipschitzWith 1 pot ∧
      ∀ π : Measure (M × M), IsOptimalCoupling edist μ ν π →
        ∃ (T : Type (max u v)) (hT : Fintype T),
          let _inst : Fintype T := hT
          Nonempty (PopulationTypedCostData π μ ν T (Module.finrank ℝ E - 1)
            (fun x y ↦ (F.lengthEDist x y).toReal - pot y + pot x)) := by
  let μ := ωM.withDensity (fun x ↦ ENNReal.ofReal (ρ₀ x))
  let ν := ωM.withDensity (fun x ↦ ENNReal.ofReal (ρ₁ x))
  let _inst : MetricSpace M := F.metricSpace
  let _instProper : ProperSpace M := F.properSpace_of_complete hcomplete
  let _instBorel : StandardBorelSpace M := inferInstance
  let _instNonempty : Nonempty M := nonempty_of_isProbabilityMeasure μ
  obtain ⟨pot, a, hu, _, hμreg, hνreg, ha, hinj, horder, _, hface, _⟩ :=
    exists_finsler_lipschitz_population_moment_atlas hF hcomplete m ωM ρ₀ ρ₁ hρ₀ hρ₁
      hρ₀nonneg hρ₁nonneg v hv hvnonneg hvolume hA hB hAB hμ hν
  exact ⟨pot, hu, exists_populationTypedCostData_of_original_optimal_face hF hcomplete
    hu ha hinj horder hA hB hAB hμ hν hμreg hνreg hface⟩

end OTSelector.Reconstruction
