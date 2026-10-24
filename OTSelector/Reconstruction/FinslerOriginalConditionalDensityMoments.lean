import OTSelector.Reconstruction.FinslerOriginalConditionalMoments

/-! Keep the actual physical density formulas when producing original moment witnesses. -/
open Set Matrix Module Manifold MeasureTheory ProbabilityTheory
open scoped Topology ContDiff ENNReal
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Geometry ContinuousFinslerNorm
set_option backward.isDefEq.respectTransparency false

variable {E M Z : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [MeasurableSpace M] [MeasurableSpace Z]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}

omit [BorelSpace E] in
/-- The original supported comparison law produces one actual moment witness
while retaining BOTH whole active-chart physical conditional densities and
their same strictly positive finite original normalization. These formulas
remain available for sharp focal birth estimates, beyond the integrated moments. -/
theorem PopulationSupportedComparisonLaw.conditional_moments_with_physical_densities
    {P : ℕ → F.CalibratedSeedWindow u} {a : M → Z}
    {κ : ∀ j, Measure (P j).seed.covector.ker} {lambda : Measure Z}
    {η₀ η₁ : Measure M} [IsFiniteMeasure η₀] [IsFiniteMeasure η₁]
    {ρ₀ ρ₁ : M → ℝ} {v : M → E → ℝ}
    (hlaw : PopulationSupportedComparisonLaw P a κ lambda η₀ η₁ ρ₀ ρ₁ v)
    (hF : F.IsSmoothStronglyConvex)
    (hρ₀ : Continuous ρ₀) (hρ₁ : Continuous ρ₁)
    (hρ₀nonneg : ∀ x, 0 ≤ ρ₀ x) (hρ₁nonneg : ∀ x, 0 ≤ ρ₁ x)
    (hv : ∀ old, ContinuousOn (v old) (extChartAt 𝓘(ℝ, E) old).target)
    (hv0 : ∀ old, ∀ x ∈ (extChartAt 𝓘(ℝ, E) old).target, 0 ≤ v old x) :
    ∀ᵐ z ∂lambda, ∃ (j : ℕ) (w : (P j).seed.covector.ker),
      w ∈ (P j).seed.labels ∧ a ((P j).seed.curve w 0) = z ∧
      ∃ _D : OriginalSeedConditionalMoments (P j).seed w
          (condDistrib u a η₀ z) (condDistrib u a η₁ z),
        (populationSeedLabelReference (P j).seed a (κ j)).rnDeriv lambda z ≠ 0 ∧
        (populationSeedLabelReference (P j).seed a (κ j)).rnDeriv lambda z < (∞ : ℝ≥0∞) ∧
        PopulationSeedClockDensity (P j).seed w
          ((condDistrib u a η₀ z).map (fun s : ℝ ↦ s - (P j).seed.level)) ρ₀ v
          ((populationSeedLabelReference (P j).seed a (κ j)).rnDeriv lambda z).toReal ∧
        PopulationSeedClockDensity (P j).seed w
          ((condDistrib u a η₁ z).map (fun s : ℝ ↦ s - (P j).seed.level)) ρ₁ v
          ((populationSeedLabelReference (P j).seed a (κ j)).rnDeriv lambda z).toReal := by
  filter_upwards [hlaw] with z hz
  obtain ⟨j, w, lo, hi, hw, hwz, hc0, hcfin, hcomparison, hspan, hdensity₀, hdensity₁⟩ := hz
  obtain ⟨D⟩ := originalSeedConditionalMoments_of_supported_comparison hF hw hcomparison
    hspan hρ₀ hρ₁ hρ₀nonneg hρ₁nonneg hv hv0 hdensity₀ hdensity₁
  exact ⟨j, w, hw, hwz, D, hc0, hcfin, hdensity₀, hdensity₁⟩

end OTSelector.Reconstruction
