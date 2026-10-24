import OTSelector.Reconstruction.FinslerOriginalSeedComparisonConstruction
import OTSelector.Reconstruction.FinslerPopulationSupportedComparison
import OTSelector.Reconstruction.FinslerOriginalConditionalMoments

/-!
# Simultaneous-label capstone for the raw seed conditional-moments datum

The raw normalized population window law, together with the physical support law and
the two physical chart-density laws, produces at ONE label simultaneously:

* an actual seed with a complete smooth phase-jet comparison (HasActiveSeedComparison),
* both original conditional clock laws of that label as the seed clock laws,
* the common seed support span (automatic from the supported-comparison law),
* and the physical clock density formulas for both colors.

`exists_simultaneous_supported_label` extracts this bundle at a single label from
`PopulationSupportedComparisonLaw`.  `exists_raw_originalSeedConditionalMoments` then
constructs a full `OriginalSeedConditionalMoments` datum at that label from the raw
window/support/density data, using the library producer
`PopulationConditionalWindowLaw.ae_exists_supported_seed_comparison` and the
a.e. conditional-moment construction `PopulationSupportedComparisonLaw.conditional_moments`.
-/

open Set MeasureTheory ProbabilityTheory Filter Topology Manifold Metric
  OTSelector.Geometry
open scoped Topology ContDiff ENNReal

noncomputable section

set_option maxHeartbeats 1600000

namespace OTSelector.Reconstruction

variable {E M Z : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  [StandardBorelSpace M] [Nonempty M]
  [MeasurableSpace Z] [MeasurableEq Z] [MeasurableSpace.CountablySeparated Z]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}

omit [FiniteDimensional ℝ E] [BorelSpace E] [T2Space M] [PreconnectedSpace M]
  [BorelSpace M] [StandardBorelSpace M] [Nonempty M] [MeasurableEq Z]
  [MeasurableSpace.CountablySeparated Z] in
/-- Simultaneous-label datum bundle: one label carrying a complete comparison, the
common seed support span and both physical clock densities for the two conditional
clock laws. -/
theorem exists_simultaneous_supported_label
    {P : ℕ → F.CalibratedSeedWindow u} {a : M → Z}
    {kappa : ∀ j, Measure (P j).seed.covector.ker} {lambda : Measure Z}
    {eta0 eta1 : Measure M} [IsFiniteMeasure eta0] [IsFiniteMeasure eta1]
    {rho0 rho1 : M → ℝ} {v : M → E → ℝ}
    [IsProbabilityMeasure lambda]
    (hlaw : PopulationSupportedComparisonLaw P a kappa lambda eta0 eta1 rho0 rho1 v) :
    ∃ (z : Z) (j : ℕ) (w : (P j).seed.covector.ker) (lo hi : ℝ),
      w ∈ (P j).seed.labels ∧ a ((P j).seed.curve w 0) = z ∧
      HasActiveSeedComparison (P j).seed w ∧
      CommonSeedSupportSpan (P j).seed w
        (condDistrib u a eta0 z) (condDistrib u a eta1 z) lo hi ∧
      PopulationSeedClockDensity (P j).seed w
        ((condDistrib u a eta0 z).map (fun s : ℝ => s - (P j).seed.level))
        rho0 v
        ((populationSeedLabelReference (P j).seed a (kappa j)).rnDeriv
          lambda z).toReal ∧
      PopulationSeedClockDensity (P j).seed w
        ((condDistrib u a eta1 z).map (fun s : ℝ => s - (P j).seed.level))
        rho1 v
        ((populationSeedLabelReference (P j).seed a (kappa j)).rnDeriv
          lambda z).toReal := by
  obtain ⟨z, j, w, lo, hi, hw, hwz, _hrn, _hfin, hcomparison, hspan, hd0, hd1⟩ :=
    exists_of_eventually_of_isProbabilityMeasure hlaw
  exact ⟨z, j, w, lo, hi, hw, hwz, hcomparison, hspan, hd0, hd1⟩

omit [StandardBorelSpace M] [Nonempty M] [MeasurableEq Z] in
/-- The simultaneous-label capstone: at one raw label, a full
`OriginalSeedConditionalMoments` datum is constructed for the seed selected at that
label and the two conditional clock laws of that label. -/
theorem exists_raw_originalSeedConditionalMoments
    {P : ℕ → F.CalibratedSeedWindow u} {a : M → Z}
    {kappa : ∀ j, Measure (P j).seed.covector.ker} {lambda : Measure Z}
    {eta0 eta1 : Measure M} [IsFiniteMeasure eta0] [IsFiniteMeasure eta1]
    {rho0 rho1 : M → ℝ} {v : M → E → ℝ} {vP : ℕ → E → ℝ}
    [IsProbabilityMeasure lambda]
    (hlaw : PopulationConditionalWindowLaw P a kappa lambda eta0 rho0 vP)
    (hsupport : PopulationConditionalSupportLaw (F := F) (u := u) a lambda eta0 eta1)
    (hdensity0 : ∀ j, PopulationSeedChartDensityLaw (P j).seed a (kappa j)
      lambda eta0 rho0 v (P j).seed.level)
    (hdensity1 : ∀ j, PopulationSeedChartDensityLaw (P j).seed a (kappa j)
      lambda eta1 rho1 v (P j).seed.level)
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _instRawCapstoneMetric : MetricSpace M := F.metricSpace
      LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Function.Injective
      (fun x : F.potentialRegularDomain u => (a x.val, u x.val)))
    (horder : let _instRawCapstoneOrder : MetricSpace M := F.metricSpace
      ∀ x ∈ F.potentialRegularDomain u, ∀ y ∈ F.potentialRegularDomain u,
        (a x = a y ∧ u x ≤ u y) ↔ u y - u x = dist x y)
    (hkappa : ∀ j, (kappa j).IsAddHaarMeasure)
    (hrho0 : Continuous rho0) (hrho1 : Continuous rho1)
    (hrho0nonneg : ∀ x, 0 ≤ rho0 x) (hrho1nonneg : ∀ x, 0 ≤ rho1 x)
    (hv : ∀ old, ContinuousOn (v old) (extChartAt 𝓘(ℝ, E) old).target)
    (hv0 : ∀ old, ∀ x ∈ (extChartAt 𝓘(ℝ, E) old).target, 0 ≤ v old x) :
    ∃ (z : Z) (j : ℕ) (w : (P j).seed.covector.ker),
      w ∈ (P j).seed.labels ∧ a ((P j).seed.curve w 0) = z ∧
      Nonempty (OriginalSeedConditionalMoments (P j).seed w
        (condDistrib u a eta0 z) (condDistrib u a eta1 z)) := by
  have hsupported : PopulationSupportedComparisonLaw P a kappa lambda eta0 eta1
      rho0 rho1 v :=
    hlaw.ae_exists_supported_seed_comparison hsupport hdensity0 hdensity1 hF
      hcomplete hu ha hinj horder hkappa
  have hmoment : PopulationConditionalMomentLaw P a lambda eta0 eta1 :=
    hsupported.conditional_moments hF hrho0 hrho1 hrho0nonneg hrho1nonneg hv hv0
  obtain ⟨z, j, w, hw, hwz, hne⟩ :=
    exists_of_eventually_of_isProbabilityMeasure hmoment
  exact ⟨z, j, w, hw, hwz, hne⟩

end OTSelector.Reconstruction

end
