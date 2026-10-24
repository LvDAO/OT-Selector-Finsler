import OTSelector.Reconstruction.FinslerOriginalRawSeedConditionalMoments
import OTSelector.Reconstruction.FinslerOriginalPoissonClockSupport
import OTSelector.Reconstruction.FinslerOriginalClockSupportBounds
import OTSelector.Reconstruction.FinslerPopulationConditionalSeparation

/-!
# Bundled raw seed conditional-moments datum with atomless compact clock laws

The raw capstone `exists_raw_originalSeedConditionalMoments` constructs the full
conditional-moments datum at one label but keeps the atomless compact clock law and
the `ConditionalClockSupportBounds` separate.  This file bundles them:

* `ae_atomless_clock_of_windowLaw`: the conditional clock law of an input is almost
  surely atomless with compact support in an explicit compact physical set;
* `exists_conditionalClockSupportBounds_of_raw_input_lambda`: the conditional clock
  support bounds of the two inputs hold almost surely on the label law itself;
* `exists_bundled_raw_seed_datum`: at ONE label, a single bundle carrying the actual
  seed, its complete comparison, both physical densities, the atomless compact clock
  law, the conditional clock support bounds, both finite square moments, and a full
  `OriginalSeedConditionalMoments` datum for that same seed.
-/

open Set MeasureTheory ProbabilityTheory Filter Topology Manifold Metric
  OTSelector.Geometry
open scoped Topology ContDiff ENNReal

noncomputable section

set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace OTSelector.Reconstruction

variable {E M Z : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  [StandardBorelSpace M] [Nonempty M]
  [MeasurableSpace Z] [MeasurableEq Z] [MeasurableSpace.CountablySeparated Z]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}

/-- The source conditional clock law is almost surely atomless with compact support
in an explicit compact physical set. -/
theorem ae_atomless_clock_of_windowLaw
    {P : ℕ → F.CalibratedSeedWindow u} {a : M → Z}
    {kappa : ∀ j, Measure (P j).seed.covector.ker} {lambda : Measure Z}
    {eta : Measure M} [IsFiniteMeasure eta] {rho : M → ℝ} {v : ℕ → E → ℝ}
    (hlaw : PopulationConditionalWindowLaw P a kappa lambda eta rho v)
    (ha : Measurable a)
    (hu : let _instClockMetric : MetricSpace M := F.metricSpace
      LipschitzWith 1 u)
    {A : Set M} (hA : IsCompact A) (hEtaA : ∀ᵐ x ∂eta, x ∈ A) :
    ∀ᵐ z ∂lambda, NullSingletonClass (condDistrib u a eta z) ∧
      IsCompact (condDistrib u a eta z).support ∧
      (condDistrib u a eta z).support ⊆ u '' A := by
  filter_upwards [hlaw.ae_compact_atomless_clock ha hu hA hEtaA] with z hz
  exact ⟨hz.1, hz.2.1, hz.2.2.1⟩

/-- The conditional clock support bounds of the two original inputs hold almost
surely on the label law itself. -/
theorem exists_conditionalClockSupportBounds_of_raw_input_lambda
    {eta0 eta1 : Measure M} [IsFiniteMeasure eta0] [IsFiniteMeasure eta1]
    {a : M → Z} (ha : Measurable a) (hbalance : eta0.map a = eta1.map a)
    {u : M → ℝ} (hu : Continuous u) {A Bs N : Set M}
    (hA : IsCompact A) (hBs : IsCompact Bs) (hAB : Disjoint A Bs)
    (hN : MeasurableSet N)
    (hA0 : ∀ᵐ x ∂eta0, x ∈ A) (hB1 : ∀ᵐ x ∂eta1, x ∈ Bs)
    (hN0 : ∀ᵐ x ∂eta0, x ∈ N) (hN1 : ∀ᵐ x ∂eta1, x ∈ N)
    (horder : let _instRawClockOrder : MetricSpace M := F.metricSpace
      ∀ x ∈ N, ∀ y ∈ N, (a x = a y ∧ u x ≤ u y) ↔ u y - u x = dist x y)
    {lambda : Measure Z} (hlabel : eta0.map a = lambda) :
    ∃ delta > 0, ∃ D : ℝ,
      ∀ᵐ z ∂lambda,
        ConditionalClockSupportBounds (condDistrib u a eta0 z)
          (condDistrib u a eta1 z) delta D := by
  let _instRawClockOrder : MetricSpace M := F.metricSpace
  obtain ⟨delta, hdelta, hlaw⟩ := exists_population_conditional_separation eta0 eta1
    ha hbalance hu hA hBs hAB hN hA0 hB1 hN0 hN1 horder
  refine ⟨delta, hdelta, Metric.diam (A ∪ Bs), ?_⟩
  rw [← hlabel]
  exact hlaw

/-- Simultaneous-label bundle: one label carrying the actual seed, its complete
comparison, both physical densities, the atomless compact source clock law, the
conditional clock support bounds, both finite square moments, and a full conditional
moments datum for the same seed. -/
theorem exists_bundled_raw_seed_datum
    {P : ℕ → F.CalibratedSeedWindow u} {a : M → Z}
    {kappa : ∀ j, Measure (P j).seed.covector.ker} {lambda : Measure Z}
    {eta0 eta1 : Measure M} [IsFiniteMeasure eta0] [IsFiniteMeasure eta1]
    {rho0 rho1 : M → ℝ} {v : M → E → ℝ}
    [IsProbabilityMeasure lambda]
    (hsupported : PopulationSupportedComparisonLaw P a kappa lambda eta0 eta1
      rho0 rho1 v)
    (hF : F.IsSmoothStronglyConvex)
    (hrho0 : Continuous rho0) (hrho1 : Continuous rho1)
    (hrho0nonneg : ∀ x, 0 ≤ rho0 x) (hrho1nonneg : ∀ x, 0 ≤ rho1 x)
    (hv : ∀ old, ContinuousOn (v old) (extChartAt 𝓘(ℝ, E) old).target)
    (hv0 : ∀ old, ∀ x ∈ (extChartAt 𝓘(ℝ, E) old).target, 0 ≤ v old x)
    {A : Set M} (_hA : IsCompact A)
    (hatomA : ∀ᵐ z ∂lambda, NullSingletonClass (condDistrib u a eta0 z) ∧
      IsCompact (condDistrib u a eta0 z).support ∧
      (condDistrib u a eta0 z).support ⊆ u '' A)
    {delta D : ℝ}
    (hbounds : ∀ᵐ z ∂lambda,
      ConditionalClockSupportBounds (condDistrib u a eta0 z)
        (condDistrib u a eta1 z) delta D) :
    ∃ (z : Z) (j : ℕ) (w : (P j).seed.covector.ker),
      w ∈ (P j).seed.labels ∧ a ((P j).seed.curve w 0) = z ∧
      HasActiveSeedComparison (P j).seed w ∧
      NullSingletonClass (condDistrib u a eta0 z) ∧
      IsCompact (condDistrib u a eta0 z).support ∧
      ConditionalClockSupportBounds (condDistrib u a eta0 z)
        (condDistrib u a eta1 z) delta D ∧
      Integrable (fun t : ℝ => t ^ 2) (condDistrib u a eta0 z) ∧
      Integrable (fun t : ℝ => t ^ 2) (condDistrib u a eta1 z) ∧
      Nonempty (OriginalSeedConditionalMoments (P j).seed w
        (condDistrib u a eta0 z) (condDistrib u a eta1 z)) := by
  have hAll : ∀ᵐ z ∂lambda,
      ((∃ (j : ℕ) (w : (P j).seed.covector.ker) (lo hi : ℝ),
          w ∈ (P j).seed.labels ∧ a ((P j).seed.curve w 0) = z ∧
          (populationSeedLabelReference (P j).seed a (kappa j)).rnDeriv
            lambda z ≠ 0 ∧
          (populationSeedLabelReference (P j).seed a (kappa j)).rnDeriv
            lambda z < (∞ : ℝ≥0∞) ∧
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
              lambda z).toReal) ∧
        (NullSingletonClass (condDistrib u a eta0 z) ∧
          IsCompact (condDistrib u a eta0 z).support ∧
          (condDistrib u a eta0 z).support ⊆ u '' A) ∧
        ConditionalClockSupportBounds (condDistrib u a eta0 z)
          (condDistrib u a eta1 z) delta D) := by
    filter_upwards [hsupported, hatomA, hbounds] with z hz ha hb
    exact ⟨hz, ha, hb⟩
  obtain ⟨z, hsup, hatom, hbnd⟩ :=
    exists_of_eventually_of_isProbabilityMeasure hAll
  obtain ⟨j, w, lo, hi, hw, hwz, _hrn, _hfin, hcomparison, hspan, hd0, hd1⟩ := hsup
  have hdatum := originalSeedConditionalMoments_of_supported_comparison hF hw
    hcomparison hspan hrho0 hrho1 hrho0nonneg hrho1nonneg hv hv0 hd0 hd1
  haveI : IsProbabilityMeasure (condDistrib u a eta0 z) := inferInstance
  haveI : IsProbabilityMeasure (condDistrib u a eta1 z) := inferInstance
  have hmom0 : Integrable (fun t : ℝ => t ^ 2) (condDistrib u a eta0 z) :=
    integrable_sq_of_compact_support hatom.2.1 (measure_compl_support_eq_zero _)
  have hmom1 : Integrable (fun t : ℝ => t ^ 2) (condDistrib u a eta1 z) :=
    integrable_sq_of_compact_support hbnd.target_compact
      (measure_compl_support_eq_zero _)
  exact ⟨z, j, w, hw, hwz, hcomparison, hatom.1, hatom.2.1, hbnd, hmom0, hmom1,
    hdatum⟩

end OTSelector.Reconstruction

end
