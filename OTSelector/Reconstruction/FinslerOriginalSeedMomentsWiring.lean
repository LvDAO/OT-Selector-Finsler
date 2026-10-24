import OTSelector.Reconstruction.AeClockLawProbability

/-!
# Wiring the a.e. capstone into the seed-moments consumer

`OrderCouplingConstruction.ae_exists_boundedSecondMomentClass_of_support_threshold` is
the only consumer of `ae_exists_boundedSecondMomentClass_of_raw`; it assumed the raw
coupling hypothesis and derived it from a support-threshold condition via the product
coupling.  This file replaces that route by the discharged chain:

* `ae_exists_boundedSecondMomentClass_of_population_cdf_dominance`: the seed-moments
  consumer theorem with only a.e. CDF dominance of the actual population clock laws
  as modeled input; the a.e. probability of the conditional laws is derived, and the
  order coupling is derived from cdf dominance (`QuantilePushforward`);
* `ae_exists_boundedSecondMomentClass_of_population_support_threshold`: the same
  consumer theorem with a.e. support-threshold separation as the only input, now
  routed through the discharged capstone instead of the raw capstone;
* `exists_boundedSecondMomentClass_of_cdf_dominance` and
  `exists_boundedSecondMomentClass_of_population_support_threshold`: the pointwise
  single-label consumer form obtained from the a.e. statements on a probability
  label law (the form the finite-reference chain consumes at one label).

Remaining gap: the downstream marked-stationary consumers
(`MarkedStationaryValueLegal*`) take a legal weighted stationary Poisson matching `Q`
instead of constructing it, so wiring those needs the per-label truncation/cut data
that the seed-moments capstone does not provide; only the population consumer form is
closed here.
-/

open Set MeasureTheory ProbabilityTheory Filter Topology Manifold Metric Module
  OTSelector.Geometry OTSelector.PointProcess
  OTSelector.PointProcess.StationaryForwardMatching OTSelector.Probability
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

/-- The seed-moments consumer theorem with only a.e. CDF dominance of the actual
population clock laws as modeled input.  The a.e. probability of those laws is derived
(`condDistrib_isProbabilityMeasure`) and the order coupling is derived from cdf
dominance (`exists_orderCoupling_of_stochastic_dominance`), so this consumes the
discharged capstone rather than `ae_exists_boundedSecondMomentClass_of_raw`. -/
theorem ae_exists_boundedSecondMomentClass_of_population_cdf_dominance
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
    {A : Set M} (hA : IsCompact A)
    (hatomA : ∀ᵐ z ∂lambda, NullSingletonClass (condDistrib u a eta0 z) ∧
      IsCompact (condDistrib u a eta0 z).support ∧
      (condDistrib u a eta0 z).support ⊆ u '' A)
    {delta diameter : ℝ} (hdelta : 0 < delta)
    (hboundsAE : ∀ᵐ z ∂lambda,
      ConditionalClockSupportBounds (condDistrib u a eta0 z)
        (condDistrib u a eta1 z) delta diameter)
    (hdom : ∀ᵐ z ∂lambda, ∀ t : ℝ,
      cdf (condDistrib u a eta1 z) t ≤ cdf (condDistrib u a eta0 z) t)
    (hq : ∀ j, 4 < finrank ℝ (P j).seed.covector.ker)
    (g : ℝ → ℝ → ℝ) (hg : Measurable (Function.uncurry g)) {G : ℝ}
    (hgb : ∀ a b, |g a b| ≤ G) :
    ∀ᵐ z ∂lambda,
      ∃ (j : ℕ) (w : (P j).seed.covector.ker)
        (datum : OriginalSeedConditionalMoments (P j).seed w
          (condDistrib u a eta0 z) (condDistrib u a eta1 z))
        (Q : LegalWeightedStationaryPoissonMatching
          (finrank ℝ (P j).seed.covector.ker)
          (condDistrib u a eta0 z) (condDistrib u a eta1 z)
          (datum.originalFocalKinetic delta) g) (Bnd : ℝ),
        0 ≤ Bnd ∧
        (boundedSecondMomentClass
          (α := (legalMarkedJointPalm (finrank ℝ (P j).seed.covector.ker) Q.law).map
            carrierRecodePair |>.map (fun p => p.1.2))
          (β := (legalMarkedJointPalm (finrank ℝ (P j).seed.covector.ker) Q.law).map
            carrierRecodePair |>.map (fun p => p.2.2)) Bnd).Nonempty := by
  exact ae_exists_boundedSecondMomentClass_of_cdf_dominance hsupported hF hrho0 hrho1
    hrho0nonneg hrho1nonneg hv hv0 hA hatomA hdelta hboundsAE hdom hq g hg hgb

/-- The seed-moments consumer theorem with a.e. support-threshold separation of the
clock laws as the only input, routed through the discharged capstone. -/
theorem ae_exists_boundedSecondMomentClass_of_population_support_threshold
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
    {A : Set M} (hA : IsCompact A)
    (hatomA : ∀ᵐ z ∂lambda, NullSingletonClass (condDistrib u a eta0 z) ∧
      IsCompact (condDistrib u a eta0 z).support ∧
      (condDistrib u a eta0 z).support ⊆ u '' A)
    {delta diameter : ℝ} (hdelta : 0 < delta)
    (hboundsAE : ∀ᵐ z ∂lambda,
      ConditionalClockSupportBounds (condDistrib u a eta0 z)
        (condDistrib u a eta1 z) delta diameter)
    (hthreshold : ∀ᵐ z ∂lambda, ∃ c : ℝ,
      (condDistrib u a eta0 z).support ⊆ Set.Iic c ∧
      (condDistrib u a eta1 z).support ⊆ Set.Ici c)
    (hq : ∀ j, 4 < finrank ℝ (P j).seed.covector.ker)
    (g : ℝ → ℝ → ℝ) (hg : Measurable (Function.uncurry g)) {G : ℝ}
    (hgb : ∀ a b, |g a b| ≤ G) :
    ∀ᵐ z ∂lambda,
      ∃ (j : ℕ) (w : (P j).seed.covector.ker)
        (datum : OriginalSeedConditionalMoments (P j).seed w
          (condDistrib u a eta0 z) (condDistrib u a eta1 z))
        (Q : LegalWeightedStationaryPoissonMatching
          (finrank ℝ (P j).seed.covector.ker)
          (condDistrib u a eta0 z) (condDistrib u a eta1 z)
          (datum.originalFocalKinetic delta) g) (Bnd : ℝ),
        0 ≤ Bnd ∧
        (boundedSecondMomentClass
          (α := (legalMarkedJointPalm (finrank ℝ (P j).seed.covector.ker) Q.law).map
            carrierRecodePair |>.map (fun p => p.1.2))
          (β := (legalMarkedJointPalm (finrank ℝ (P j).seed.covector.ker) Q.law).map
            carrierRecodePair |>.map (fun p => p.2.2)) Bnd).Nonempty := by
  refine ae_exists_boundedSecondMomentClass_of_population_cdf_dominance hsupported hF
    hrho0 hrho1 hrho0nonneg hrho1nonneg hv hv0 hA hatomA hdelta hboundsAE ?_ hq g hg hgb
  filter_upwards [hthreshold] with z hz
  obtain ⟨c, h0, h1⟩ := hz
  haveI : IsProbabilityMeasure (condDistrib u a eta0 z) :=
    condDistrib_isProbabilityMeasure (u := u) (a := a) eta0 z
  haveI : IsProbabilityMeasure (condDistrib u a eta1 z) :=
    condDistrib_isProbabilityMeasure (u := u) (a := a) eta1 z
  exact cdf_le_of_support_threshold h0 h1

/-- Single-label consumer form: from a.e. CDF dominance and a probability label law
there is an actual label carrying the seed conditional-moments datum, the legal
stationary matching and a nonnegative bounded second-moment class. -/
theorem exists_boundedSecondMomentClass_of_cdf_dominance
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
    {A : Set M} (hA : IsCompact A)
    (hatomA : ∀ᵐ z ∂lambda, NullSingletonClass (condDistrib u a eta0 z) ∧
      IsCompact (condDistrib u a eta0 z).support ∧
      (condDistrib u a eta0 z).support ⊆ u '' A)
    {delta diameter : ℝ} (hdelta : 0 < delta)
    (hboundsAE : ∀ᵐ z ∂lambda,
      ConditionalClockSupportBounds (condDistrib u a eta0 z)
        (condDistrib u a eta1 z) delta diameter)
    (hdom : ∀ᵐ z ∂lambda, ∀ t : ℝ,
      cdf (condDistrib u a eta1 z) t ≤ cdf (condDistrib u a eta0 z) t)
    (hq : ∀ j, 4 < finrank ℝ (P j).seed.covector.ker)
    (g : ℝ → ℝ → ℝ) (hg : Measurable (Function.uncurry g)) {G : ℝ}
    (hgb : ∀ a b, |g a b| ≤ G) :
    ∃ (z : Z) (j : ℕ) (w : (P j).seed.covector.ker)
      (datum : OriginalSeedConditionalMoments (P j).seed w
        (condDistrib u a eta0 z) (condDistrib u a eta1 z))
      (Q : LegalWeightedStationaryPoissonMatching
        (finrank ℝ (P j).seed.covector.ker)
        (condDistrib u a eta0 z) (condDistrib u a eta1 z)
        (datum.originalFocalKinetic delta) g) (Bnd : ℝ),
      0 ≤ Bnd ∧
      (boundedSecondMomentClass
        (α := (legalMarkedJointPalm (finrank ℝ (P j).seed.covector.ker) Q.law).map
          carrierRecodePair |>.map (fun p => p.1.2))
        (β := (legalMarkedJointPalm (finrank ℝ (P j).seed.covector.ker) Q.law).map
          carrierRecodePair |>.map (fun p => p.2.2)) Bnd).Nonempty :=
  exists_of_eventually_of_isProbabilityMeasure
    (ae_exists_boundedSecondMomentClass_of_population_cdf_dominance hsupported hF
      hrho0 hrho1 hrho0nonneg hrho1nonneg hv hv0 hA hatomA hdelta hboundsAE hdom hq g hg hgb)

/-- Single-label consumer form from a.e. support-threshold separation. -/
theorem exists_boundedSecondMomentClass_of_population_support_threshold
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
    {A : Set M} (hA : IsCompact A)
    (hatomA : ∀ᵐ z ∂lambda, NullSingletonClass (condDistrib u a eta0 z) ∧
      IsCompact (condDistrib u a eta0 z).support ∧
      (condDistrib u a eta0 z).support ⊆ u '' A)
    {delta diameter : ℝ} (hdelta : 0 < delta)
    (hboundsAE : ∀ᵐ z ∂lambda,
      ConditionalClockSupportBounds (condDistrib u a eta0 z)
        (condDistrib u a eta1 z) delta diameter)
    (hthreshold : ∀ᵐ z ∂lambda, ∃ c : ℝ,
      (condDistrib u a eta0 z).support ⊆ Set.Iic c ∧
      (condDistrib u a eta1 z).support ⊆ Set.Ici c)
    (hq : ∀ j, 4 < finrank ℝ (P j).seed.covector.ker)
    (g : ℝ → ℝ → ℝ) (hg : Measurable (Function.uncurry g)) {G : ℝ}
    (hgb : ∀ a b, |g a b| ≤ G) :
    ∃ (z : Z) (j : ℕ) (w : (P j).seed.covector.ker)
      (datum : OriginalSeedConditionalMoments (P j).seed w
        (condDistrib u a eta0 z) (condDistrib u a eta1 z))
      (Q : LegalWeightedStationaryPoissonMatching
        (finrank ℝ (P j).seed.covector.ker)
        (condDistrib u a eta0 z) (condDistrib u a eta1 z)
        (datum.originalFocalKinetic delta) g) (Bnd : ℝ),
      0 ≤ Bnd ∧
      (boundedSecondMomentClass
        (α := (legalMarkedJointPalm (finrank ℝ (P j).seed.covector.ker) Q.law).map
          carrierRecodePair |>.map (fun p => p.1.2))
        (β := (legalMarkedJointPalm (finrank ℝ (P j).seed.covector.ker) Q.law).map
          carrierRecodePair |>.map (fun p => p.2.2)) Bnd).Nonempty :=
  exists_of_eventually_of_isProbabilityMeasure
    (ae_exists_boundedSecondMomentClass_of_population_support_threshold hsupported hF
      hrho0 hrho1 hrho0nonneg hrho1nonneg hv hv0 hA hatomA hdelta hboundsAE hthreshold
      hq g hg hgb)

end OTSelector.Reconstruction

end
