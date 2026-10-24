import OTSelector.Reconstruction.AeOrderCoupling

/-!
# Physical derivation of the a.e. clock law probability and cdf dominance

This file closes the two modeled inputs of `AeOrderCoupling.lean`.

(a) The conditional clock laws are probability measures for *every* label:
`condDistrib` of a finite population law is a Markov kernel by Mathlib
(`IsMarkovKernel (condDistrib Y X μ)`), so no mass-normalisation hypothesis is
needed and the a.e. probability input is fully derived.

(b) Cdf dominance of the two conditional clock laws is a genuine distributional
input in the general case: `ConditionalClockSupportBounds` only separates the
supports without ordering them, and the formalised density law
`PopulationSeedChartDensityLaw` identifies the clock law only on the active chart
part `U`, so a pointwise comparison of the `ρ` weights (which would give density,
hence cdf, dominance on `U`) does not control the complementary mass and hence
does not give cdf dominance of the full clock laws.  The derivable case proved
here is threshold separation of the supports.  No clock-tilt monotonicity is
formalised in this repository, so the tilt-order route is not available.

The capstone `ae_exists_boundedSecondMomentClass_of_cdf_dominance` therefore has
a.e. cdf dominance as its only modeled input, and
`ae_exists_boundedSecondMomentClass_of_ae_support_threshold` derives even that
from a.e. threshold separation of the clock supports.
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

/-- Every fibre of the conditional clock law is a probability measure: the regular
conditional distribution of a finite population law is a Markov kernel. -/
theorem condDistrib_isProbabilityMeasure {M Z : Type*} [MeasurableSpace M]
    [MeasurableSpace Z] {u : M → ℝ} {a : M → Z} (eta : Measure M)
    [IsFiniteMeasure eta] (z : Z) :
    IsProbabilityMeasure (condDistrib u a eta z) :=
  inferInstance

/-- A.e. version of `condDistrib_isProbabilityMeasure`. -/
theorem ae_condDistrib_isProbabilityMeasure {M Z : Type*} [MeasurableSpace M]
    [MeasurableSpace Z] {u : M → ℝ} {a : M → Z} (eta : Measure M)
    [IsFiniteMeasure eta] (lambda : Measure Z) :
    ∀ᵐ z ∂lambda, IsProbabilityMeasure (condDistrib u a eta z) :=
  Filter.Eventually.of_forall fun z => condDistrib_isProbabilityMeasure eta z

/-- A.e. cdf dominance from a.e. threshold separation of the two supports. -/
theorem ae_cdf_le_of_ae_support_threshold
    {Z : Type*} [MeasurableSpace Z] {lambda : Measure Z}
    {s0 s1 : Z → Measure ℝ} {c : Z → ℝ}
    (hprob0 : ∀ᵐ z ∂lambda, IsProbabilityMeasure (s0 z))
    (hprob1 : ∀ᵐ z ∂lambda, IsProbabilityMeasure (s1 z))
    (hthreshold : ∀ᵐ z ∂lambda,
      (s0 z).support ⊆ Set.Iic (c z) ∧ (s1 z).support ⊆ Set.Ici (c z)) :
    ∀ᵐ z ∂lambda, ∀ t : ℝ, cdf (s1 z) t ≤ cdf (s0 z) t := by
  filter_upwards [hprob0, hprob1, hthreshold] with z h0 h1 hz
  haveI : IsProbabilityMeasure (s0 z) := h0
  haveI : IsProbabilityMeasure (s1 z) := h1
  exact cdf_le_of_support_threshold hz.1 hz.2

variable {E M Z : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  [StandardBorelSpace M] [Nonempty M]
  [MeasurableSpace Z] [MeasurableEq Z] [MeasurableSpace.CountablySeparated Z]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}

/-- The a.e. seed-moments capstone with only a.e. cdf dominance of the conditional
clock laws as a distributional input; the a.e. probability of those laws is derived. -/
theorem ae_exists_boundedSecondMomentClass_of_cdf_dominance
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
  exact ae_exists_boundedSecondMomentClass_of_ae_cdf_dominance hsupported hF hrho0
    hrho1 hrho0nonneg hrho1nonneg hv hv0 hA hatomA hdelta hboundsAE
    (ae_condDistrib_isProbabilityMeasure (u := u) (a := a) eta0 lambda)
    (ae_condDistrib_isProbabilityMeasure (u := u) (a := a) eta1 lambda) hdom hq g hg hgb

/-- The a.e. seed-moments capstone from a.e. threshold separation of the clock
supports: both modeled inputs of `AeOrderCoupling.lean` are derived. -/
theorem ae_exists_boundedSecondMomentClass_of_ae_support_threshold
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
    {c : Z → ℝ}
    (hthreshold : ∀ᵐ z ∂lambda,
      (condDistrib u a eta0 z).support ⊆ Set.Iic (c z) ∧
      (condDistrib u a eta1 z).support ⊆ Set.Ici (c z))
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
  refine ae_exists_boundedSecondMomentClass_of_cdf_dominance hsupported hF hrho0 hrho1
    hrho0nonneg hrho1nonneg hv hv0 hA hatomA hdelta hboundsAE ?_ hq g hg hgb
  exact ae_cdf_le_of_ae_support_threshold
    (ae_condDistrib_isProbabilityMeasure (u := u) (a := a) eta0 lambda)
    (ae_condDistrib_isProbabilityMeasure (u := u) (a := a) eta1 lambda) hthreshold

end OTSelector.Reconstruction

end
