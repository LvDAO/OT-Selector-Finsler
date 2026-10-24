import OTSelector.Reconstruction.AeClockLawProbability
import OTSelector.Reconstruction.FinslerOriginalRawSeedConditionalMoments
import OTSelector.Reconstruction.FinslerOriginalClockSupportBounds
import OTSelector.Reconstruction.FinslerOriginalWeightedStationaryMinimizer
import OTSelector.Reconstruction.FinslerOriginalCommonScaleFinalUnconditional
import OTSelector.Reconstruction.MarkedStationaryValueLegalOriginalFocalMomentum

/-!
# Seed-moments consumer: single-label witness into the marked-stationary chain

`AeClockLawProbability` closes the seed-moments capstone with only a.e. CDF
dominance as modeled input, but its conclusion is a bare existential over the
label.  The downstream marked-stationary consumers
(`OriginalSeedConditionalMoments.exists_original_weighted_stationary_minimizer`,
`OriginalSeedConditionalMoments.ae_original_minimizer_commonScale_finalUnconditional`)
need, at one and the same label:

* the seed label membership `w ∈ S.labels`,
* the conditional clock support bounds (for the gap between the two clocks),
* an actual seed conditional-moments datum for the two conditional clock laws,
* a legal weighted stationary matching attaining the weighted infimum (the
  minimizer needed by the common-scale consumer),
* and a nonempty bounded second-moment class.

This file produces exactly that witness at one label from the capstone inputs,
using the order coupling derived from a.e. CDF dominance
(`exists_orderCoupling_of_stochastic_dominance`):

* `exists_minimizer_witness_of_cdf_dominance`: the full single-label witness
  (label membership, clock support bounds, seed conditional-moments datum,
  weighted-stationary minimizer, nonempty bounded second-moment class);
* `exists_integrable_originalSeedPairMomentum_of_cdf_dominance`: the downstream
  marked-stationary consumer
  `OriginalSeedConditionalMoments.integrable_original_pair_momentum_of_weighted_stationary`
  applied to that witness, giving integrable original pair momentum and momentum
  square at the witness label.

Remaining sub-gap: the common-scale consumer
`ae_original_minimizer_commonScale_finalUnconditional` additionally needs per-label
truncation/cut data (`T`, `cut`, `h`, `ell`, ...) whose types depend on the seed
selected by the capstone.  Since the capstone selects the seed only existentially,
that data must be quantified after the witness and its whole-path conclusion
restated under the `(P j).seed` projections; the witness construction here provides
exactly the datum, the minimizer and the clock bounds that consumer starts from.
-/

open Set Function Filter MeasureTheory ProbabilityTheory Matrix Module Manifold Metric Topology
  OTSelector.Geometry ContinuousFinslerNorm OTSelector.PointProcess
  OTSelector.PointProcess.StationaryForwardMatching OTSelector.Probability
open scoped ENNReal NNReal ContDiff Matrix.Norms.Operator Classical Topology

noncomputable section

set_option maxHeartbeats 6400000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

namespace OTSelector.Reconstruction

variable {E M Z : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  [StandardBorelSpace M] [Nonempty M]
  [MeasurableSpace Z] [MeasurableEq Z] [MeasurableSpace.CountablySeparated Z]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}


variable {E M Z : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  [StandardBorelSpace M] [Nonempty M]
  [MeasurableSpace Z] [MeasurableEq Z] [MeasurableSpace.CountablySeparated Z]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}

/-- Single-label witness feeding the marked-stationary consumers.  From the seed
capstone inputs and a.e. CDF dominance of the two conditional clock laws, at ONE
label there are a seed label member, the conditional clock support bounds, a full
seed conditional-moments datum, a legal weighted stationary minimizer and a
nonempty bounded second-moment class. -/
theorem exists_minimizer_witness_of_cdf_dominance
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
    (hdom : ∀ᵐ z ∂lambda, ∀ s : ℝ,
      cdf (condDistrib u a eta1 z) s ≤ cdf (condDistrib u a eta0 z) s)
    (hq : ∀ j, 4 < finrank ℝ (P j).seed.covector.ker)
    (g : ℝ → ℝ → ℝ) (hg : Measurable (Function.uncurry g)) {G : ℝ}
    (hgb : ∀ s t, |g s t| ≤ G)
    (hgc : Continuous (Function.uncurry g)) (t : ℝ) :
    ∃ (z : Z) (j : ℕ) (w : (P j).seed.covector.ker)
      (datum : OriginalSeedConditionalMoments (P j).seed w
        (condDistrib u a eta0 z) (condDistrib u a eta1 z)),
      w ∈ (P j).seed.labels ∧
      ConditionalClockSupportBounds (condDistrib u a eta0 z)
        (condDistrib u a eta1 z) delta diameter ∧
      (∃ Qmin : LegalWeightedStationaryPoissonMatching
          (finrank ℝ (P j).seed.covector.ker)
          (condDistrib u a eta0 z) (condDistrib u a eta1 z)
          (datum.originalFocalKinetic delta) g,
        ∀ P' : LegalWeightedStationaryPoissonMatching
          (finrank ℝ (P j).seed.covector.ker)
          (condDistrib u a eta0 z) (condDistrib u a eta1 z)
          (datum.originalFocalKinetic delta) g, Qmin.value t ≤ P'.value t) ∧
      ∃ (Qprobe : LegalWeightedStationaryPoissonMatching
          (finrank ℝ (P j).seed.covector.ker)
          (condDistrib u a eta0 z) (condDistrib u a eta1 z)
          (datum.originalFocalKinetic delta) g) (Bnd : ℝ),
        0 ≤ Bnd ∧
        (boundedSecondMomentClass
          (α := (legalMarkedJointPalm (finrank ℝ (P j).seed.covector.ker)
            Qprobe.law).map carrierRecodePair |>.map (fun p => p.1.2))
          (β := (legalMarkedJointPalm (finrank ℝ (P j).seed.covector.ker)
            Qprobe.law).map carrierRecodePair |>.map (fun p => p.2.2)) Bnd).Nonempty := by
  have hall : ∀ᵐ z ∂lambda,
      (∃ (j : ℕ) (w : (P j).seed.covector.ker) (lo hi : ℝ),
        w ∈ (P j).seed.labels ∧ a ((P j).seed.curve w 0) = z ∧
        ((populationSeedLabelReference (P j).seed a (kappa j)).rnDeriv
            lambda z) ≠ 0 ∧
        ((populationSeedLabelReference (P j).seed a (kappa j)).rnDeriv
            lambda z) < (⊤ : ℝ≥0∞) ∧
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
        (condDistrib u a eta1 z) delta diameter ∧
      (∀ s : ℝ, cdf (condDistrib u a eta1 z) s ≤ cdf (condDistrib u a eta0 z) s) := by
    filter_upwards [hsupported, hatomA, hboundsAE, hdom] with z hsup ha hb hd
    exact ⟨hsup, ha, hb, hd⟩
  obtain ⟨z, ⟨j, w, lo, hi, hw, _hwz, _hrn, _hfin, hcomparison, hspan, hd0, hd1⟩,
    _ha, hbnd, hdomz⟩ := exists_of_eventually_of_isProbabilityMeasure hall
  have hdatum := originalSeedConditionalMoments_of_supported_comparison hF hw
    hcomparison hspan hrho0 hrho1 hrho0nonneg hrho1nonneg hv hv0 hd0 hd1
  let datum : OriginalSeedConditionalMoments (P j).seed w
      (condDistrib u a eta0 z) (condDistrib u a eta1 z) := Classical.choice hdatum
  haveI : IsProbabilityMeasure (condDistrib u a eta0 z) :=
    condDistrib_isProbabilityMeasure (u := u) (a := a) eta0 z
  haveI : IsProbabilityMeasure (condDistrib u a eta1 z) :=
    condDistrib_isProbabilityMeasure (u := u) (a := a) eta1 z
  obtain ⟨pi, hpiProb, hpiCoup, hpiOrd⟩ :=
    exists_orderCoupling_of_stochastic_dominance hdomz
  haveI : IsProbabilityMeasure pi := hpiProb
  obtain ⟨Qprobe, Bnd, hBnd0, hclass⟩ :=
    exists_boundedSecondMomentClass_legal_reserve_probe datum hF hw (hq j) hdelta
      hbnd pi hpiCoup hpiOrd g hg hgb
  obtain ⟨Qmin, _hvalue, hmin⟩ :=
    datum.exists_original_weighted_stationary_minimizer hF hw (hq j) hdelta hbnd
      pi hpiCoup hpiOrd hg hgb hgc.continuousOn t
  exact ⟨z, j, w, datum, hw, hbnd, ⟨Qmin, hmin⟩, Qprobe, Bnd, hBnd0, hclass⟩

/-- Downstream marked-stationary consumer wiring: the witness label carries an
actual seed conditional-moments datum and a legal weighted stationary Poisson
matching whose original pair momentum and momentum square are integrable, i.e.
the marked-stationary consumer
`OriginalSeedConditionalMoments.integrable_original_pair_momentum_of_weighted_stationary`
applies to the witness data produced from the capstone inputs and a.e. CDF
dominance. -/
theorem exists_integrable_originalSeedPairMomentum_of_cdf_dominance
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
    (hdom : ∀ᵐ z ∂lambda, ∀ s : ℝ,
      cdf (condDistrib u a eta1 z) s ≤ cdf (condDistrib u a eta0 z) s)
    (hq : ∀ j, 4 < finrank ℝ (P j).seed.covector.ker)
    (g : ℝ → ℝ → ℝ) (hg : Measurable (Function.uncurry g)) {G : ℝ}
    (hgb : ∀ s t, |g s t| ≤ G)
    (hgc : Continuous (Function.uncurry g)) (t : ℝ) :
    ∃ (z : Z) (j : ℕ) (w : (P j).seed.covector.ker)
      (datum : OriginalSeedConditionalMoments (P j).seed w
        (condDistrib u a eta0 z) (condDistrib u a eta1 z))
      (Q : LegalWeightedStationaryPoissonMatching
        (finrank ℝ (P j).seed.covector.ker)
        (condDistrib u a eta0 z) (condDistrib u a eta1 z)
        (datum.originalFocalKinetic delta) g),
      w ∈ (P j).seed.labels ∧
      ConditionalClockSupportBounds (condDistrib u a eta0 z)
        (condDistrib u a eta1 z) delta diameter ∧
      Integrable (originalSeedPairMomentum (P j).seed w)
        (legalMarkedJointPalm (finrank ℝ (P j).seed.covector.ker) Q.law) ∧
      Integrable (fun m => ‖originalSeedPairMomentum (P j).seed w m‖ ^ 2)
        (legalMarkedJointPalm (finrank ℝ (P j).seed.covector.ker) Q.law) := by
  obtain ⟨z, j, w, datum, hw, hbnd, ⟨_Qmin, _hmin⟩, Qprobe, _Bnd, _hBnd0, _hclass⟩ :=
    exists_minimizer_witness_of_cdf_dominance hsupported hF hrho0 hrho1 hrho0nonneg
      hrho1nonneg hv hv0 hA hatomA hdelta hboundsAE hdom hq g hg hgb hgc t
  obtain ⟨hint1, hint2⟩ :=
    datum.integrable_original_pair_momentum_of_weighted_stationary hF hw hdelta hbnd
      Qprobe
  exact ⟨z, j, w, datum, Qprobe, hw, hbnd, hint1, hint2⟩

end OTSelector.Reconstruction

end