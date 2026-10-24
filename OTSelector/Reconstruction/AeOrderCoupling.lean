import OTSelector.Reconstruction.QuantilePushforward
import OTSelector.Reconstruction.FinslerOriginalSeedMomentsAeCapstone

/-!
# Almost-everywhere order coupling for the conditional clock laws

This file closes the wiring gap of `QuantilePushforward.lean`: the unconditional
co-monotone order coupling `exists_orderCoupling_of_stochastic_dominance` is
lifted to the label-almost-sure setting and composed with the a.e. seed-moments
capstone, so that the a.e. coupling-existence hypothesis of
`ae_exists_boundedSecondMomentClass_of_raw` is constructed instead of assumed.

* `ae_exists_orderCoupling_of_ae_cdf_dominance`: a.e. cdf dominance of two
  families of probability laws on `ℝ` yields a.e. existence of a coupling
  supported on the order relation;
* `ae_exists_boundedSecondMomentClass_of_ae_cdf_dominance`: the a.e. seed-moments
  capstone with the coupling input discharged from a.e. cdf dominance of the
  conditional clock laws.

The cdf-dominance hypothesis is a genuine stochastic-dominance input: the only
available support information on the conditional clock laws
(`ConditionalClockSupportBounds`) separates the two supports but does not order
them, so the cdf dominance is not derivable from it and remains the modeled
input.  In the stronger threshold-separated case (one support below a level, the
other above it) cdf dominance is derivable, see
`cdf_le_of_support_threshold` below.
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

/-- A.e. cdf dominance of two families of real probability laws gives a.e. an order
coupling (a finite measure coupling supported on the order relation). -/
theorem ae_exists_orderCoupling_of_ae_cdf_dominance
    {Z : Type*} [MeasurableSpace Z] {lambda : Measure Z}
    {s0 s1 : Z → Measure ℝ}
    (hprob0 : ∀ᵐ z ∂lambda, IsProbabilityMeasure (s0 z))
    (hprob1 : ∀ᵐ z ∂lambda, IsProbabilityMeasure (s1 z))
    (hdom : ∀ᵐ z ∂lambda, ∀ t : ℝ, cdf (s1 z) t ≤ cdf (s0 z) t) :
    ∀ᵐ z ∂lambda, ∃ pi : Measure (ℝ × ℝ), IsFiniteMeasure pi ∧
      Vlasov.IsCoupling pi (s0 z) (s1 z) ∧ ∀ᵐ p ∂pi, p.1 ≤ p.2 := by
  filter_upwards [hprob0, hprob1, hdom] with z h0 h1 hz
  haveI : IsProbabilityMeasure (s0 z) := h0
  haveI : IsProbabilityMeasure (s1 z) := h1
  obtain ⟨pi, hpi, hcoup, horder⟩ := exists_orderCoupling_of_stochastic_dominance hz
  haveI : IsProbabilityMeasure pi := hpi
  exact ⟨pi, inferInstance, hcoup, horder⟩


/-- In the threshold-separated case cdf dominance is derivable: if one law is supported
below a level and the other above it, the cdf of the upper law is pointwise smaller. -/
theorem cdf_le_of_support_threshold {μ ν : Measure ℝ} [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] {c : ℝ} (hμ : μ.support ⊆ Set.Iic c)
    (hν : ν.support ⊆ Set.Ici c) : ∀ t : ℝ, cdf ν t ≤ cdf μ t := by
  intro t
  rcases lt_or_ge t c with htc | hct
  · have hzero : ν (Set.Iic t) = 0 := by
      apply measure_mono_null ?_ (measure_compl_support_eq_zero ν)
      intro x hx
      rw [Set.mem_compl_iff]
      intro hxs
      have hcx : c ≤ x := hν hxs
      have hxt : x ≤ t := hx
      linarith
    have hcdf : cdf ν t = 0 := by
      have h := ofReal_cdf (μ := ν) t
      rw [hzero] at h
      have hle := ENNReal.ofReal_eq_zero.mp h
      linarith [cdf_nonneg ν t]
    rw [hcdf]
    exact cdf_nonneg μ t
  · have hone : μ (Set.Iic t) = 1 := by
      have hcompl : μ (Set.Iic t)ᶜ = 0 := by
        apply measure_mono_null ?_ (measure_compl_support_eq_zero μ)
        intro x hx
        rw [Set.mem_compl_iff]
        intro hxs
        have hxt : t < x := by simpa using hx
        have hxc : x ≤ c := hμ hxs
        linarith
      have h := measure_add_measure_compl (μ := μ) (s := Set.Iic t) measurableSet_Iic
      rw [hcompl, add_zero] at h
      rw [h, measure_univ]
    have honecdf : cdf μ t = 1 := by
      have h := ofReal_cdf (μ := μ) t
      rw [hone] at h
      have h1 : ENNReal.ofReal (cdf μ t) = ENNReal.ofReal (1:ℝ) := by
        rw [h]
        simp
      exact (ENNReal.ofReal_eq_ofReal_iff (cdf_nonneg μ t) zero_le_one).mp h1
    rw [honecdf]
    exact cdf_le_one ν t


variable {E M Z : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  [StandardBorelSpace M] [Nonempty M]
  [MeasurableSpace Z] [MeasurableEq Z] [MeasurableSpace.CountablySeparated Z]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}

/-- The a.e. seed-moments capstone with the coupling input discharged from a.e. cdf
dominance of the conditional clock laws. -/
theorem ae_exists_boundedSecondMomentClass_of_ae_cdf_dominance
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
    (hprob0 : ∀ᵐ z ∂lambda, IsProbabilityMeasure (condDistrib u a eta0 z))
    (hprob1 : ∀ᵐ z ∂lambda, IsProbabilityMeasure (condDistrib u a eta1 z))
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
  exact ae_exists_boundedSecondMomentClass_of_raw hsupported hF hrho0 hrho1
    hrho0nonneg hrho1nonneg hv hv0 hA hatomA hdelta hboundsAE
    (ae_exists_orderCoupling_of_ae_cdf_dominance hprob0 hprob1 hdom) hq g hg hgb

end OTSelector.Reconstruction

end
