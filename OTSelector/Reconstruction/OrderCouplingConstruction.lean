import OTSelector.Reconstruction.FinslerOriginalSeedMomentsAeCapstone
import OTSelector.Reconstruction.FinslerOriginalPoissonClockSupport

/-!
# Order (co-monotone) coupling construction

Mathlib provides `nonempty_couplings` (the product coupling) but no order or
quantile coupling theorem.  This file constructs order-preserving couplings in the
two forms needed by the seed conditional-moments capstone:

* `exists_orderCoupling_of_support_threshold`: if two probability laws on `ℝ` have
  supports separated by a threshold `c` (all source support points `≤ c`, all target
  support points `≥ c`), the product coupling is supported on the order relation
  `p.1 ≤ p.2`;
* `exists_orderCoupling_of_measurable_le`: if two clocks are a.e. pointwise ordered
  functions of a common probability law, the joint law of the pair is an
  order-preserving coupling (the functional co-monotone coupling);
* `ae_exists_orderCoupling_of_ae_support_threshold`: the a.e.-in-label version of the
  first construction, producing exactly the a.e. coupling-existence input of
  `ae_exists_boundedSecondMomentClass_of_raw`;
* `ae_exists_boundedSecondMomentClass_of_support_threshold`: the a.e. second-moment
  class capstone with the coupling no longer assumed but derived from the a.e.
  support-threshold condition.
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

/-- If two probability laws on `ℝ` have supports on opposite sides of a threshold,
the product coupling is supported on the order relation. -/
theorem exists_orderCoupling_of_support_threshold
    {μ ν : Measure ℝ} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {c : ℝ} (hμ : μ.support ⊆ Set.Iic c) (hν : ν.support ⊆ Set.Ici c) :
    ∃ π : Measure (ℝ × ℝ), IsProbabilityMeasure π ∧ Vlasov.IsCoupling π μ ν ∧
      ∀ᵐ p ∂π, p.1 ≤ p.2 := by
  refine ⟨μ.prod ν, inferInstance, ?_, ?_⟩
  · simp [Vlasov.IsCoupling]
  · have hmap1 : (μ.prod ν).map Prod.fst = μ := by simp
    have hmap2 : (μ.prod ν).map Prod.snd = ν := by simp
    have h1 : ∀ᵐ p ∂(μ.prod ν), p.1 ∈ μ.support :=
      ae_of_ae_map measurable_fst.aemeasurable (by rw [hmap1]; exact μ.support_mem_ae)
    have h2 : ∀ᵐ p ∂(μ.prod ν), p.2 ∈ ν.support :=
      ae_of_ae_map measurable_snd.aemeasurable (by rw [hmap2]; exact ν.support_mem_ae)
    filter_upwards [h1, h2] with p hp1 hp2
    exact le_trans (hμ hp1) (hν hp2)

/-- The functional co-monotone coupling: two a.e. ordered clocks on a common
probability space have an order-preserving joint law. -/
theorem exists_orderCoupling_of_measurable_le
    {Ω : Type*} [MeasurableSpace Ω] {law : Measure Ω} [IsProbabilityMeasure law]
    {f g : Ω → ℝ} (hf : Measurable f) (hg : Measurable g) (hle : f ≤ᵐ[law] g) :
    ∃ π : Measure (ℝ × ℝ), IsProbabilityMeasure π ∧
      Vlasov.IsCoupling π (law.map f) (law.map g) ∧ ∀ᵐ p ∂π, p.1 ≤ p.2 := by
  have hh : Measurable (fun x : Ω => (f x, g x)) := hf.prodMk hg
  refine ⟨law.map (fun x : Ω => (f x, g x)),
    Measure.isProbabilityMeasure_map hh.aemeasurable, ?_, ?_⟩
  · refine ⟨?_, ?_⟩
    · rw [Measure.map_map measurable_fst hh]; rfl
    · rw [Measure.map_map measurable_snd hh]; rfl
  · rw [ae_iff]
    have hbad : MeasurableSet {p : ℝ × ℝ | ¬ p.1 ≤ p.2} :=
      (measurableSet_le measurable_fst measurable_snd).compl
    rw [Measure.map_apply hh hbad]
    exact (ae_iff (μ := law) (p := fun x => f x ≤ g x)).mp hle

/-- The a.e.-in-label version of the support-threshold order coupling, producing the
a.e. coupling-existence input needed by the second-moment class capstone. -/
theorem ae_exists_orderCoupling_of_ae_support_threshold
    {Z : Type*} [MeasurableSpace Z] {lambda : Measure Z}
    {s t : Z → Measure ℝ} (hprobS : ∀ z, IsProbabilityMeasure (s z))
    (hprobT : ∀ z, IsProbabilityMeasure (t z))
    (h : ∀ᵐ z ∂lambda, ∃ c : ℝ, (s z).support ⊆ Set.Iic c ∧
      (t z).support ⊆ Set.Ici c) :
    ∀ᵐ z ∂lambda, ∃ π : Measure (ℝ × ℝ), IsProbabilityMeasure π ∧
      Vlasov.IsCoupling π (s z) (t z) ∧ ∀ᵐ p ∂π, p.1 ≤ p.2 := by
  filter_upwards [h] with z hz
  obtain ⟨c, hc1, hc2⟩ := hz
  haveI : IsProbabilityMeasure (s z) := hprobS z
  haveI : IsProbabilityMeasure (t z) := hprobT z
  exact exists_orderCoupling_of_support_threshold hc1 hc2

variable {E M Z : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  [StandardBorelSpace M] [Nonempty M]
  [MeasurableSpace Z] [MeasurableEq Z] [MeasurableSpace.CountablySeparated Z]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}

/-- The a.e. second-moment class capstone with the order coupling derived from the
a.e. support-threshold condition instead of assumed. -/
theorem ae_exists_boundedSecondMomentClass_of_support_threshold
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
  have hcoupling : ∀ᵐ z ∂lambda, ∃ pi : Measure (ℝ × ℝ), IsFiniteMeasure pi ∧
      Vlasov.IsCoupling pi (condDistrib u a eta0 z) (condDistrib u a eta1 z) ∧
      ∀ᵐ p ∂pi, p.1 ≤ p.2 := by
    have hbase := ae_exists_orderCoupling_of_ae_support_threshold
      (lambda := lambda) (s := fun z => condDistrib u a eta0 z)
      (t := fun z => condDistrib u a eta1 z)
      (fun z => inferInstance) (fun z => inferInstance) hthreshold
    filter_upwards [hbase] with z hz
    obtain ⟨pi, hprob, hcoup, hord⟩ := hz
    haveI : IsProbabilityMeasure pi := hprob
    exact ⟨pi, inferInstance, hcoup, hord⟩
  exact ae_exists_boundedSecondMomentClass_of_raw hsupported hF hrho0 hrho1
    hrho0nonneg hrho1nonneg hv hv0 hA hatomA hdelta hboundsAE hcoupling hq g hg hgb

end OTSelector.Reconstruction

end
