import OTSelector.Reconstruction.FinslerOriginalRawSeedConditionalMoments
import OTSelector.Reconstruction.FinslerOriginalClockSupportBounds
import OTSelector.Reconstruction.FinslerOriginalPoissonClockSupport
import OTSelector.Reconstruction.FinslerPopulationConditionalSeparation

/-!
# Second-moment class capstone from the bundled raw seed datum

The bundled raw seed datum carries, at one label, the actual seed, its complete
comparison, the atomless compact clock laws, the conditional clock support bounds
and a full conditional-moments datum.  This file feeds that datum into the bounded
second-moment class capstone: choosing the concrete datum and invoking the reserve
second-moment capstone with a coupling and an arbitrary bounded measurable probe
produces a legal stationary Poisson matching (for the actual seed level and the two
conditional clock laws of that label) whose recoded legal Palm has a nonempty
abstract bounded second-moment class.
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

/-- Second-moment class capstone fed by the bundled raw seed datum. -/
theorem exists_boundedSecondMomentClass_of_bundled_raw_seed
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
    {delta diameter : ℝ} (hdelta : 0 < delta)
    (hboundsAE : ∀ᵐ z ∂lambda,
      ConditionalClockSupportBounds (condDistrib u a eta0 z)
        (condDistrib u a eta1 z) delta diameter)
    (hq : ∀ j, 4 < finrank ℝ (P j).seed.covector.ker)
    (pi : Z → Measure (ℝ × ℝ)) (hpiFinite : ∀ z, IsFiniteMeasure (pi z))
    (hpi : ∀ z, Vlasov.IsCoupling (pi z) (condDistrib u a eta0 z)
      (condDistrib u a eta1 z))
    (horder : ∀ z, ∀ᵐ p ∂pi z, p.1 ≤ p.2)
    (g : ℝ → ℝ → ℝ) (hg : Measurable (Function.uncurry g)) {G : ℝ}
    (hgb : ∀ a b, |g a b| ≤ G) :
    ∃ (z : Z) (j : ℕ) (w : (P j).seed.covector.ker)
      (D : OriginalSeedConditionalMoments (P j).seed w
        (condDistrib u a eta0 z) (condDistrib u a eta1 z))
      (Q : LegalWeightedStationaryPoissonMatching
        (finrank ℝ (P j).seed.covector.ker)
        (condDistrib u a eta0 z) (condDistrib u a eta1 z)
        (D.originalFocalKinetic delta) g) (Bnd : ℝ),
      0 ≤ Bnd ∧
      (boundedSecondMomentClass
        (α := (legalMarkedJointPalm (finrank ℝ (P j).seed.covector.ker) Q.law).map
          carrierRecodePair |>.map (fun p => p.1.2))
        (β := (legalMarkedJointPalm (finrank ℝ (P j).seed.covector.ker) Q.law).map
          carrierRecodePair |>.map (fun p => p.2.2)) Bnd).Nonempty := by
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
          (condDistrib u a eta1 z) delta diameter) := by
    filter_upwards [hsupported, hatomA, hboundsAE] with z hz ha hb
    exact ⟨hz, ha, hb⟩
  obtain ⟨z, hsup, _hatom, hbnd⟩ :=
    exists_of_eventually_of_isProbabilityMeasure hAll
  obtain ⟨j, w, lo, hi, hw, _hwz, _hrn, _hfin, hcomparison, hspan, hd0, hd1⟩ := hsup
  have hdatum := originalSeedConditionalMoments_of_supported_comparison hF hw
    hcomparison hspan hrho0 hrho1 hrho0nonneg hrho1nonneg hv hv0 hd0 hd1
  let D : OriginalSeedConditionalMoments (P j).seed w
      (condDistrib u a eta0 z) (condDistrib u a eta1 z) := Classical.choice hdatum
  haveI : IsFiniteMeasure (pi z) := hpiFinite z
  obtain ⟨Q, Bnd, hBnd0, hclass⟩ :=
    exists_boundedSecondMomentClass_legal_reserve_probe D hF hw (hq j) hdelta
      hbnd (pi z) (hpi z) (horder z) g hg hgb
  exact ⟨z, j, w, D, Q, Bnd, hBnd0, hclass⟩

end OTSelector.Reconstruction

end
