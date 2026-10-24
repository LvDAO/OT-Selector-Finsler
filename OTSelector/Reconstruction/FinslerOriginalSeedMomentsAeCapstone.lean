import OTSelector.Reconstruction.FinslerOriginalSeedMomentsBundled
import OTSelector.Reconstruction.FinslerOriginalClockSupportBounds
import OTSelector.Reconstruction.FinslerOriginalPoissonClockSupport

/-!
# Almost-everywhere and coupled seed moments capstone

This file upgrades the single-label second-moment class capstone in two directions.

* `exists_boundedSecondMomentClass_of_bundled_datum` imports the bundled raw seed
  datum module and composes it with the reserve second-moment capstone, instead of
  re-deriving the bundle inline;
* `ae_exists_boundedSecondMomentClass_of_raw` proves the almost-everywhere version:
  on a label almost surely, the whole chain (actual seed, comparison, datum, coupling,
  legal stationary Poisson matching and nonempty bounded second-moment class) holds
  simultaneously, using only the a.e. producers and an a.e. coupling-existence input;
* `ae_exists_boundedSecondMomentClass_selfCoupling` derives the a.e. coupling input
  from the physical window law itself in the equal-input case, using the diagonal
  monotone coupling of a conditional clock law with itself.
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

/-- Single-label second-moment class capstone obtained by importing the bundled raw
seed datum module (no inline re-derivation of the bundle). -/
theorem exists_boundedSecondMomentClass_of_bundled_datum
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
    (hq : ∀ j, 4 < finrank ℝ (P j).seed.covector.ker)
    (pi : Z → Measure (ℝ × ℝ)) (hpiFinite : ∀ z, IsFiniteMeasure (pi z))
    (hpi : ∀ z, Vlasov.IsCoupling (pi z) (condDistrib u a eta0 z)
      (condDistrib u a eta1 z))
    (horder : ∀ z, ∀ᵐ p ∂pi z, p.1 ≤ p.2)
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
          carrierRecodePair |>.map (fun p => p.2.2)) Bnd).Nonempty := by
  obtain ⟨z, j, w, hw, _hwz, _hcomparison, _hatom, _hcompact, hbnd, _hmom0, _hmom1,
    hne⟩ :=
    exists_bundled_raw_seed_datum (delta := delta) (D := diameter) hsupported hF
      hrho0 hrho1 hrho0nonneg hrho1nonneg hv hv0 hA hatomA hboundsAE
  let datum : OriginalSeedConditionalMoments (P j).seed w
      (condDistrib u a eta0 z) (condDistrib u a eta1 z) := Classical.choice hne
  haveI : IsFiniteMeasure (pi z) := hpiFinite z
  obtain ⟨Q, Bnd, hBnd0, hclass⟩ :=
    exists_boundedSecondMomentClass_legal_reserve_probe datum hF hw (hq j) hdelta
      hbnd (pi z) (hpi z) (horder z) g hg hgb
  exact ⟨z, j, w, datum, Q, Bnd, hBnd0, hclass⟩

/-- Almost-everywhere second-moment class capstone: on a label almost surely the
whole chain holds simultaneously, with the coupling supplied only almost everywhere.-/
theorem ae_exists_boundedSecondMomentClass_of_raw
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
    (hcoupling : ∀ᵐ z ∂lambda, ∃ pi : Measure (ℝ × ℝ), IsFiniteMeasure pi ∧
      Vlasov.IsCoupling pi (condDistrib u a eta0 z) (condDistrib u a eta1 z) ∧
      ∀ᵐ p ∂pi, p.1 ≤ p.2)
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
  filter_upwards [hsupported, hatomA, hboundsAE, hcoupling] with z hsup _ha hb hc
  obtain ⟨j, w, lo, hi, hw, _hwz, _hrn, _hfin, hcomparison, hspan, hd0, hd1⟩ := hsup
  have hdatum := originalSeedConditionalMoments_of_supported_comparison hF hw
    hcomparison hspan hrho0 hrho1 hrho0nonneg hrho1nonneg hv hv0 hd0 hd1
  let datum : OriginalSeedConditionalMoments (P j).seed w
      (condDistrib u a eta0 z) (condDistrib u a eta1 z) := Classical.choice hdatum
  obtain ⟨pi, hpiFin, hpiCoup, hpiOrd⟩ := hc
  haveI : IsFiniteMeasure pi := hpiFin
  obtain ⟨Q, Bnd, hBnd0, hclass⟩ :=
    exists_boundedSecondMomentClass_legal_reserve_probe datum hF hw (hq j) hdelta
      hb pi hpiCoup hpiOrd g hg hgb
  exact ⟨j, w, datum, Q, Bnd, hBnd0, hclass⟩

end OTSelector.Reconstruction

end
