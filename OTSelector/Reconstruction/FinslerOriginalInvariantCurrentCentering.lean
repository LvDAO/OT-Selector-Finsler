import OTSelector.Reconstruction.MarkedStationaryValueLegalInvariantPalmCentering
import OTSelector.Reconstruction.FinslerOriginalCenteredClockOccupation
import OTSelector.Reconstruction.FinslerOriginalWeightedStationaryMinimizer

/-!
# Invariant-conditional centering of the actual original Finsler current

The minimizing law is conditioned on actual invariant scene events while its
complete original Poisson input and weighted cost stay fixed. First variation
on those genuine conditioned minimizers gives zero conditional current mean.
-/
open Set Function MeasureTheory Filter Topology Module Manifold
open scoped ContDiff ProbabilityTheory
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability OTSelector.Geometry ContinuousFinslerNorm
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2600000
set_option linter.unusedSectionVars false
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {S : CalibratedLevelSeedPatch F u} {w : S.covector.ker} {μ ν : Measure ℝ}
namespace OriginalSeedConditionalMoments
variable (D : OriginalSeedConditionalMoments S w μ ν)

/-- Every actual clock crossing has zero invariant-conditional momentum mean
in the original minimizing scene, componentwise and as a whole vector. -/
theorem condExp_original_crossingMomentum_sceneReadout_eq_zero_of_minimal_value
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    (hq : 0 < finrank ℝ S.covector.ker)
    {gap diameter : ℝ} (hgap : 0 < gap)
    (hbounds : ConditionalClockSupportBounds μ ν gap diameter)
    {g : ℝ → ℝ → ℝ}
    (Q : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν
      (D.originalFocalKinetic gap) g) (t : ℝ)
    (hmin : ∀ R : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν
      (D.originalFocalKinetic gap) g, Q.value t ≤ R.value t) (c : ℝ) :
    (Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker)))[
      legalMarkedScenePalmReadout (finrank ℝ S.covector.ker)
        (originalSeedCrossingMomentum S w c) | Q.invariantSigma] =ᵐ[(Q.law : Measure _)]
          fun _ ↦ 0 := by
  let _ : IsProbabilityMeasure μ := D.support.source.probability
  let _ : IsProbabilityMeasure ν := D.support.target.probability
  apply Q.condExp_scenePalmReadout_eq_zero hq
    (D.integrable_original_crossingMomentum hF hw hgap hbounds Q c)
  intro A hA hpos hinv
  exact D.integral_original_crossingMomentum_eq_zero_of_minimal_value hF hw hgap hbounds
    (Q.invariantConditionedMatching hq A hA hpos hinv) t
    (Q.invariantConditionedMatching_minimal hq t hmin A hA hpos hinv) c

/-- The actual compliance velocity occupying every clock has zero conditional
mean on all invariant original scene events, with only weighted kinetic energy. -/
theorem condExp_original_clockOccupation_sceneReadout_eq_zero_of_minimal_value
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    (hq : 0 < finrank ℝ S.covector.ker)
    {gap diameter : ℝ} (hgap : 0 < gap)
    (hbounds : ConditionalClockSupportBounds μ ν gap diameter)
    {g : ℝ → ℝ → ℝ}
    (Q : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν
      (D.originalFocalKinetic gap) g) (t : ℝ)
    (hmin : ∀ R : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν
      (D.originalFocalKinetic gap) g, Q.value t ≤ R.value t) (c : ℝ) :
    (Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker)))[
      legalMarkedScenePalmReadout (finrank ℝ S.covector.ker)
        (originalSeedClockOccupation S w c) | Q.invariantSigma] =ᵐ[(Q.law : Measure _)]
          fun _ ↦ 0 := by
  let _ : IsProbabilityMeasure μ := D.support.source.probability
  let _ : IsProbabilityMeasure ν := D.support.target.probability
  apply Q.condExp_scenePalmReadout_eq_zero hq
    (D.integrable_original_clockOccupation hF hw hgap hbounds Q c)
  intro A hA hpos hinv
  exact D.integral_original_clockOccupation_eq_zero_of_minimal_value hF hw hgap hbounds
    (Q.invariantConditionedMatching hq A hA hpos hinv) t
    (Q.invariantConditionedMatching_minimal hq t hmin A hA hpos hinv) c

/-- Original general Finsler data produce an actual minimizing original law
whose current has zero invariant-conditional vector mean at every clock. -/
theorem exists_original_minimizer_invariant_current_centered
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    (hq : 4 < finrank ℝ S.covector.ker)
    {gap diameter : ℝ} (hgap : 0 < gap)
    (hbounds : ConditionalClockSupportBounds μ ν gap diameter)
    (π : Measure (ℝ × ℝ)) [IsFiniteMeasure π]
    (hπ : Vlasov.IsCoupling π μ ν) (horder : ∀ᵐ p ∂π, p.1 ≤ p.2)
    {G : ℝ} {g : ℝ → ℝ → ℝ} (hg : Measurable (Function.uncurry g))
    (hgb : ∀ a b, |g a b| ≤ G)
    (hgc : ContinuousOn (Function.uncurry g)
      {p | p.1 - S.level ∈ Ioo D.lo D.hi ∧
        p.2 - S.level ∈ Ioo D.lo D.hi ∧ p.1 < p.2}) (t : ℝ) :
    ∃ Q : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν
      (D.originalFocalKinetic gap) g,
      Q.value t = D.originalWeightedStationaryInf gap g t ∧
      (∀ R : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν
        (D.originalFocalKinetic gap) g, Q.value t ≤ R.value t) ∧
      ∀ c : ℝ, (Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker)))[
        legalMarkedScenePalmReadout (finrank ℝ S.covector.ker)
          (originalSeedClockOccupation S w c) | Q.invariantSigma] =ᵐ[(Q.law : Measure _)]
            fun _ ↦ 0 := by
  obtain ⟨Q, heq, hmin⟩ := D.exists_original_weighted_stationary_minimizer
    hF hw hq hgap hbounds π hπ horder hg hgb hgc t
  exact ⟨Q, heq, hmin, fun c ↦
    D.condExp_original_clockOccupation_sceneReadout_eq_zero_of_minimal_value
      hF hw (by omega) hgap hbounds Q t hmin c⟩

end OriginalSeedConditionalMoments
end OTSelector.Reconstruction
