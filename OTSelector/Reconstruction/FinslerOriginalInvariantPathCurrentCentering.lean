import OTSelector.Probability.InvariantConditionalMeanZero
import OTSelector.Reconstruction.FinslerOriginalPathClockCurrent
import OTSelector.Reconstruction.MarkedStationaryValueLegalInvariantMinimum

/-!
# True path-position current has zero invariant conditional vector mean

Conditioning on each actual invariant event retains the complete original
input and global minimum. Exact path-local Campbell readout then centers
the literal current at its actual path position on every such event.
-/
open Set Function MeasureTheory Filter Topology Module Manifold
open scoped ContDiff ProbabilityTheory
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability OTSelector.Geometry ContinuousFinslerNorm
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
set_option linter.unusedSectionVars false
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {S : CalibratedLevelSeedPatch F u} {w : S.covector.ker} {μ ν : Measure ℝ}
namespace OriginalSeedConditionalMoments
variable (D : OriginalSeedConditionalMoments S w μ ν)

/-- The current is observed in the unit physical cube containing its actual
path position. Its complete vector mean is zero conditional on every
reroot-invariant original scene event, with no displacement second moment. -/
theorem condExp_original_pathClockCurrent_eq_zero_of_minimal_value
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
      originalSeedPathClockCurrent S w c | Q.invariantSigma] =ᵐ[(Q.law : Measure _)]
        fun _ ↦ 0 := by
  let _ : IsProbabilityMeasure μ := D.support.source.probability
  let _ : IsProbabilityMeasure ν := D.support.target.probability
  apply condExp_eq_zero_of_all_positive_cond_integral_eq_zero _
    (aeInvariantEventSigma_le _ _)
    (D.original_pathClockCurrent_integrable_and_integral hF hw hgap hbounds Q c).1
  intro A hA hpos
  exact D.integral_original_pathClockCurrent_eq_zero_of_minimal_value hF hw hgap hbounds
    (Q.invariantConditionedMatching hq A hA.1 hpos hA.2) t
    (Q.invariantConditionedMatching_minimal hq t hmin A hA.1 hpos hA.2) c

end OriginalSeedConditionalMoments
end OTSelector.Reconstruction
