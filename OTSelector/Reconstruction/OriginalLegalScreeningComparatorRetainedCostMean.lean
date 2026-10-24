import OTSelector.Reconstruction.OriginalRetainedFinitePlan
import OTSelector.Reconstruction.OriginalLegalScreeningComparatorRestrictedPalmMean

/-! Exact Campbell means of the actual path-length retained original plan. -/
open Set Function Filter MeasureTheory ProbabilityTheory Module Manifold
open scoped ENNReal Topology ContDiff
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OTSelector.Reconstruction
open OTSelector.Geometry ContinuousFinslerNorm OTSelector.Probability
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {S : CalibratedLevelSeedPatch F u} {w : S.covector.ker} {μ ν : Measure ℝ}

/-- The unchanged path-retained plan has the exact inner-cube volume times
the same original Palm observable truncated by its actual complete path length.
Integrability is produced by Campbell, without a retained-cost hypothesis. -/
theorem originalPathRetainedPlan_palmReadout_integrable_and_integral
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {kin : ℝ → ℝ → (Fin (finrank ℝ S.covector.ker) → ℝ) → ℝ}
    {g : ℝ → ℝ → ℝ}
    (Q : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν kin g)
    (R ell : ℝ) (f : PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker)) → ℝ)
    (hf : Measurable f) (hi : Integrable f (legalMarkedJointPalm _ Q.law)) :
    Integrable (fun scene ↦ ∫ e, f (physicalPairAnchor e).2
      ∂(originalPathRetainedPlan S w R ell scene : Measure
        (LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker))))
      (Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))) ∧
    (∫ scene, ∫ e, f (physicalPairAnchor e).2
      ∂(originalPathRetainedPlan S w R ell scene : Measure
        (LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker)))
      ∂(Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker)))) =
      volume.real (haarRootCube (Fin (finrank ℝ S.covector.ker)) (R - 2 * ell)) *
        ∫ m in {m | originalSeedPairPathLength S w m ≤ ell}, f m
          ∂legalMarkedJointPalm _ Q.law := by
  exact Q.productRestrictedPlan_palmReadout_mean
    measurableSet_Icc isCompact_Icc.measure_ne_top
    (measurableSet_le (measurable_originalSeedPairPathLength S hF hw) measurable_const)
    f hf hi

/-- The actual signed retained edge cost is integrable, with its full original
kinetic cost and probe preserved in the exact Campbell identity. -/
theorem originalPathRetainedPlan_weightedCost_integrable_and_integral
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {kin : ℝ → ℝ → (Fin (finrank ℝ S.covector.ker) → ℝ) → ℝ}
    {g : ℝ → ℝ → ℝ}
    (Q : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν kin g)
    (hk : Measurable (Function.uncurry (fun p : ℝ × ℝ ↦ kin p.1 p.2)))
    (hg : Measurable (Function.uncurry g)) (R ell t : ℝ) :
    Integrable (fun scene ↦ ∫ e, originalWeightedEdgeCost kin g t e
      ∂(originalPathRetainedPlan S w R ell scene : Measure
        (LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker))))
      (Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))) ∧
    (∫ scene, ∫ e, originalWeightedEdgeCost kin g t e
      ∂(originalPathRetainedPlan S w R ell scene : Measure
        (LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker)))
      ∂(Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker)))) =
      volume.real (haarRootCube (Fin (finrank ℝ S.covector.ker)) (R - 2 * ell)) *
        ∫ m in {m | originalSeedPairPathLength S w m ≤ ell},
          kin m.1.1 m.1.2 m.2 + t * g m.1.1 m.1.2
          ∂legalMarkedJointPalm _ Q.law := by
  exact originalPathRetainedPlan_palmReadout_integrable_and_integral hF hw Q R ell
    (fun m ↦ kin m.1.1 m.1.2 m.2 + t * g m.1.1 m.1.2)
    (hk.add ((hg.comp measurable_fst).const_mul t))
    (Q.kinetic_integrable.add (Q.probe_integrable.const_mul t))

end OTSelector.Reconstruction
