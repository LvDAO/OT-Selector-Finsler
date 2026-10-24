import OTSelector.Reconstruction.OriginalLegalScreeningComparatorRestrictedPalmMean
import OTSelector.Reconstruction.OriginalStageResidualDensityOrientedWindowPorts
import OTSelector.Reconstruction.OriginalOmittedCurrentOrientedTrafficVolume

/-! Exact signed retained-cost means in the same chosen physical frame. -/
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

omit [BorelSpace E] in
/-- The same-frame retained set is the product of its actual inner physical
cube and the actual full-path cutoff, with all original positions unchanged. -/
theorem originalOrientedPathLengthRetained_eq_product
    (b : OrthonormalBasis (Fin (finrank ℝ S.covector.ker)) ℝ
      (EuclideanSpace ℝ (Fin (finrank ℝ S.covector.ker)))) (R ell : ℝ) :
    originalOrientedPathLengthRetained S w b R ell =
      originalCenteredPhysicalCubeRegion b (2 * (R - 2 * (originalStageFrameCollarFactor b * ell))) ×ˢ
        {m | originalSeedPairPathLength S w m ≤ ell} := by
  rw [originalOrientedTraffic_cube_eq_preimage]
  rfl

/-- Campbell produces the actual scene L1 and signed-cost mean of the same
oriented retained plan. The orientation has no volume or cost correction. -/
theorem originalOrientedPathRetainedPlan_weightedCost_integrable_and_integral
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {kin : ℝ → ℝ → (Fin (finrank ℝ S.covector.ker) → ℝ) → ℝ}
    {g : ℝ → ℝ → ℝ}
    (Q : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν kin g)
    (hk : Measurable (Function.uncurry (fun p : ℝ × ℝ ↦ kin p.1 p.2)))
    (hg : Measurable (Function.uncurry g))
    (b : OrthonormalBasis (Fin (finrank ℝ S.covector.ker)) ℝ
      (EuclideanSpace ℝ (Fin (finrank ℝ S.covector.ker)))) (R ell t : ℝ) :
    Integrable (fun scene ↦ ∫ e, originalWeightedEdgeCost kin g t e
      ∂(originalStageRestrictedPathPlan (originalOrientedPathLengthRetained S w b R ell) scene :
        Measure (LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker))))
      (Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))) ∧
    (∫ scene, ∫ e, originalWeightedEdgeCost kin g t e
      ∂(originalStageRestrictedPathPlan (originalOrientedPathLengthRetained S w b R ell) scene :
        Measure (LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker)))
      ∂(Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker)))) =
      volume.real (originalCenteredPhysicalCubeRegion b
        (2 * (R - 2 * (originalStageFrameCollarFactor b * ell)))) *
        ∫ m in {m | originalSeedPairPathLength S w m ≤ ell},
          kin m.1.1 m.1.2 m.2 + t * g m.1.1 m.1.2
          ∂legalMarkedJointPalm _ Q.law := by
  rw [originalOrientedPathLengthRetained_eq_product]
  exact Q.productRestrictedPlan_palmReadout_mean
    (isCompact_originalStagePhysicalCube b _).measurableSet
    (isCompact_originalStagePhysicalCube b _).measure_ne_top
    (measurableSet_le (measurable_originalSeedPairPathLength S hF hw) measurable_const)
    (fun m ↦ kin m.1.1 m.1.2 m.2 + t * g m.1.1 m.1.2)
    (hk.add ((hg.comp measurable_fst).const_mul t))
    (Q.kinetic_integrable.add (Q.probe_integrable.const_mul t))

end OTSelector.Reconstruction
