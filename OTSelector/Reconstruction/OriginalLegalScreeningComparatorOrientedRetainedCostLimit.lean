import OTSelector.Reconstruction.OriginalLegalScreeningComparatorRetainedCostLimit
import OTSelector.Reconstruction.OriginalLegalScreeningComparatorOrientedRetainedCostMean

/-! The unchanged same-frame retained signed cost recovers the same weighted value. -/
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

/-- The genuine retained plan in the chosen physical cube has normalized
expected signed cost tending to the unchanged matching's own weighted value.
Only its actual finite path length and original Palm L1 are used. -/
theorem tendsto_originalOrientedPathRetainedPlan_normalized_weightedCost
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {kin : ℝ → ℝ → (Fin (finrank ℝ S.covector.ker) → ℝ) → ℝ}
    {g : ℝ → ℝ → ℝ}
    (Q : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν kin g)
    (hk : Measurable (Function.uncurry (fun p : ℝ × ℝ ↦ kin p.1 p.2)))
    (hg : Measurable (Function.uncurry g))
    (b : OrthonormalBasis (Fin (finrank ℝ S.covector.ker)) ℝ
      (EuclideanSpace ℝ (Fin (finrank ℝ S.covector.ker)))) (t : ℝ)
    {ell : ℝ → ℝ} (hell : ∀ᶠ R in atTop, 0 ≤ ell R)
    (hlarge : Tendsto ell atTop atTop)
    (hsmall : Tendsto (fun R ↦ ell R / R) atTop (𝓝 0)) :
    Tendsto (fun R ↦
      (∫ scene, ∫ e, originalWeightedEdgeCost kin g t e
        ∂(originalStageRestrictedPathPlan
          (originalOrientedPathLengthRetained S w b R (ell R)) scene :
          Measure (LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker)))
        ∂(Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker)))) /
      volume.real (originalCenteredPhysicalCubeRegion b (2 * R))) atTop (𝓝 (Q.value t)) := by
  have htail := tendsto_original_truncated_Palm_integral
    (f := fun m : PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker)) ↦
      kin m.1.1 m.1.2 m.2 + t * g m.1.1 m.1.2)
    (measurable_originalSeedPairPathLength S hF hw)
    (hk.add ((hg.comp measurable_fst).const_mul t))
    (Q.kinetic_integrable.add (Q.probe_integrable.const_mul t)) hlarge
  have hv : Tendsto (fun R ↦ volume.real (originalCenteredPhysicalCubeRegion b
        (2 * (R - 2 * (originalStageFrameCollarFactor b * ell R)))) /
      volume.real (originalCenteredPhysicalCubeRegion b (2 * R))) atTop (𝓝 1) := by
    simpa only [measureReal_def, volume_originalOrientedTraffic_cube, mul_assoc] using
      tendsto_original_innerCube_volume_ratio (Fin (finrank ℝ S.covector.ker)) hell
        (k := 2 * originalStageFrameCollarFactor b)
        (mul_nonneg (by norm_num)
          (zero_le_one.trans (one_le_originalStageFrameCollarFactor b))) hsmall
  have hvalue : (∫ m : PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker)),
      kin m.1.1 m.1.2 m.2 + t * g m.1.1 m.1.2 ∂legalMarkedJointPalm _ Q.law) = Q.value t := by
    rw [integral_add Q.kinetic_integrable (Q.probe_integrable.const_mul t), integral_const_mul]
    rfl
  rw [hvalue] at htail
  have h := hv.mul htail
  simp only [one_mul] at h
  apply h.congr'
  filter_upwards [] with R
  rw [(originalOrientedPathRetainedPlan_weightedCost_integrable_and_integral
    hF hw Q hk hg b R (ell R) t).2]
  ring

end OTSelector.Reconstruction
