import OTSelector.Reconstruction.OriginalScreeningBoundaryBudgetOrientedPortCountCampbell
import OTSelector.Reconstruction.OriginalOmittedCurrentOrientedTrafficVolume
import OTSelector.Reconstruction.OriginalTargetPortCountExpectation

/-! The actual same-frame source and target port plans satisfy genuine collar-and-path-tail bounds. -/
open Set Function Filter MeasureTheory Module Manifold
open scoped ENNReal Topology ContDiff
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OTSelector.Reconstruction
open OTSelector.Geometry ContinuousFinslerNorm OTSelector.Probability
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {S : CalibratedLevelSeedPatch F u} {w : S.covector.ker} {μ ν : Measure ℝ}

/-- Literal source port masses in the chosen physical cube are paid by its own source
collar and the unchanged original full-path tail, without rotating the original law. -/
theorem lintegral_originalOrientedStageSourcePorts_le_collar_and_pathTail
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {kin : ℝ → ℝ → (Fin (finrank ℝ S.covector.ker) → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (Q : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν kin g)
    (b : OrthonormalBasis (Fin (finrank ℝ S.covector.ker)) ℝ
      (EuclideanSpace ℝ (Fin (finrank ℝ S.covector.ker)))) (R ell : ℝ) :
    let K := originalCenteredPhysicalCubeRegion b (2*R)
    (∫⁻ scene, (originalStageWindowSourcePortPlan (originalOrientedPathLengthRetained S w b R ell)
        K scene : Measure (LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker))) univ
      ∂(Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker)))) ≤
      volume (K \ originalCenteredPhysicalCubeRegion b (2*(R-2*(originalStageFrameCollarFactor b*ell)))) +
      volume K * (legalMarkedJointPalm (finrank ℝ S.covector.ker) Q.law)
        {m | ell < originalSeedPairPathLength S w m} := by
  dsimp only
  have hK := measurableSet_originalOrientedTraffic_cube b R
  have hK₀ := measurableSet_originalOrientedTraffic_cube b (R-2*(originalStageFrameCollarFactor b*ell))
  have hA := measurableSet_originalOrientedPathLengthRetained S hF hw b R ell
  simp_rw [originalStageWindowSourcePortPlan_mass_eq_pairKernel hA hK]
  apply Q.lintegral_original_count_le_collar_and_markTail (fun _ ↦ 0) measurable_const hK hK₀
    (measurableSet_lt measurable_const (measurable_originalSeedPairPathLength S hF hw))
  apply Eventually.of_forall
  intro scene
  apply Eventually.of_forall
  intro a ha
  change a.1 ∈ originalCenteredPhysicalCubeRegion b (2*R) ∧
    a ∉ originalOrientedPathLengthRetained S w b R ell at ha
  by_cases hx : a.1 ∈ originalCenteredPhysicalCubeRegion b
      (2*(R-2*(originalStageFrameCollarFactor b*ell)))
  · right
    change a.1+0 ∈ originalCenteredPhysicalCubeRegion b (2*R) ∧ ell < originalSeedPairPathLength S w a.2
    refine ⟨by simpa only [add_zero] using ha.1, lt_of_not_ge ?_⟩
    intro hlength
    apply ha.2
    refine ⟨?_, hlength⟩
    rw [originalOrientedTraffic_cube_eq_preimage] at hx
    exact hx
  · left
    change a.1+0 ∈ originalCenteredPhysicalCubeRegion b (2*R) ∧
      a.1+0 ∉ originalCenteredPhysicalCubeRegion b (2*(R-2*(originalStageFrameCollarFactor b*ell)))
    simpa only [add_zero] using And.intro ha.1 hx

namespace OriginalSeedConditionalMoments
variable (D : OriginalSeedConditionalMoments S w μ ν)
include D

/-- A genuine short target port in the chosen physical deep cube would have been retained.
The resulting expected target count uses the original Campbell/Palm law. -/
theorem lintegral_originalOrientedStageTargetPorts_le_collar_and_pathTail
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {kin : ℝ → ℝ → (Fin (finrank ℝ S.covector.ker) → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (Q : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν kin g)
    (b : OrthonormalBasis (Fin (finrank ℝ S.covector.ker)) ℝ
      (EuclideanSpace ℝ (Fin (finrank ℝ S.covector.ker))))
    {R ell : ℝ} (hell : 0 ≤ ell) (hR : 3*(originalStageFrameCollarFactor b*ell) ≤ R) :
    let K := originalCenteredPhysicalCubeRegion b (2*R)
    (∫⁻ scene, (originalStageWindowTargetPortPlan (originalOrientedPathLengthRetained S w b R ell)
        K scene : Measure (LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker))) univ
      ∂(Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker)))) ≤
      volume (K \ originalCenteredPhysicalCubeRegion b (2*(R-3*(originalStageFrameCollarFactor b*ell)))) +
      volume K * (legalMarkedJointPalm (finrank ℝ S.covector.ker) Q.law)
        {m | ell < originalSeedPairPathLength S w m} := by
  dsimp only
  have hK := measurableSet_originalOrientedTraffic_cube b R
  have hK₀ := measurableSet_originalOrientedTraffic_cube b (R-3*(originalStageFrameCollarFactor b*ell))
  have hA := measurableSet_originalOrientedPathLengthRetained S hF hw b R ell
  simp_rw [originalStageWindowTargetPortPlan_mass_eq_pairKernel hA hK]
  apply Q.lintegral_original_count_le_collar_and_markTail Prod.snd measurable_snd hK hK₀
    (measurableSet_lt measurable_const (measurable_originalSeedPairPathLength S hF hw))
  filter_upwards [D.ae_ae_original_pairKernel_interior_forward Q] with scene hs
  filter_upwards [hs] with a ha
  intro hport
  change a.1+a.2.2 ∈ originalCenteredPhysicalCubeRegion b (2*R) ∧
    a ∉ originalOrientedPathLengthRetained S w b R ell at hport
  by_cases hx : a.1+a.2.2 ∈ originalCenteredPhysicalCubeRegion b
      (2*(R-3*(originalStageFrameCollarFactor b*ell)))
  · right
    change a.1+a.2.2 ∈ originalCenteredPhysicalCubeRegion b (2*R) ∧ ell < originalSeedPairPathLength S w a.2
    refine ⟨hport.1, lt_of_not_ge ?_⟩
    intro hlength
    have hpath : originalSeedCompletePath S w a.1 a.2 a.2.1.2 ∈
        originalCenteredPhysicalCubeRegion b (2*(R-3*(originalStageFrameCollarFactor b*ell))) := by
      simpa only [D.originalSeedCompletePath_target hF hw a.1 a.2 ha.1 ha.2.1 ha.2.2] using hx
    exact hport.2 (D.originalOrientedPathLengthRetained_of_path_mem_deepCube hF hw b hell hR
      ha.1 ha.2.1 (right_mem_Icc.mpr ha.2.2.le) hpath hlength)
  · exact Or.inl ⟨hport.1, hx⟩

end OriginalSeedConditionalMoments
end OTSelector.Reconstruction
