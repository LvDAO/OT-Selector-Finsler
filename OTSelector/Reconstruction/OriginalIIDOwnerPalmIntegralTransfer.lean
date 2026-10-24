import OTSelector.Reconstruction.OriginalIIDFixedCandidatePalmReadout

/-! The same original candidate's owner Palm readout in the exact local
probability root coordinates, retaining arbitrary measured-core mass. -/
open Set Function MeasureTheory ProbabilityTheory
open scoped ENNReal Topology
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability OTSelector.PointProcess
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-- Any measured subset of an original owner uses the original local Haar
root probability restricted to its exact translated preimage. -/
theorem map_originalMacroFrameOwner_root_subset
    {q : ℕ} {K A : Set (Fin q → ℝ)} (hK : MeasurableSet K)
    (hA : MeasurableSet A) (j : ℕ) (hsub : A ⊆ originalMacroFrameOwner q K j) :
    let η := physicalSceneUnitMassHaarLaw (physicalSceneCanonicalMacroCarrier q)
      (physicalScene_centered_unitCube_mass (Fin q))
    ((η : Measure (Fin q → ℝ)).restrict
      ((fun w ↦ originalMacroFrameCenter q j+w) ⁻¹' A)).map
      (fun w ↦ originalMacroFrameCenter q j+w) = volume.restrict A := by
  intro η
  have hpre : (fun w ↦ originalMacroFrameCenter q j+w) ⁻¹' A ⊆
      (fun w ↦ originalMacroFrameCenter q j+w) ⁻¹' originalMacroFrameOwner q K j :=
    preimage_mono hsub
  calc
    _ = (((η : Measure (Fin q → ℝ)).restrict
        ((fun w ↦ originalMacroFrameCenter q j+w) ⁻¹' originalMacroFrameOwner q K j)).restrict
        ((fun w ↦ originalMacroFrameCenter q j+w) ⁻¹' A)).map
        (fun w ↦ originalMacroFrameCenter q j+w) := by
          rw [Measure.restrict_restrict_of_subset hpre]
    _ = (((η : Measure (Fin q → ℝ)).restrict
        ((fun w ↦ originalMacroFrameCenter q j+w) ⁻¹' originalMacroFrameOwner q K j)).map
        (fun w ↦ originalMacroFrameCenter q j+w)).restrict A :=
      (Measure.restrict_map (measurable_const.add measurable_id) hA).symm
    _ = _ := by
      rw [map_originalMacroFrameOwner_root q hK j,Measure.restrict_restrict_of_subset hsub]

attribute [local instance] iidFixedCandidatePalmPointStandardBorel
  iidFixedCandidatePalmPlanPolish iidFixedCandidatePalmInputPolish
  iidFixedCandidatePalmPlanNonempty iidFixedCandidatePalmInputNonempty
  iidFixedCandidatePalmConfigurationTopology iidFixedCandidatePalmConfigurationBorel
  iidFixedCandidatePalmConfigurationPolish

/-- Exact local-root readout of the SAME whole-core candidate on any
measured owner subset. No energy regularity or clock condition is needed. -/
theorem lintegral_originalIIDFixedCandidate_cubePalm_eq_local_owner_subset
    {q : ℕ} (K : Set (Fin q → ℝ)) (hK : MeasurableSet K)
    (Q : ℕ → ProbabilityMeasure
      (OriginalIIDMaskedMacroCarrier (0 : (Fin q → ℝ) × ℝ) ×
        OriginalIIDMaskedMacroCarrier (0 : (Fin q → ℝ) × ℝ))) (j : ℕ)
    (hroot : (originalIIDFixedCandidateFullSceneJoint (Q j)).fst =
      (physicalSceneUnitMassHaarLaw (physicalSceneCanonicalMacroCarrier q)
        (physicalScene_centered_unitCube_mass (Fin q)) : Measure (Fin q → ℝ)))
    (A : Set (Fin q → ℝ)) (hA : MeasurableSet A)
    (hsub : A ⊆ originalMacroFrameOwner q K j)
    (F : (Fin q → ℝ) → PhysicalPairPalmMark (Fin q) → ℝ≥0∞) :
    let η := physicalSceneUnitMassHaarLaw (physicalSceneCanonicalMacroCarrier q)
      (physicalScene_centered_unitCube_mass (Fin q))
    (∫⁻ c in A, ∫⁻ mark, F c mark ∂cubePalm (Fin q) (physicalScenePairCampbell
      ((originalIIDWholeCoreSceneKernel K hK Q c).map Prod.fst)) ∂volume) =
      ∫⁻ w, ∫⁻ mark, F (originalMacroFrameCenter q j+w) mark
        ∂cubePalm (Fin q) (physicalScenePairCampbell
          ((originalIIDFixedCandidatePairPlanJoint (Q j)).condKernel w))
        ∂(η : Measure (Fin q → ℝ)).restrict
          ((fun w ↦ originalMacroFrameCenter q j+w) ⁻¹' A) := by
  intro η
  rw [lintegral_originalIIDFixedCandidate_cubePalm_eq_on_owner_subset K hK Q j hroot hsub F,
    ← map_originalMacroFrameOwner_root_subset hK hA j hsub]
  rw [(measurableEmbedding_addLeft (originalMacroFrameCenter q j)).lintegral_map]
  simp only [add_sub_cancel_left]
  rfl

end OTSelector.Reconstruction
