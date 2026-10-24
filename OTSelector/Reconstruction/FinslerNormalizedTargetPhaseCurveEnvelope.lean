import OTSelector.Finite.SampledLipschitzCurveCover
import OTSelector.Finite.LatticePairCoordinates
import OTSelector.Reconstruction.FinslerNormalizedTargetPhaseWalkCandidateCounts

/-! Finite original-input envelopes contain every tube in the actual normalized phase frame. -/
open Set Function MeasureTheory Module Manifold Matrix
open scoped ContDiff Topology Matrix.Norms.Operator Classical ENNReal
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Geometry ContinuousFinslerNorm
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 1800000
set_option linter.unusedSectionVars false
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {S : CalibratedLevelSeedPatch F u} {w : S.covector.ker} {μ ν : Measure ℝ}
namespace OriginalSeedConditionalMoments
variable (D : OriginalSeedConditionalMoments S w μ ν)

/-- A normalized actual path/momentum tube lies in one deterministic original-target
candidate at the same phase radius. A later adaptive choice of curve uses the same cover. -/
theorem exists_normalizedTargetPhaseWalkEnvelope_containing_pathPhaseTube
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    (T : Matrix (Fin (finrank ℝ S.covector.ker)) (Fin (finrank ℝ S.covector.ker)) ℝ)
    [Invertible T] {cut : ℝ} (hcut : cut ∈ Ioo D.lo D.hi) {m : ℕ} (hm : 1 ≤ m)
    (γ : ℝ → Fin (2 * finrank ℝ S.covector.ker) → ℝ)
    (hroot : ‖γ 0‖ ≤ (m : ℝ))
    (hLip : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
      ‖γ s - γ t‖ ≤ (m : ℝ) * |s - t|) {r : ℝ} (hr : 0 ≤ r) :
    ∃ code : PhaseWalkCode (2 * finrank ℝ S.covector.ker) m,
      ∀ (x : Fin (finrank ℝ S.covector.ker) → ℝ)
        (edge : PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker))),
      edge.1.1 - S.level ∈ Ioo D.lo D.hi →
      edge.1.2 ∈ D.targetPhaseClocks cut → edge.1.1 < edge.1.2 →
      (∃ t ∈ Icc (0 : ℝ) 1,
        ‖phasePairVector (T *ᵥ originalSeedCompletePath S w x edge (cut + S.level))
          ((Tᵀ)⁻¹ *ᵥ originalSeedPairMomentum S w edge) - γ t‖ ≤ r) →
      (x + edge.2, edge.1.2) ∈ D.normalizedTargetPhaseWalkEnvelope T cut
        (fun code j ↦ phaseWalkPosition code j) (fun code j ↦ phaseWalkMomentum code j)
        code (r + 2) := by
  obtain ⟨code, hcover⟩ := exists_phaseWalkCode_cover_of_curve hm γ hroot hLip
  refine ⟨code, fun x edge ha hb hab htube ↦ ?_⟩
  obtain ⟨t, ht, hnear⟩ := htube
  obtain ⟨j, hj⟩ := hcover t ht
  have hphase : ‖phasePairVector
      (T *ᵥ originalSeedCompletePath S w x edge (cut + S.level))
      ((Tᵀ)⁻¹ *ᵥ originalSeedPairMomentum S w edge) - phaseWalkVertex code j‖ ≤ r + 2 :=
    (norm_sub_le_norm_sub_add_norm_sub _ _ _).trans (add_le_add hnear hj)
  change (x + edge.2, edge.1.2) ∈ ⋃ j : Fin (m + 1), D.normalizedTargetPhaseCell T cut
    (phaseWalkPosition code j) (phaseWalkMomentum code j) (r + 2)
  apply Set.mem_iUnion.mpr
  refine ⟨j, ?_⟩
  exact D.original_normalized_pathPhase_target_mem hF hw T hcut x
    (phaseWalkPosition code j) (phaseWalkMomentum code j) edge ha hb hab (by linarith)
    ((norm_position_sub_phaseWalkPosition_le _ _ code j).trans hphase)
    ((norm_momentum_sub_phaseWalkMomentum_le _ _ code j).trans hphase)

end OriginalSeedConditionalMoments
end OTSelector.Reconstruction
