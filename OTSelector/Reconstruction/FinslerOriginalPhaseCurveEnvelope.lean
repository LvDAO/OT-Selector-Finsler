import OTSelector.Finite.SampledLipschitzCurveCover
import OTSelector.Finite.LatticePairCoordinates
import OTSelector.Reconstruction.FinslerOriginalPhaseWalkCandidateCounts

/-!
# Every actual original path phase tube lies in one finite original-input candidate

A bounded-speed phase curve is covered by one literal finite lattice code. The
actual complete path and original momentum then force every relevant unchanged
source into that code's fixed original-input envelope. A later adaptive curve
uses the already proved all-candidate original Poisson event.
-/
open Set Function MeasureTheory Module Manifold Matrix
open scoped ContDiff Topology Matrix.Norms.Operator Classical ENNReal
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Geometry ContinuousFinslerNorm
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {S : CalibratedLevelSeedPatch F u} {w : S.covector.ker} {μ ν : Measure ℝ}
namespace OriginalSeedConditionalMoments
variable (D : OriginalSeedConditionalMoments S w μ ν)

omit [BorelSpace E] in
/-- All actual source endpoints whose true path/momentum phase lies in the curve tube belong
to one of the finite original source candidates. The curve may be selected after seeing the input. -/
theorem exists_sourcePhaseWalkEnvelope_containing_pathPhaseTube
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {cut : ℝ} (hcut : cut ∈ Ioo D.lo D.hi) {m : ℕ} (hm : 1 ≤ m)
    (γ : ℝ → Fin (2 * finrank ℝ S.covector.ker) → ℝ)
    (hroot : ‖γ 0‖ ≤ (m : ℝ))
    (hLip : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
      ‖γ s - γ t‖ ≤ (m : ℝ) * |s - t|) {r : ℝ} (hr : 0 ≤ r) :
    ∃ code : PhaseWalkCode (2 * finrank ℝ S.covector.ker) m,
      ∀ (x : Fin (finrank ℝ S.covector.ker) → ℝ)
        (edge : PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker))),
      edge.1.1 ∈ D.sourcePhaseClocks cut →
      (∃ t ∈ Icc (0 : ℝ) 1,
        ‖phasePairVector (originalSeedCompletePath S w x edge (cut + S.level))
          (originalSeedPairMomentum S w edge) - γ t‖ ≤ r) →
      (x, edge.1.1) ∈ D.sourcePhaseWalkEnvelope cut
        (fun code j ↦ phaseWalkPosition code j) (fun code j ↦ phaseWalkMomentum code j)
        code (r + 2) := by
  obtain ⟨code, hcover⟩ := exists_phaseWalkCode_cover_of_curve hm γ hroot hLip
  refine ⟨code, fun x edge ha htube ↦ ?_⟩
  obtain ⟨t, ht, hnear⟩ := htube
  obtain ⟨j, hj⟩ := hcover t ht
  have hphase : ‖phasePairVector (originalSeedCompletePath S w x edge (cut + S.level))
      (originalSeedPairMomentum S w edge) - phaseWalkVertex code j‖ ≤ r + 2 := by
    exact (norm_sub_le_norm_sub_add_norm_sub _ _ _).trans (add_le_add hnear hj)
  change (x, edge.1.1) ∈ ⋃ j : Fin (m + 1), markedPhaseSourceCell 1 (D.sourcePhaseLeg cut)
    (D.sourcePhaseCenter cut (phaseWalkPosition code j) (phaseWalkMomentum code j))
      (D.sourcePhaseClocks cut) (r + 2)
  apply Set.mem_iUnion.mpr
  refine ⟨j, ?_⟩
  exact D.original_pathPhase_source_mem hF hw hcut x (phaseWalkPosition code j)
    (phaseWalkMomentum code j) edge ha (by linarith)
    ((norm_position_sub_phaseWalkPosition_le _ _ code j).trans hphase)
    ((norm_momentum_sub_phaseWalkMomentum_le _ _ code j).trans hphase)

end OriginalSeedConditionalMoments
end OTSelector.Reconstruction
