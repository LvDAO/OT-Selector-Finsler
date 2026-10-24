import OTSelector.Reconstruction.FinslerOriginalAdaptiveGlobalEnvelope
import OTSelector.Reconstruction.FinslerOriginalTargetPhaseBadEventSecondMoment

/-! # Fixed original target envelope for every admissible actual phase tube -/
open Set Function MeasureTheory Module Manifold Matrix
open scoped ContDiff ENNReal
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Geometry ContinuousFinslerNorm
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 700000
set_option linter.unusedSectionVars false
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {S : CalibratedLevelSeedPatch F u} {w : S.covector.ker} {μ ν : Measure ℝ}
namespace OriginalSeedConditionalMoments
variable (D : OriginalSeedConditionalMoments S w μ ν)

/-- The unchanged target-color envelope of all radius-r tubes at phase scale m. -/
def adaptiveGlobalTargetEnvelope (cut : ℝ) (m : ℕ) (r : ℝ) :
    Set (LegalMarkedPhysicalPoint (finrank ℝ S.covector.ker)) :=
  markedPhaseSourceCell 1 (D.targetPhaseLeg cut) 0 (D.targetPhaseClocks cut) (2 * (m : ℝ) + r)

theorem measurableSet_adaptiveGlobalTargetEnvelope
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {cut : ℝ} (hcut : cut ∈ Ioo D.lo D.hi) (m : ℕ) (r : ℝ) :
    MeasurableSet (D.adaptiveGlobalTargetEnvelope cut m r) :=
  measurableSet_markedPhaseSourceCell 1 (D.measurable_targetPhaseLeg hF hw hcut)
    measurable_const (D.measurableSet_targetPhaseClocks cut) _

theorem adaptiveGlobalTargetEnvelope_intensity_lt_top
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {cut : ℝ} (hcut : cut ∈ Ioo D.lo D.hi) (m : ℕ) (r : ℝ) :
    ((volume : Measure (Fin (finrank ℝ S.covector.ker) → ℝ)).prod ν)
      (D.adaptiveGlobalTargetEnvelope cut m r) < (∞ : ℝ≥0∞) := by
  let _ : IsProbabilityMeasure ν := D.support.target.probability
  exact D.targetPhaseCell_intensity_lt_top hF hw hcut (by simp) measurable_const _

/-- The same radius bound contains the literal target of an actual forward
original edge, through the actual target compliance leg. -/
theorem target_pathPhaseTube_mem_adaptiveGlobalTargetEnvelope
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {cut : ℝ} (hcut : cut ∈ Ioo D.lo D.hi) {m : ℕ}
    (γ : ℝ → Fin (2 * finrank ℝ S.covector.ker) → ℝ)
    (hroot : ‖γ 0‖ ≤ (m : ℝ))
    (hLip : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
      ‖γ s - γ t‖ ≤ (m : ℝ) * |s - t|) {r : ℝ} (hr : 0 ≤ r)
    (x : Fin (finrank ℝ S.covector.ker) → ℝ)
    (edge : PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker)))
    (ha : edge.1.1 - S.level ∈ Ioo D.lo D.hi)
    (hb : edge.1.2 ∈ D.targetPhaseClocks cut) (hab : edge.1.1 < edge.1.2)
    (htube : ∃ t ∈ Icc (0 : ℝ) 1,
      ‖phasePairVector (originalSeedCompletePath S w x edge (cut + S.level))
        (originalSeedPairMomentum S w edge) - γ t‖ ≤ r) :
    (x + edge.2, edge.1.2) ∈ D.adaptiveGlobalTargetEnvelope cut m r := by
  obtain ⟨t, ht, hnear⟩ := htube
  have hphase : ‖phasePairVector (originalSeedCompletePath S w x edge (cut + S.level))
      (originalSeedPairMomentum S w edge)‖ ≤ 2 * (m : ℝ) + r := by
    calc
      _ = ‖(phasePairVector (originalSeedCompletePath S w x edge (cut + S.level))
          (originalSeedPairMomentum S w edge) - γ t) + γ t‖ := by rw [sub_add_cancel]
      _ ≤ _ := norm_add_le _ _
      _ ≤ _ := by linarith [norm_phaseCurve_le_two_mul γ hroot hLip ht]
  have hmem := D.original_pathPhase_target_mem hF hw hcut x 0 0 edge ha hb hab
    (R := 2 * (m : ℝ) + r) (by positivity)
    (by simpa only [sub_zero] using (norm_position_le_phasePairVector _ _).trans hphase)
    (by simpa only [sub_zero] using (norm_momentum_le_phasePairVector _ _).trans hphase)
  have hc : D.targetPhaseCenter cut 0 0 = 0 := by
    funext a
    simp [targetPhaseCenter]
  simpa only [hc, adaptiveGlobalTargetEnvelope] using hmem

end OriginalSeedConditionalMoments
end OTSelector.Reconstruction
