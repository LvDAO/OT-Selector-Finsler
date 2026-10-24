import OTSelector.Reconstruction.FinslerNormalizedTargetPhaseBadEventSecondMoment
import OTSelector.Reconstruction.FinslerNormalizedAdaptiveGlobalEnvelope

/-! A fixed original-target envelope contains every admissible normalized phase tube. -/
open Set Function MeasureTheory Module Manifold Matrix
open scoped ContDiff Topology Matrix.Norms.Operator ENNReal
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Geometry ContinuousFinslerNorm
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 1500000
set_option linter.unusedSectionVars false

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {S : CalibratedLevelSeedPatch F u} {w : S.covector.ker} {μ ν : Measure ℝ}
namespace OriginalSeedConditionalMoments
variable (D : OriginalSeedConditionalMoments S w μ ν)

/-- The fixed complete original target envelope for all phase curves of scale m. -/
def normalizedAdaptiveGlobalTargetEnvelope
    (T : Matrix (Fin (finrank ℝ S.covector.ker)) (Fin (finrank ℝ S.covector.ker)) ℝ)
    (cut : ℝ) (m : ℕ) (r : ℝ) :
    Set (LegalMarkedPhysicalPoint (finrank ℝ S.covector.ker)) :=
  D.normalizedTargetPhaseCell T cut 0 0 (2 * (m : ℝ) + r)

theorem measurableSet_normalizedAdaptiveGlobalTargetEnvelope
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    (T : Matrix (Fin (finrank ℝ S.covector.ker)) (Fin (finrank ℝ S.covector.ker)) ℝ)
    [Invertible T] {cut : ℝ} (hcut : cut ∈ Ioo D.lo D.hi) (m : ℕ) (r : ℝ) :
    MeasurableSet (D.normalizedAdaptiveGlobalTargetEnvelope T cut m r) :=
  D.measurableSet_normalizedTargetPhaseCell hF hw T hcut 0 0 _

/-- Original focal determinant integrability supplies finite intensity of the
whole fixed envelope; compactness of its clock-marked shape is unnecessary. -/
theorem normalizedAdaptiveGlobalTargetEnvelope_intensity_lt_top
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    (T : Matrix (Fin (finrank ℝ S.covector.ker)) (Fin (finrank ℝ S.covector.ker)) ℝ)
    [Invertible T] {cut : ℝ} (hcut : cut ∈ Ioo D.lo D.hi) (m : ℕ) (r : ℝ) :
    ((volume : Measure (Fin (finrank ℝ S.covector.ker) → ℝ)).prod ν)
      (D.normalizedAdaptiveGlobalTargetEnvelope T cut m r) < (∞ : ℝ≥0∞) := by
  let _ : IsProbabilityMeasure ν := D.support.target.probability
  exact D.normalizedTargetPhaseCell_intensity_lt_top hF hw T hcut 0 0 _

/-- Every actual path/momentum tube point of any admissible curve belongs
to the same fixed original target envelope, including on its bad event. -/
theorem normalized_target_pathPhaseTube_mem_globalTargetEnvelope
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    (T : Matrix (Fin (finrank ℝ S.covector.ker)) (Fin (finrank ℝ S.covector.ker)) ℝ)
    [Invertible T] {cut : ℝ} (hcut : cut ∈ Ioo D.lo D.hi) {m : ℕ}
    (γ : ℝ → Fin (2 * finrank ℝ S.covector.ker) → ℝ)
    (hroot : ‖γ 0‖ ≤ (m : ℝ))
    (hLip : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
      ‖γ s - γ t‖ ≤ (m : ℝ) * |s - t|) {r : ℝ} (hr : 0 ≤ r)
    (x : Fin (finrank ℝ S.covector.ker) → ℝ)
    (edge : PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker)))
    (ha : edge.1.1 - S.level ∈ Ioo D.lo D.hi)
    (hb : edge.1.2 ∈ D.targetPhaseClocks cut) (hab : edge.1.1 < edge.1.2)
    (htube : ∃ t ∈ Icc (0 : ℝ) 1,
      ‖phasePairVector (T *ᵥ originalSeedCompletePath S w x edge (cut + S.level))
        ((Tᵀ)⁻¹ *ᵥ originalSeedPairMomentum S w edge) - γ t‖ ≤ r) :
    (x + edge.2, edge.1.2) ∈ D.normalizedAdaptiveGlobalTargetEnvelope T cut m r := by
  obtain ⟨t, ht, hnear⟩ := htube
  have hphase : ‖phasePairVector (T *ᵥ originalSeedCompletePath S w x edge (cut + S.level))
      ((Tᵀ)⁻¹ *ᵥ originalSeedPairMomentum S w edge)‖ ≤ 2 * (m : ℝ) + r := by
    calc
      _ = ‖(phasePairVector (T *ᵥ originalSeedCompletePath S w x edge (cut + S.level))
          ((Tᵀ)⁻¹ *ᵥ originalSeedPairMomentum S w edge) - γ t) + γ t‖ := by rw [sub_add_cancel]
      _ ≤ _ := norm_add_le _ _
      _ ≤ _ := by linarith [norm_phaseCurve_le_two_mul γ hroot hLip ht]
  have hmem := D.original_normalized_pathPhase_target_mem hF hw T hcut x 0 0 edge ha hb hab
    (R := 2 * (m : ℝ) + r) (by positivity)
    (by simpa only [sub_zero] using
      (norm_position_le_phasePairVector _ _).trans hphase)
    (by simpa only [sub_zero] using
      (norm_momentum_le_phasePairVector _ _).trans hphase)
  simpa only [normalizedAdaptiveGlobalTargetEnvelope] using hmem

/-- The exact original intensity scales by the phase radius to the actual dimension. -/
theorem normalizedTargetPhaseCell_intensity_scale
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    (T : Matrix (Fin (finrank ℝ S.covector.ker)) (Fin (finrank ℝ S.covector.ker)) ℝ)
    [Invertible T] {cut : ℝ} (hcut : cut ∈ Ioo D.lo D.hi) {R : ℝ} (hR : 0 ≤ R) :
    ((volume : Measure (Fin (finrank ℝ S.covector.ker) → ℝ)).prod ν)
      (D.normalizedTargetPhaseCell T cut 0 0 R) =
      ENNReal.ofReal R ^ finrank ℝ S.covector.ker *
        ((volume : Measure (Fin (finrank ℝ S.covector.ker) → ℝ)).prod ν)
          (D.normalizedTargetPhaseCell T cut 0 0 1) := by
  let _ : IsProbabilityMeasure ν := D.support.target.probability
  simpa only [normalizedTargetPhaseCell, Fintype.card_fin] using
    prod_volume_markedPhaseSourceCell_radius_scale
      (T.isUnit_nonsing_inv_det (Matrix.isUnit_det_of_invertible T))
      (D.measurable_normalizedTargetPhaseLeg hF hw T hcut)
      (D.normalizedTargetPhaseLeg_posSemidef hF hw T hcut)
      (D.measurable_normalizedTargetPhaseCenter hF hw T hcut 0 0)
      (D.measurableSet_targetPhaseClocks cut) ν hR

/-- The deterministic whole envelope has exact polynomial original intensity. -/
theorem normalizedAdaptiveGlobalTargetEnvelope_intensity_real
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    (T : Matrix (Fin (finrank ℝ S.covector.ker)) (Fin (finrank ℝ S.covector.ker)) ℝ)
    [Invertible T] {cut : ℝ} (hcut : cut ∈ Ioo D.lo D.hi) (m : ℕ) {r : ℝ} (hr : 0 ≤ r) :
    (((volume : Measure (Fin (finrank ℝ S.covector.ker) → ℝ)).prod ν)
      (D.normalizedAdaptiveGlobalTargetEnvelope T cut m r)).toReal =
      (2 * (m : ℝ) + r) ^ finrank ℝ S.covector.ker *
        (((volume : Measure (Fin (finrank ℝ S.covector.ker) → ℝ)).prod ν)
          (D.normalizedTargetPhaseCell T cut 0 0 1)).toReal := by
  unfold normalizedAdaptiveGlobalTargetEnvelope
  rw [D.normalizedTargetPhaseCell_intensity_scale hF hw T hcut (by positivity),
    ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_ofReal (by positivity)]

end OriginalSeedConditionalMoments
end OTSelector.Reconstruction
