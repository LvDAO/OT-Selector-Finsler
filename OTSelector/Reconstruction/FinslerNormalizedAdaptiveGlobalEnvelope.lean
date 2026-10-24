import OTSelector.Reconstruction.FinslerNormalizedPhaseBadEventSecondMoment
import OTSelector.Reconstruction.FinslerOriginalAdaptiveGlobalEnvelope

/-! A fixed original-source envelope contains every admissible normalized phase tube. -/
open Set Function MeasureTheory Module Manifold Matrix
open scoped ContDiff Topology Matrix.Norms.Operator ENNReal
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Geometry ContinuousFinslerNorm
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 1500000
set_option linter.unusedSectionVars false

/-- Original marked-cell intensity has exact radius homogeneity for any fixed frame.
The same determinant factor is retained, so no condition-number estimate is used. -/
theorem prod_volume_markedPhaseSourceCell_radius_scale
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {L : Matrix ι ι ℝ} (hL : IsUnit L.det) {U : ℝ → Matrix ι ι ℝ}
    (hUm : Measurable U) (hU : ∀ a, (U a).PosSemidef)
    {c : ℝ → (ι → ℝ)} (hc : Measurable c) {B : Set ℝ} (hB : MeasurableSet B)
    (μ : Measure ℝ) [SFinite μ] {R : ℝ} (hR : 0 ≤ R) :
    ((volume : Measure (ι → ℝ)).prod μ) (markedPhaseSourceCell L U c B R) =
      ENNReal.ofReal R ^ Fintype.card ι *
        ((volume : Measure (ι → ℝ)).prod μ) (markedPhaseSourceCell L U c B 1) := by
  have hpos (r : ℝ) (hr : 0 ≤ r) : 0 ≤ phaseSourceCellRadius ι r := by
    unfold phaseSourceCellRadius
    positivity
  rw [prod_volume_markedPhaseSourceCell hL hUm hU hc hB μ R,
    prod_volume_markedPhaseSourceCell hL hUm hU hc hB μ 1]
  simp only [Real.volume_pi_closedBall _ (hpos R hR),
    Real.volume_pi_closedBall _ (hpos 1 zero_le_one)]
  have heq : 2 * phaseSourceCellRadius ι R = R * (2 * phaseSourceCellRadius ι 1) := by
    unfold phaseSourceCellRadius
    ring
  rw [heq, mul_pow, ENNReal.ofReal_mul (pow_nonneg hR _), ENNReal.ofReal_pow hR]
  ring

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {S : CalibratedLevelSeedPatch F u} {w : S.covector.ker} {μ ν : Measure ℝ}
namespace OriginalSeedConditionalMoments
variable (D : OriginalSeedConditionalMoments S w μ ν)

/-- The fixed complete original source envelope for all phase curves of scale m. -/
def normalizedAdaptiveGlobalSourceEnvelope
    (T : Matrix (Fin (finrank ℝ S.covector.ker)) (Fin (finrank ℝ S.covector.ker)) ℝ)
    (cut : ℝ) (m : ℕ) (r : ℝ) :
    Set (LegalMarkedPhysicalPoint (finrank ℝ S.covector.ker)) :=
  D.normalizedSourcePhaseCell T cut 0 0 (2 * (m : ℝ) + r)

theorem measurableSet_normalizedAdaptiveGlobalSourceEnvelope
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    (T : Matrix (Fin (finrank ℝ S.covector.ker)) (Fin (finrank ℝ S.covector.ker)) ℝ)
    [Invertible T] {cut : ℝ} (hcut : cut ∈ Ioo D.lo D.hi) (m : ℕ) (r : ℝ) :
    MeasurableSet (D.normalizedAdaptiveGlobalSourceEnvelope T cut m r) :=
  D.measurableSet_normalizedSourcePhaseCell hF hw T hcut 0 0 _

/-- Original focal determinant integrability supplies finite intensity of the
whole fixed envelope; compactness of its clock-marked shape is unnecessary. -/
theorem normalizedAdaptiveGlobalSourceEnvelope_intensity_lt_top
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    (T : Matrix (Fin (finrank ℝ S.covector.ker)) (Fin (finrank ℝ S.covector.ker)) ℝ)
    [Invertible T] {cut : ℝ} (hcut : cut ∈ Ioo D.lo D.hi) (m : ℕ) (r : ℝ) :
    ((volume : Measure (Fin (finrank ℝ S.covector.ker) → ℝ)).prod μ)
      (D.normalizedAdaptiveGlobalSourceEnvelope T cut m r) < (∞ : ℝ≥0∞) := by
  let _ : IsProbabilityMeasure μ := D.support.source.probability
  exact D.normalizedSourcePhaseCell_intensity_lt_top hF hw T hcut 0 0 _

/-- Every actual path/momentum tube point of any admissible curve belongs
to the same fixed original source envelope, including on its bad event. -/
theorem normalized_source_pathPhaseTube_mem_globalSourceEnvelope
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    (T : Matrix (Fin (finrank ℝ S.covector.ker)) (Fin (finrank ℝ S.covector.ker)) ℝ)
    [Invertible T] {cut : ℝ} (hcut : cut ∈ Ioo D.lo D.hi) {m : ℕ}
    (γ : ℝ → Fin (2 * finrank ℝ S.covector.ker) → ℝ)
    (hroot : ‖γ 0‖ ≤ (m : ℝ))
    (hLip : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
      ‖γ s - γ t‖ ≤ (m : ℝ) * |s - t|) {r : ℝ} (hr : 0 ≤ r)
    (x : Fin (finrank ℝ S.covector.ker) → ℝ)
    (edge : PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker)))
    (ha : edge.1.1 ∈ D.sourcePhaseClocks cut)
    (htube : ∃ t ∈ Icc (0 : ℝ) 1,
      ‖phasePairVector (T *ᵥ originalSeedCompletePath S w x edge (cut + S.level))
        ((Tᵀ)⁻¹ *ᵥ originalSeedPairMomentum S w edge) - γ t‖ ≤ r) :
    (x, edge.1.1) ∈ D.normalizedAdaptiveGlobalSourceEnvelope T cut m r := by
  obtain ⟨t, ht, hnear⟩ := htube
  have hphase : ‖phasePairVector (T *ᵥ originalSeedCompletePath S w x edge (cut + S.level))
      ((Tᵀ)⁻¹ *ᵥ originalSeedPairMomentum S w edge)‖ ≤ 2 * (m : ℝ) + r := by
    calc
      _ = ‖(phasePairVector (T *ᵥ originalSeedCompletePath S w x edge (cut + S.level))
          ((Tᵀ)⁻¹ *ᵥ originalSeedPairMomentum S w edge) - γ t) + γ t‖ := by rw [sub_add_cancel]
      _ ≤ _ := norm_add_le _ _
      _ ≤ _ := by linarith [norm_phaseCurve_le_two_mul γ hroot hLip ht]
  have hmem := D.original_normalized_pathPhase_source_mem hF hw T hcut x 0 0 edge ha
    (R := 2 * (m : ℝ) + r) (by positivity)
    (by simpa only [sub_zero] using
      (norm_position_le_phasePairVector _ _).trans hphase)
    (by simpa only [sub_zero] using
      (norm_momentum_le_phasePairVector _ _).trans hphase)
  simpa only [normalizedAdaptiveGlobalSourceEnvelope] using hmem

/-- The exact original intensity scales by the phase radius to the actual dimension. -/
theorem normalizedSourcePhaseCell_intensity_scale
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    (T : Matrix (Fin (finrank ℝ S.covector.ker)) (Fin (finrank ℝ S.covector.ker)) ℝ)
    [Invertible T] {cut : ℝ} (hcut : cut ∈ Ioo D.lo D.hi) {R : ℝ} (hR : 0 ≤ R) :
    ((volume : Measure (Fin (finrank ℝ S.covector.ker) → ℝ)).prod μ)
      (D.normalizedSourcePhaseCell T cut 0 0 R) =
      ENNReal.ofReal R ^ finrank ℝ S.covector.ker *
        ((volume : Measure (Fin (finrank ℝ S.covector.ker) → ℝ)).prod μ)
          (D.normalizedSourcePhaseCell T cut 0 0 1) := by
  let _ : IsProbabilityMeasure μ := D.support.source.probability
  simpa only [normalizedSourcePhaseCell, Fintype.card_fin] using
    prod_volume_markedPhaseSourceCell_radius_scale
      (T.isUnit_nonsing_inv_det (Matrix.isUnit_det_of_invertible T))
      (D.measurable_normalizedSourcePhaseLeg hF hw T hcut)
      (D.normalizedSourcePhaseLeg_posSemidef hF hw T hcut)
      (D.measurable_normalizedSourcePhaseCenter hF hw T hcut 0 0)
      (D.measurableSet_sourcePhaseClocks cut) μ hR

/-- The deterministic whole envelope has exact polynomial original intensity. -/
theorem normalizedAdaptiveGlobalSourceEnvelope_intensity_real
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    (T : Matrix (Fin (finrank ℝ S.covector.ker)) (Fin (finrank ℝ S.covector.ker)) ℝ)
    [Invertible T] {cut : ℝ} (hcut : cut ∈ Ioo D.lo D.hi) (m : ℕ) {r : ℝ} (hr : 0 ≤ r) :
    (((volume : Measure (Fin (finrank ℝ S.covector.ker) → ℝ)).prod μ)
      (D.normalizedAdaptiveGlobalSourceEnvelope T cut m r)).toReal =
      (2 * (m : ℝ) + r) ^ finrank ℝ S.covector.ker *
        (((volume : Measure (Fin (finrank ℝ S.covector.ker) → ℝ)).prod μ)
          (D.normalizedSourcePhaseCell T cut 0 0 1)).toReal := by
  unfold normalizedAdaptiveGlobalSourceEnvelope
  rw [D.normalizedSourcePhaseCell_intensity_scale hF hw T hcut (by positivity),
    ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_ofReal (by positivity)]

end OriginalSeedConditionalMoments
end OTSelector.Reconstruction
