import OTSelector.Reconstruction.FinslerOriginalAdaptiveTargetGlobalEnvelope

/-! # Exact polynomial growth of the actual complete original phase envelope -/
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

/-- The same original determinant integral appears at every phase radius;
Haar volume gives the exact degree-q growth without a new geometric bound. -/
theorem targetPhaseCell_intensity_scale
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {cut : ℝ} (hcut : cut ∈ Ioo D.lo D.hi) {R : ℝ} (hR : 0 ≤ R) :
    ((volume : Measure (Fin (finrank ℝ S.covector.ker) → ℝ)).prod ν)
      (markedPhaseSourceCell 1 (D.targetPhaseLeg cut) 0 (D.targetPhaseClocks cut) R) =
      ENNReal.ofReal R ^ finrank ℝ S.covector.ker *
        ((volume : Measure (Fin (finrank ℝ S.covector.ker) → ℝ)).prod ν)
          (markedPhaseSourceCell 1 (D.targetPhaseLeg cut) 0 (D.targetPhaseClocks cut) 1) := by
  let _ : IsProbabilityMeasure ν := D.support.target.probability
  have hpos (r : ℝ) (hr : 0 ≤ r) :
      0 ≤ phaseSourceCellRadius (Fin (finrank ℝ S.covector.ker)) r := by
    unfold phaseSourceCellRadius
    positivity
  rw [prod_volume_markedPhaseSourceCell (L := (1 : Matrix (Fin (finrank ℝ S.covector.ker)) _ ℝ))
    (c := 0) (by simp) (D.measurable_targetPhaseLeg hF hw hcut)
    (D.targetPhaseLeg_posSemidef hF hw hcut) measurable_const
    (D.measurableSet_targetPhaseClocks cut) ν R,
    prod_volume_markedPhaseSourceCell (L := (1 : Matrix (Fin (finrank ℝ S.covector.ker)) _ ℝ))
      (c := 0) (by simp) (D.measurable_targetPhaseLeg hF hw hcut)
      (D.targetPhaseLeg_posSemidef hF hw hcut) measurable_const
      (D.measurableSet_targetPhaseClocks cut) ν 1]
  simp only [Matrix.det_one, abs_one, ENNReal.ofReal_one, one_mul,
    Real.volume_pi_closedBall _ (hpos R hR), Real.volume_pi_closedBall _ (hpos 1 zero_le_one)]
  have heq : 2 * phaseSourceCellRadius (Fin (finrank ℝ S.covector.ker)) R =
      R * (2 * phaseSourceCellRadius (Fin (finrank ℝ S.covector.ker)) 1) := by
    unfold phaseSourceCellRadius
    ring
  rw [heq, mul_pow, ENNReal.ofReal_mul (pow_nonneg hR _), ENNReal.ofReal_pow hR]
  simp only [Fintype.card_fin]
  ring

/-- The fixed envelope for all adaptive phase curves has an internally
produced exact polynomial original intensity. -/
theorem adaptiveGlobalTargetEnvelope_intensity_real
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {cut : ℝ} (hcut : cut ∈ Ioo D.lo D.hi) (m : ℕ) {r : ℝ} (hr : 0 ≤ r) :
    (((volume : Measure (Fin (finrank ℝ S.covector.ker) → ℝ)).prod ν)
      (D.adaptiveGlobalTargetEnvelope cut m r)).toReal =
      (2 * (m : ℝ) + r) ^ finrank ℝ S.covector.ker *
        (((volume : Measure (Fin (finrank ℝ S.covector.ker) → ℝ)).prod ν)
          (markedPhaseSourceCell 1 (D.targetPhaseLeg cut) 0 (D.targetPhaseClocks cut) 1)).toReal := by
  unfold adaptiveGlobalTargetEnvelope
  rw [D.targetPhaseCell_intensity_scale hF hw hcut (by positivity),
    ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_ofReal (by positivity)]

end OriginalSeedConditionalMoments
end OTSelector.Reconstruction
