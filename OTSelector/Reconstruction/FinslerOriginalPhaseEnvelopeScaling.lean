import OTSelector.Reconstruction.FinslerOriginalAdaptiveGlobalEnvelope

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
theorem sourcePhaseCell_intensity_scale
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {cut : ℝ} (hcut : cut ∈ Ioo D.lo D.hi) {R : ℝ} (hR : 0 ≤ R) :
    ((volume : Measure (Fin (finrank ℝ S.covector.ker) → ℝ)).prod μ)
      (markedPhaseSourceCell 1 (D.sourcePhaseLeg cut) 0 (D.sourcePhaseClocks cut) R) =
      ENNReal.ofReal R ^ finrank ℝ S.covector.ker *
        ((volume : Measure (Fin (finrank ℝ S.covector.ker) → ℝ)).prod μ)
          (markedPhaseSourceCell 1 (D.sourcePhaseLeg cut) 0 (D.sourcePhaseClocks cut) 1) := by
  let _ : IsProbabilityMeasure μ := D.support.source.probability
  have hpos (r : ℝ) (hr : 0 ≤ r) :
      0 ≤ phaseSourceCellRadius (Fin (finrank ℝ S.covector.ker)) r := by
    unfold phaseSourceCellRadius
    positivity
  rw [prod_volume_markedPhaseSourceCell (L := (1 : Matrix (Fin (finrank ℝ S.covector.ker)) _ ℝ))
    (c := 0) (by simp) (D.measurable_sourcePhaseLeg hF hw hcut)
    (D.sourcePhaseLeg_posSemidef hF hw hcut) measurable_const
    (D.measurableSet_sourcePhaseClocks cut) μ R,
    prod_volume_markedPhaseSourceCell (L := (1 : Matrix (Fin (finrank ℝ S.covector.ker)) _ ℝ))
      (c := 0) (by simp) (D.measurable_sourcePhaseLeg hF hw hcut)
      (D.sourcePhaseLeg_posSemidef hF hw hcut) measurable_const
      (D.measurableSet_sourcePhaseClocks cut) μ 1]
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
theorem adaptiveGlobalSourceEnvelope_intensity_real
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {cut : ℝ} (hcut : cut ∈ Ioo D.lo D.hi) (m : ℕ) {r : ℝ} (hr : 0 ≤ r) :
    (((volume : Measure (Fin (finrank ℝ S.covector.ker) → ℝ)).prod μ)
      (D.adaptiveGlobalSourceEnvelope cut m r)).toReal =
      (2 * (m : ℝ) + r) ^ finrank ℝ S.covector.ker *
        (((volume : Measure (Fin (finrank ℝ S.covector.ker) → ℝ)).prod μ)
          (markedPhaseSourceCell 1 (D.sourcePhaseLeg cut) 0 (D.sourcePhaseClocks cut) 1)).toReal := by
  unfold adaptiveGlobalSourceEnvelope
  rw [D.sourcePhaseCell_intensity_scale hF hw hcut (by positivity),
    ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_ofReal (by positivity)]

end OriginalSeedConditionalMoments
end OTSelector.Reconstruction
