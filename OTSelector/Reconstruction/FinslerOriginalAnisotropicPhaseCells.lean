import OTSelector.Reconstruction.FinslerOriginalPhaseSourceCells
import OTSelector.Reconstruction.MarkedPhaseCellCongruence

/-!
# Actual Finsler phase cells in arbitrary fixed anisotropic frames

Every deterministic original source or target clock restriction retains finite
phase-cell intensity after the true compliance congruence. No new determinant
moment or matrix lower-bound assumption is introduced.
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
/-- The true normalized source compliance has finite phase-cell intensity on every original
mark subfamily. Both the spatial frame and compliance congruence may be anisotropic. -/
theorem sourcePhaseCell_congruence_intensity_lt_top [SFinite μ]
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {cut : ℝ} (hcut : cut ∈ Ioo D.lo D.hi)
    (T : Matrix (Fin (finrank ℝ S.covector.ker)) (Fin (finrank ℝ S.covector.ker)) ℝ)
    {L : Matrix (Fin (finrank ℝ S.covector.ker)) (Fin (finrank ℝ S.covector.ker)) ℝ}
    (hL : IsUnit L.det) {c : ℝ → (Fin (finrank ℝ S.covector.ker) → ℝ)}
    (hc : Measurable c) {B : Set ℝ} (hB : B ⊆ D.sourcePhaseClocks cut) (R : ℝ) :
    ((volume : Measure (Fin (finrank ℝ S.covector.ker) → ℝ)).prod μ)
      (markedPhaseSourceCell L (fun a ↦ T * D.sourcePhaseLeg cut a * Tᵀ) c B R) < (∞ : ℝ≥0∞) := by
  obtain ⟨C, hC, hbound⟩ := exists_prod_volume_markedPhaseSourceCell_congruence_bound T
  have hrate := hbound hL (D.measurable_sourcePhaseLeg hF hw hcut)
    (D.sourcePhaseLeg_posSemidef hF hw hcut) hc (D.measurableSet_sourcePhaseClocks cut) μ R
  have hfin := D.sourcePhaseCell_intensity_lt_top hF hw hcut hL hc R
  apply (measure_mono (show markedPhaseSourceCell L
      (fun a ↦ T * D.sourcePhaseLeg cut a * Tᵀ) c B R ⊆
      markedPhaseSourceCell L (fun a ↦ T * D.sourcePhaseLeg cut a * Tᵀ)
        c (D.sourcePhaseClocks cut) R from fun v hv ↦ ⟨hB hv.1, hv.2⟩)).trans_lt
  exact hrate.trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hfin)

omit [BorelSpace E] in
/-- The unchanged original target law has the same finite normalized envelope on arbitrary
original target-mark restrictions. -/
theorem targetPhaseCell_congruence_intensity_lt_top [SFinite ν]
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {cut : ℝ} (hcut : cut ∈ Ioo D.lo D.hi)
    (T : Matrix (Fin (finrank ℝ S.covector.ker)) (Fin (finrank ℝ S.covector.ker)) ℝ)
    {L : Matrix (Fin (finrank ℝ S.covector.ker)) (Fin (finrank ℝ S.covector.ker)) ℝ}
    (hL : IsUnit L.det) {c : ℝ → (Fin (finrank ℝ S.covector.ker) → ℝ)}
    (hc : Measurable c) {B : Set ℝ} (hB : B ⊆ D.targetPhaseClocks cut) (R : ℝ) :
    ((volume : Measure (Fin (finrank ℝ S.covector.ker) → ℝ)).prod ν)
      (markedPhaseSourceCell L (fun b ↦ T * D.targetPhaseLeg cut b * Tᵀ) c B R) < (∞ : ℝ≥0∞) := by
  obtain ⟨C, hC, hbound⟩ := exists_prod_volume_markedPhaseSourceCell_congruence_bound T
  have hrate := hbound hL (D.measurable_targetPhaseLeg hF hw hcut)
    (D.targetPhaseLeg_posSemidef hF hw hcut) hc (D.measurableSet_targetPhaseClocks cut) ν R
  have hfin := D.targetPhaseCell_intensity_lt_top hF hw hcut hL hc R
  apply (measure_mono (show markedPhaseSourceCell L
      (fun b ↦ T * D.targetPhaseLeg cut b * Tᵀ) c B R ⊆
      markedPhaseSourceCell L (fun b ↦ T * D.targetPhaseLeg cut b * Tᵀ)
        c (D.targetPhaseClocks cut) R from fun v hv ↦ ⟨hB hv.1, hv.2⟩)).trans_lt
  exact hrate.trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hfin)

end OriginalSeedConditionalMoments
end OTSelector.Reconstruction
