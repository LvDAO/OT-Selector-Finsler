import OTSelector.LinearAlgebra.Matrix.CoarsePhaseSourceCells
import OTSelector.Reconstruction.FinslerOriginalAnisotropicPhaseCells
import OTSelector.Reconstruction.FinslerOriginalCommonCutCompliance

/-!
# Actual original Finsler endpoints in coarse anisotropic phase-cell envelopes

The physical position and original momentum use the paired normalized frame.
Their bounded coarse phase cell pulls back to the same unchanged original
source or target, and the actual focal determinant moment gives finite true
physical intensity on any deterministic original clock restriction.
-/
open Set Function MeasureTheory Module Manifold Matrix
open scoped ContDiff Topology Matrix.Norms.Operator Classical ENNReal
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Geometry ContinuousFinslerNorm
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {S : CalibratedLevelSeedPatch F u} {w : S.covector.ker} {μ ν : Measure ℝ}
namespace OriginalSeedConditionalMoments
variable (D : OriginalSeedConditionalMoments S w μ ν)

omit [BorelSpace E] in
/-- A true original source belongs to the physical envelope of its normalized phase cell. -/
theorem original_source_mem_coarsePhaseCell_of_path
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {cut : ℝ} (hcut : cut ∈ Ioo D.lo D.hi)
    (T : Matrix (Fin (finrank ℝ S.covector.ker)) (Fin (finrank ℝ S.covector.ker)) ℝ)
    [Invertible T] {ℓ : ℝ} (hℓ : ℓ ≠ 0)
    (x k l : Fin (finrank ℝ S.covector.ker) → ℝ)
    (edge : PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker)))
    {B : Set ℝ} (hB : B ⊆ D.sourcePhaseClocks cut) (ha : edge.1.1 ∈ B)
    {R : ℝ} (hR : 0 ≤ R)
    (hz : ‖ℓ⁻¹ • (T *ᵥ originalSeedCompletePath S w x edge (cut + S.level)) - k‖ ≤ R)
    (hp : ‖ℓ⁻¹ • ((Tᵀ)⁻¹ *ᵥ originalSeedPairMomentum S w edge) - l‖ ≤ R) :
    (x, edge.1.1) ∈ markedPhaseSourceCell (ℓ • T⁻¹)
      (fun a ↦ T * D.sourcePhaseLeg cut a * Tᵀ)
      (coarsePhaseSourceCenter T ℓ (D.sourcePhaseLeg cut) k l) B R := by
  have h := original_source_mem_coarsePhaseCell T hℓ (D.sourcePhaseLeg_posSemidef hF hw hcut)
    k l ha hR hz hp
  have heq : originalSeedCompletePath S w x edge (cut + S.level) -
      D.sourcePhaseLeg cut edge.1.1 *ᵥ originalSeedPairMomentum S w edge = x := by
    simp only [originalSeedCompletePath, sourcePhaseLeg, indicator_of_mem (hB ha),
      add_sub_cancel_right]
  rwa [heq] at h

/-- The paired true original target uses the same coarse normalization and original clock. -/
theorem original_target_mem_coarsePhaseCell_of_path
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {cut : ℝ} (hcut : cut ∈ Ioo D.lo D.hi)
    (T : Matrix (Fin (finrank ℝ S.covector.ker)) (Fin (finrank ℝ S.covector.ker)) ℝ)
    [Invertible T] {ℓ : ℝ} (hℓ : ℓ ≠ 0)
    (x k l : Fin (finrank ℝ S.covector.ker) → ℝ)
    (edge : PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker)))
    (ha : edge.1.1 - (S.level : ℝ) ∈ Ioo D.lo D.hi)
    {B : Set ℝ} (hB : B ⊆ D.targetPhaseClocks cut) (hb : edge.1.2 ∈ B)
    (hab : edge.1.1 < edge.1.2) {R : ℝ} (hR : 0 ≤ R)
    (hz : ‖ℓ⁻¹ • (T *ᵥ originalSeedCompletePath S w x edge (cut + S.level)) - k‖ ≤ R)
    (hp : ‖ℓ⁻¹ • ((Tᵀ)⁻¹ *ᵥ originalSeedPairMomentum S w edge) - l‖ ≤ R) :
    (x + edge.2, edge.1.2) ∈ markedPhaseSourceCell (ℓ • T⁻¹)
      (fun b ↦ T * D.targetPhaseLeg cut b * Tᵀ)
      (coarsePhaseSourceCenter T ℓ (D.targetPhaseLeg cut) k (-l)) B R := by
  have h := original_target_mem_coarsePhaseCell T hℓ (D.targetPhaseLeg_posSemidef hF hw hcut)
    k l hb hR hz hp
  have hb' : edge.1.2 - (S.level : ℝ) ∈ Ioo D.lo D.hi :=
    ⟨hcut.1.trans (hB hb).1, (hB hb).2⟩
  have htarget := D.originalSeedCompletePath_target_eq_cut_add_leg hF hw x edge ha
    (by simpa using hcut) hb' hab (c := cut + S.level)
  have heq : originalSeedCompletePath S w x edge (cut + S.level) +
      D.targetPhaseLeg cut edge.1.2 *ᵥ originalSeedPairMomentum S w edge = x + edge.2 := by
    simpa only [targetPhaseLeg, indicator_of_mem (hB hb), originalSeedClockCompliance,
      add_sub_cancel_right] using htarget.symm
  rwa [heq] at h

omit [BorelSpace E] in
/-- Actual focal source determinant moments internally give finite coarse-cell physical intensity. -/
theorem original_source_coarsePhaseCell_intensity_lt_top [SFinite μ]
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {cut : ℝ} (hcut : cut ∈ Ioo D.lo D.hi)
    (T : Matrix (Fin (finrank ℝ S.covector.ker)) (Fin (finrank ℝ S.covector.ker)) ℝ)
    [Invertible T] {ℓ : ℝ} (hℓ : ℓ ≠ 0)
    (k l : Fin (finrank ℝ S.covector.ker) → ℝ)
    {B : Set ℝ} (hB : B ⊆ D.sourcePhaseClocks cut) (R : ℝ) :
    ((volume : Measure (Fin (finrank ℝ S.covector.ker) → ℝ)).prod μ)
      (markedPhaseSourceCell (ℓ • T⁻¹) (fun a ↦ T * D.sourcePhaseLeg cut a * Tᵀ)
        (coarsePhaseSourceCenter T ℓ (D.sourcePhaseLeg cut) k l) B R) < (∞ : ℝ≥0∞) :=
  D.sourcePhaseCell_congruence_intensity_lt_top hF hw hcut T
    (isUnit_det_coarsePhaseFrame T hℓ)
    (measurable_coarsePhaseSourceCenter T ℓ (D.measurable_sourcePhaseLeg hF hw hcut) k l) hB R

omit [BorelSpace E] in
/-- The unchanged original target law has the same finite actual coarse-cell intensity. -/
theorem original_target_coarsePhaseCell_intensity_lt_top [SFinite ν]
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {cut : ℝ} (hcut : cut ∈ Ioo D.lo D.hi)
    (T : Matrix (Fin (finrank ℝ S.covector.ker)) (Fin (finrank ℝ S.covector.ker)) ℝ)
    [Invertible T] {ℓ : ℝ} (hℓ : ℓ ≠ 0)
    (k l : Fin (finrank ℝ S.covector.ker) → ℝ)
    {B : Set ℝ} (hB : B ⊆ D.targetPhaseClocks cut) (R : ℝ) :
    ((volume : Measure (Fin (finrank ℝ S.covector.ker) → ℝ)).prod ν)
      (markedPhaseSourceCell (ℓ • T⁻¹) (fun b ↦ T * D.targetPhaseLeg cut b * Tᵀ)
        (coarsePhaseSourceCenter T ℓ (D.targetPhaseLeg cut) k (-l)) B R) < (∞ : ℝ≥0∞) :=
  D.targetPhaseCell_congruence_intensity_lt_top hF hw hcut T
    (isUnit_det_coarsePhaseFrame T hℓ)
    (measurable_coarsePhaseSourceCenter T ℓ (D.measurable_targetPhaseLeg hF hw hcut) k (-l)) hB R

end OriginalSeedConditionalMoments
end OTSelector.Reconstruction
