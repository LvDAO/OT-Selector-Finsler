import OTSelector.Reconstruction.FinslerOriginalCommonScaleMomentumField
import OTSelector.Reconstruction.OriginalNormalizedEndpointConfinement
import OTSelector.Reconstruction.FinslerOriginalNormalizedCompletePathContributors

/-! Literal original endpoints and complete paths retain their original
coordinates. Common phase scaling changes the input-cell frame to δ T⁻¹,
while the actual congruence compliance U remains unchanged. -/
open Set Function MeasureTheory Matrix Module Manifold
open scoped ENNReal NNReal ContDiff Matrix.Norms.Operator
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Geometry ContinuousFinslerNorm
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000
set_option linter.unusedSectionVars false
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {S : CalibratedLevelSeedPatch F u} {w : S.covector.ker} {μ ν : Measure ℝ}
namespace OriginalSeedConditionalMoments
variable (D : OriginalSeedConditionalMoments S w μ ν)

/-- The original physical source uses frame δ T⁻¹ and the unchanged congruence leg. -/
theorem commonScaleNormalizedMomentumNode_source_identity
    (T : Matrix (Fin (finrank ℝ S.covector.ker)) (Fin (finrank ℝ S.covector.ker)) ℝ)
    [Invertible T] {δ : ℝ} (hδ : 0 < δ) {cut : ℝ}
    (e : LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker))
    (ha : e.1.2 ∈ D.sourcePhaseClocks cut) :
    e.1.1 = (δ • T⁻¹) *ᵥ
      (commonScaleNormalizedMomentumNodePosition S w T δ (cut + S.level) e -
        (T * D.sourcePhaseLeg cut e.1.2 * Tᵀ) *ᵥ
          commonScaleNormalizedMomentumNodeValue S w T δ e) := by
  have hs := congrArg (fun v ↦ T⁻¹ *ᵥ v) (D.normalizedMomentumNode_source_identity T e ha)
  rw [Matrix.mulVec_mulVec, Matrix.inv_mul_of_invertible, Matrix.one_mulVec] at hs
  simpa only [commonScaleNormalizedMomentumNodePosition, commonScaleNormalizedMomentumNodeValue,
    Matrix.smul_mulVec, Matrix.mulVec_smul, ← smul_sub, smul_smul,
    inv_mul_cancel₀ hδ.ne', mul_inv_cancel₀ hδ.ne', one_smul] using hs

/-- The original target uses the same cell frame and the opposite phase sign. -/
theorem commonScaleNormalizedMomentumNode_target_identity
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    (T : Matrix (Fin (finrank ℝ S.covector.ker)) (Fin (finrank ℝ S.covector.ker)) ℝ)
    [Invertible T] {δ : ℝ} (hδ : 0 < δ) {cut : ℝ} (hcut : cut ∈ Ioo D.lo D.hi)
    (e : LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker))
    (ha : e.1.2 ∈ D.sourcePhaseClocks cut) (hb : e.2.2 ∈ D.targetPhaseClocks cut) :
    e.2.1 = (δ • T⁻¹) *ᵥ
      (commonScaleNormalizedMomentumNodePosition S w T δ (cut + S.level) e +
        (T * D.targetPhaseLeg cut e.2.2 * Tᵀ) *ᵥ
          commonScaleNormalizedMomentumNodeValue S w T δ e) := by
  have hs := congrArg (fun v ↦ T⁻¹ *ᵥ v)
    (D.normalizedMomentumNode_target_identity hF hw T hcut e ha hb)
  rw [Matrix.mulVec_mulVec, Matrix.inv_mul_of_invertible, Matrix.one_mulVec] at hs
  simpa only [commonScaleNormalizedMomentumNodePosition, commonScaleNormalizedMomentumNodeValue,
    Matrix.smul_mulVec, Matrix.mulVec_smul, ← smul_add, smul_smul,
    inv_mul_cancel₀ hδ.ne', mul_inv_cancel₀ hδ.ne', one_smul] using hs

/-- Actual path evolution is divided by δ, with the identical actual mobility R. -/
theorem commonScaleNormalizedMomentumNode_completePath_identity
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    (T : Matrix (Fin (finrank ℝ S.covector.ker)) (Fin (finrank ℝ S.covector.ker)) ℝ)
    [Invertible T] (δ : ℝ) (e : LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker))
    {cut ell r : ℝ} (ha : e.1.2 - S.level ∈ Ioo D.lo D.hi)
    (hcut : cut ∈ Ioo D.lo D.hi) (hr : cut + ell * r ∈ Ioo D.lo D.hi) :
    commonScaleNormalizedMomentumNodePosition S w T δ (cut + S.level) e +
      originalNormalizedClockMobility S w T (cut + S.level) ell r
        (commonScaleNormalizedMomentumNodeValue S w T δ e) =
      δ⁻¹ • (T *ᵥ originalSeedCompletePath S w e.1.1 (physicalPairAnchor e).2
        (cut + S.level + ell * r)) := by
  simpa only [commonScaleNormalizedMomentumNodePosition, commonScaleNormalizedMomentumNodeValue,
    _root_.map_smul, smul_add] using congrArg (fun v ↦ δ⁻¹ • v)
      (D.normalizedMomentumNode_completePath_identity hF hw T e ha hcut hr)

end OriginalSeedConditionalMoments
end OTSelector.Reconstruction