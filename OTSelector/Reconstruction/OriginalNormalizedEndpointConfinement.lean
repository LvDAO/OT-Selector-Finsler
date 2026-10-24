import OTSelector.Reconstruction.FinslerOriginalNormalizedPhaseTargetContainment
import OTSelector.Reconstruction.NormalizedComplianceOperatorCurve
import OTSelector.Reconstruction.PositiveComplianceBounds

/-! Literal original source and target endpoints are controlled by the same
normalized path position, momentum and actual short compliance leg. -/
open Set Matrix Module Manifold MeasureTheory
open scoped ContDiff Matrix.Norms.Operator
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Geometry ContinuousFinslerNorm
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option linter.unusedSectionVars false

/-- A scalar semidefinite upper bound produces one deterministic operator-norm
bound, uniformly over the actual positive compliance matrices. -/
theorem exists_norm_bound_of_posSemidef_scalar_upper
    {ι : Type*} [Fintype ι] [DecidableEq ι] (C : ℝ) :
    ∃ B ≥ 0, ∀ A : Matrix ι ι ℝ, A.PosSemidef →
      (C • 1 - A).PosSemidef → ‖A‖ ≤ B := by
  obtain ⟨B, hB, hbound⟩ := exists_norm_bound_of_posSemidef_trace_le
    (n := ι) (C * Fintype.card ι)
  refine ⟨B, hB, fun A hA hu ↦ hbound A hA ?_⟩
  have ht := hu.trace_nonneg
  simp only [Matrix.trace_sub, Matrix.trace_smul, Matrix.trace_one, smul_eq_mul] at ht
  linarith

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {S : CalibratedLevelSeedPatch F u} {w : S.covector.ker} {μ ν : Measure ℝ}
namespace OriginalSeedConditionalMoments
variable (D : OriginalSeedConditionalMoments S w μ ν)

/-- The original physical source is the cut position minus its own short leg,
in the unchanged common normalization. -/
theorem normalizedMomentumNode_source_identity
    (T : Matrix (Fin (finrank ℝ S.covector.ker)) (Fin (finrank ℝ S.covector.ker)) ℝ)
    [Invertible T] {cut : ℝ}
    (e : LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker))
    (ha : e.1.2 ∈ D.sourcePhaseClocks cut) :
    T *ᵥ e.1.1 = normalizedMomentumNodePosition S w T (cut + S.level) e -
      (T * D.sourcePhaseLeg cut e.1.2 * Tᵀ) *ᵥ normalizedMomentumNodeValue S w T e := by
  have hpath : originalSeedCompletePath S w e.1.1 (physicalPairAnchor e).2 (cut + S.level) =
      e.1.1 + D.sourcePhaseLeg cut e.1.2 *ᵥ
        originalSeedPairMomentum S w (physicalPairAnchor e).2 := by
    simp only [originalSeedCompletePath, sourcePhaseLeg, physicalPairAnchor,
      indicator_of_mem ha, add_sub_cancel_right]
  change T *ᵥ e.1.1 = T *ᵥ originalSeedCompletePath S w e.1.1
    (physicalPairAnchor e).2 (cut + S.level) -
      (T * D.sourcePhaseLeg cut e.1.2 * Tᵀ) *ᵥ
        ((Tᵀ)⁻¹ *ᵥ originalSeedPairMomentum S w (physicalPairAnchor e).2)
  rw [compliance_congruence_path_offset, hpath, Matrix.mulVec_add]
  abel

/-- The unchanged original target is the same cut position plus its target
leg; target confinement never imposes a source confinement condition. -/
theorem normalizedMomentumNode_target_identity
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    (T : Matrix (Fin (finrank ℝ S.covector.ker)) (Fin (finrank ℝ S.covector.ker)) ℝ)
    [Invertible T] {cut : ℝ} (hcut : cut ∈ Ioo D.lo D.hi)
    (e : LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker))
    (ha : e.1.2 ∈ D.sourcePhaseClocks cut) (hb : e.2.2 ∈ D.targetPhaseClocks cut) :
    T *ᵥ e.2.1 = normalizedMomentumNodePosition S w T (cut + S.level) e +
      (T * D.targetPhaseLeg cut e.2.2 * Tᵀ) *ᵥ normalizedMomentumNodeValue S w T e := by
  have hab : (physicalPairAnchor e).2.1.1 < (physicalPairAnchor e).2.1.2 := by
    change e.1.2 < e.2.2
    linarith [ha.2, hb.1]
  have ht := D.originalSeedCompletePath_target_eq_cut_add_leg hF hw e.1.1
    (physicalPairAnchor e).2 ⟨ha.1, ha.2.trans hcut.2⟩
    (by simpa only [add_sub_cancel_right] using hcut)
    ⟨hcut.1.trans hb.1, hb.2⟩ hab (c := cut + S.level)
  have hpath : originalSeedCompletePath S w e.1.1 (physicalPairAnchor e).2 (cut + S.level) +
      D.targetPhaseLeg cut e.2.2 *ᵥ originalSeedPairMomentum S w (physicalPairAnchor e).2 = e.2.1 := by
    have htarget : e.1.1 + (physicalPairAnchor e).2.2 = e.2.1 := by
      dsimp [physicalPairAnchor]
      abel
    have hp : originalSeedCompletePath S w e.1.1 (physicalPairAnchor e).2 (cut + S.level) +
        D.targetPhaseLeg cut e.2.2 *ᵥ originalSeedPairMomentum S w (physicalPairAnchor e).2 =
          e.1.1 + (physicalPairAnchor e).2.2 := by
      simpa only [targetPhaseLeg, physicalPairAnchor, indicator_of_mem hb,
        originalSeedClockCompliance, add_sub_cancel_right] using ht.symm
    exact hp.trans htarget
  change T *ᵥ e.2.1 = T *ᵥ originalSeedCompletePath S w e.1.1
    (physicalPairAnchor e).2 (cut + S.level) +
      (T * D.targetPhaseLeg cut e.2.2 * Tᵀ) *ᵥ
        ((Tᵀ)⁻¹ *ᵥ originalSeedPairMomentum S w (physicalPairAnchor e).2)
  rw [compliance_congruence_path_offset, ← Matrix.mulVec_add, hpath]

/-- The actual short source leg turns the actual path/momentum bounds into a
physical source bound, without changing its normalizer. -/
theorem normalizedMomentumNode_source_norm_le
    (T : Matrix (Fin (finrank ℝ S.covector.ker)) (Fin (finrank ℝ S.covector.ker)) ℝ)
    [Invertible T] {cut : ℝ}
    (e : LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker))
    (ha : e.1.2 ∈ D.sourcePhaseClocks cut) {Z P B : ℝ} (hB : 0 ≤ B)
    (hz : ‖normalizedMomentumNodePosition S w T (cut + S.level) e‖ ≤ Z)
    (hp : ‖normalizedMomentumNodeValue S w T e‖ ≤ P)
    (hleg : ‖T * D.sourcePhaseLeg cut e.1.2 * Tᵀ‖ ≤ B) :
    ‖T *ᵥ e.1.1‖ ≤ Z + B * P := by
  rw [D.normalizedMomentumNode_source_identity T e ha]
  have hmul := (matrixPhaseOperator (T * D.sourcePhaseLeg cut e.1.2 * Tᵀ)).le_opNorm
    (normalizedMomentumNodeValue S w T e)
  rw [matrixPhaseOperator_apply, norm_matrixPhaseOperator] at hmul
  have hb := (mul_le_mul_of_nonneg_right hleg (norm_nonneg _)).trans
    (mul_le_mul_of_nonneg_left hp hB)
  exact (norm_sub_le _ _).trans (add_le_add hz (hmul.trans hb))

/-- The same estimate controls the actual physical target by its short target
leg, retaining the target anchor used by the exact Campbell formula. -/
theorem normalizedMomentumNode_target_norm_le
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    (T : Matrix (Fin (finrank ℝ S.covector.ker)) (Fin (finrank ℝ S.covector.ker)) ℝ)
    [Invertible T] {cut : ℝ} (hcut : cut ∈ Ioo D.lo D.hi)
    (e : LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker))
    (ha : e.1.2 ∈ D.sourcePhaseClocks cut) (hb : e.2.2 ∈ D.targetPhaseClocks cut)
    {Z P B : ℝ} (hB : 0 ≤ B)
    (hz : ‖normalizedMomentumNodePosition S w T (cut + S.level) e‖ ≤ Z)
    (hp : ‖normalizedMomentumNodeValue S w T e‖ ≤ P)
    (hleg : ‖T * D.targetPhaseLeg cut e.2.2 * Tᵀ‖ ≤ B) :
    ‖T *ᵥ e.2.1‖ ≤ Z + B * P := by
  rw [D.normalizedMomentumNode_target_identity hF hw T hcut e ha hb]
  have hmul := (matrixPhaseOperator (T * D.targetPhaseLeg cut e.2.2 * Tᵀ)).le_opNorm
    (normalizedMomentumNodeValue S w T e)
  rw [matrixPhaseOperator_apply, norm_matrixPhaseOperator] at hmul
  have hb' := (mul_le_mul_of_nonneg_right hleg (norm_nonneg _)).trans
    (mul_le_mul_of_nonneg_left hp hB)
  exact (norm_add_le _ _).trans (add_le_add hz (hmul.trans hb'))

end OriginalSeedConditionalMoments
end OTSelector.Reconstruction
