import OTSelector.Reconstruction.FinslerOriginalAnisotropicPhaseCells
import OTSelector.Reconstruction.FinslerOriginalNormalizedMomentumEligibleNodes
import OTSelector.LinearAlgebra.Matrix.ComplianceCongruenceCovariance
import OTSelector.Reconstruction.FinslerOriginalCommonCutCompliance

/-! Deterministic original target cells for the exact normalized phase frame.
The radius is retained without any condition-number enlargement. -/
open Set Function Filter MeasureTheory Matrix Module Manifold
open scoped ENNReal NNReal ContDiff Matrix.Norms.Operator Classical
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Geometry ContinuousFinslerNorm
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {S : CalibratedLevelSeedPatch F u} {w : S.covector.ker} {μ ν : Measure ℝ}

namespace OriginalSeedConditionalMoments
variable (D : OriginalSeedConditionalMoments S w μ ν)

/-- The original physical target center pulled back from a normalized phase center. -/
def normalizedTargetPhaseCenter
    (T : Matrix (Fin (finrank ℝ S.covector.ker)) (Fin (finrank ℝ S.covector.ker)) ℝ)
    (cut : ℝ) (z₀ p₀ : Fin (finrank ℝ S.covector.ker) → ℝ) (a : ℝ) :=
  T⁻¹ *ᵥ z₀ + D.targetPhaseLeg cut a *ᵥ (Tᵀ *ᵥ p₀)

/-- A deterministic original input cell uses the same normalized compliance and inverse frame. -/
def normalizedTargetPhaseCell
    (T : Matrix (Fin (finrank ℝ S.covector.ker)) (Fin (finrank ℝ S.covector.ker)) ℝ)
    (cut : ℝ) (z₀ p₀ : Fin (finrank ℝ S.covector.ker) → ℝ) (R : ℝ) :
    Set (LegalMarkedPhysicalPoint (finrank ℝ S.covector.ker)) :=
  markedPhaseSourceCell T⁻¹ (fun a ↦ T * D.targetPhaseLeg cut a * Tᵀ)
    (D.normalizedTargetPhaseCenter T cut z₀ p₀) (D.targetPhaseClocks cut) R

@[simp] theorem normalizedTargetPhaseCenter_zero
    (T : Matrix (Fin (finrank ℝ S.covector.ker)) (Fin (finrank ℝ S.covector.ker)) ℝ)
    (cut : ℝ) : D.normalizedTargetPhaseCenter T cut 0 0 = 0 := by
  funext a
  simp [normalizedTargetPhaseCenter]

theorem measurable_normalizedTargetPhaseCenter
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    (T : Matrix (Fin (finrank ℝ S.covector.ker)) (Fin (finrank ℝ S.covector.ker)) ℝ)
    {cut : ℝ} (hcut : cut ∈ Ioo D.lo D.hi)
    (z₀ p₀ : Fin (finrank ℝ S.covector.ker) → ℝ) :
    Measurable (D.normalizedTargetPhaseCenter T cut z₀ p₀) :=
  measurable_const.add ((completePathMatrixApply (Tᵀ *ᵥ p₀)).continuous.measurable.comp
    (D.measurable_targetPhaseLeg hF hw hcut))

theorem measurable_normalizedTargetPhaseLeg
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    (T : Matrix (Fin (finrank ℝ S.covector.ker)) (Fin (finrank ℝ S.covector.ker)) ℝ)
    {cut : ℝ} (hcut : cut ∈ Ioo D.lo D.hi) :
    Measurable (fun a ↦ T * D.targetPhaseLeg cut a * Tᵀ) := by
  apply Measurable.of_eval_matrix
  intro i j
  simp only [Matrix.mul_apply]
  apply Finset.measurable_sum
  intro k _
  apply Measurable.mul _ measurable_const
  apply Finset.measurable_sum
  intro l _
  exact measurable_const.mul (D.measurable_targetPhaseLeg hF hw hcut).eval.eval

theorem normalizedTargetPhaseLeg_posSemidef
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    (T : Matrix (Fin (finrank ℝ S.covector.ker)) (Fin (finrank ℝ S.covector.ker)) ℝ)
    {cut : ℝ} (hcut : cut ∈ Ioo D.lo D.hi) (a : ℝ) :
    (T * D.targetPhaseLeg cut a * Tᵀ).PosSemidef := by
  simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
    (D.targetPhaseLeg_posSemidef hF hw hcut a).mul_mul_conjTranspose_same T

theorem measurableSet_normalizedTargetPhaseCell
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    (T : Matrix (Fin (finrank ℝ S.covector.ker)) (Fin (finrank ℝ S.covector.ker)) ℝ)
    {cut : ℝ} (hcut : cut ∈ Ioo D.lo D.hi)
    (z₀ p₀ : Fin (finrank ℝ S.covector.ker) → ℝ) (R : ℝ) :
    MeasurableSet (D.normalizedTargetPhaseCell T cut z₀ p₀ R) :=
  measurableSet_markedPhaseSourceCell T⁻¹
    (D.measurable_normalizedTargetPhaseLeg hF hw T hcut)
    (D.measurable_normalizedTargetPhaseCenter hF hw T hcut z₀ p₀)
    (D.measurableSet_targetPhaseClocks cut) R

theorem normalizedTargetPhaseCell_intensity_lt_top [SFinite ν]
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    (T : Matrix (Fin (finrank ℝ S.covector.ker)) (Fin (finrank ℝ S.covector.ker)) ℝ)
    [Invertible T] {cut : ℝ} (hcut : cut ∈ Ioo D.lo D.hi)
    (z₀ p₀ : Fin (finrank ℝ S.covector.ker) → ℝ) (R : ℝ) :
    ((volume : Measure (Fin (finrank ℝ S.covector.ker) → ℝ)).prod ν)
      (D.normalizedTargetPhaseCell T cut z₀ p₀ R) < (⊤ : ℝ≥0∞) :=
  D.targetPhaseCell_congruence_intensity_lt_top hF hw hcut T
    (T.isUnit_nonsing_inv_det (Matrix.isUnit_det_of_invertible T))
    (D.measurable_normalizedTargetPhaseCenter hF hw T hcut z₀ p₀)
    (fun _ ha ↦ ha) R

/-- Normalized centers change no original cell intensity. -/
theorem normalizedTargetPhaseCell_intensity_eq_zeroCenter [SFinite ν]
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    (T : Matrix (Fin (finrank ℝ S.covector.ker)) (Fin (finrank ℝ S.covector.ker)) ℝ)
    [Invertible T] {cut : ℝ} (hcut : cut ∈ Ioo D.lo D.hi)
    (z₀ p₀ : Fin (finrank ℝ S.covector.ker) → ℝ) (R : ℝ) :
    ((volume : Measure (Fin (finrank ℝ S.covector.ker) → ℝ)).prod ν)
      (D.normalizedTargetPhaseCell T cut z₀ p₀ R) =
      ((volume : Measure (Fin (finrank ℝ S.covector.ker) → ℝ)).prod ν)
        (D.normalizedTargetPhaseCell T cut 0 0 R) := by
  unfold normalizedTargetPhaseCell
  rw [prod_volume_markedPhaseSourceCell
    (T.isUnit_nonsing_inv_det (Matrix.isUnit_det_of_invertible T))
    (D.measurable_normalizedTargetPhaseLeg hF hw T hcut)
    (D.normalizedTargetPhaseLeg_posSemidef hF hw T hcut)
    (D.measurable_normalizedTargetPhaseCenter hF hw T hcut z₀ p₀)
    (D.measurableSet_targetPhaseClocks cut) ν R,
    prod_volume_markedPhaseSourceCell
    (T.isUnit_nonsing_inv_det (Matrix.isUnit_det_of_invertible T))
    (D.measurable_normalizedTargetPhaseLeg hF hw T hcut)
    (D.normalizedTargetPhaseLeg_posSemidef hF hw T hcut)
    (D.measurable_normalizedTargetPhaseCenter hF hw T hcut 0 0)
    (D.measurableSet_targetPhaseClocks cut) ν R]

/-- The actual normalized path/momentum cell also controls its unchanged
original target, with the same phase radius and congruent target leg. -/
theorem original_normalized_pathPhase_target_mem
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    (T : Matrix (Fin (finrank ℝ S.covector.ker)) (Fin (finrank ℝ S.covector.ker)) ℝ)
    [Invertible T] {cut : ℝ} (hcut : cut ∈ Ioo D.lo D.hi)
    (x z₀ p₀ : Fin (finrank ℝ S.covector.ker) → ℝ)
    (m : PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker)))
    (ha : m.1.1 - S.level ∈ Ioo D.lo D.hi)
    (hb : m.1.2 ∈ D.targetPhaseClocks cut) (hab : m.1.1 < m.1.2)
    {R : ℝ} (hR : 0 ≤ R)
    (hz : ‖T *ᵥ originalSeedCompletePath S w x m (cut + S.level) - z₀‖ ≤ R)
    (hp : ‖(Tᵀ)⁻¹ *ᵥ originalSeedPairMomentum S w m - p₀‖ ≤ R) :
    (x + m.2, m.1.2) ∈ D.normalizedTargetPhaseCell T cut z₀ p₀ R := by
  have hpneg : ‖-((Tᵀ)⁻¹ *ᵥ originalSeedPairMomentum S w m - p₀)‖ ≤ R := by
    simpa only [norm_neg] using hp
  have hm := mk_add_mulVec_sub_mem_markedPhaseSourceCell
    (T.isUnit_nonsing_inv_det (Matrix.isUnit_det_of_invertible T))
    (D.normalizedTargetPhaseLeg_posSemidef hF hw T hcut)
    (D.normalizedTargetPhaseCenter T cut z₀ p₀) hb hR hz hpneg
  have hleft (v : Fin (finrank ℝ S.covector.ker) → ℝ) :
      T⁻¹ *ᵥ (T *ᵥ v) = v := by
    rw [Matrix.mulVec_mulVec, Matrix.inv_mul_of_invertible, Matrix.one_mulVec]
  have hcong (v : Fin (finrank ℝ S.covector.ker) → ℝ) :
      T⁻¹ *ᵥ ((T * D.targetPhaseLeg cut m.1.2 * Tᵀ) *ᵥ v) =
        D.targetPhaseLeg cut m.1.2 *ᵥ (Tᵀ *ᵥ v) := by
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hleft]
  have hb' : m.1.2 - S.level ∈ Ioo D.lo D.hi := ⟨hcut.1.trans hb.1, hb.2⟩
  have ht := D.originalSeedCompletePath_target_eq_cut_add_leg hF hw x m ha
    (by simpa only [add_sub_cancel_right] using hcut) hb' hab (c := cut + S.level)
  have hpath : originalSeedCompletePath S w x m (cut + S.level) +
      D.targetPhaseLeg cut m.1.2 *ᵥ originalSeedPairMomentum S w m = x + m.2 := by
    simpa only [targetPhaseLeg, indicator_of_mem hb, originalSeedClockCompliance,
      add_sub_cancel_right] using ht.symm
  have heq : D.normalizedTargetPhaseCenter T cut z₀ p₀ m.1.2 + T⁻¹ *ᵥ
      ((T *ᵥ originalSeedCompletePath S w x m (cut + S.level) - z₀) -
        (T * D.targetPhaseLeg cut m.1.2 * Tᵀ) *ᵥ
          (-((Tᵀ)⁻¹ *ᵥ originalSeedPairMomentum S w m - p₀))) = x + m.2 := by
    simp only [normalizedTargetPhaseCenter, Matrix.mulVec_sub, Matrix.mulVec_neg,
      sub_neg_eq_add, Matrix.mulVec_add, compliance_congruence_path_offset, hleft, hcong]
    rw [← hpath]
    abel
  rwa [heq] at hm

end OriginalSeedConditionalMoments
end OTSelector.Reconstruction
