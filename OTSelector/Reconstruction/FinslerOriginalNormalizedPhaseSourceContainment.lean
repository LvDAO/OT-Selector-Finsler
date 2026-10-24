import OTSelector.Reconstruction.FinslerOriginalAnisotropicPhaseCells
import OTSelector.Reconstruction.FinslerOriginalNormalizedMomentumEligibleNodes
import OTSelector.LinearAlgebra.Matrix.ComplianceCongruenceCovariance

/-! Deterministic original source cells for the exact normalized phase frame.
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

/-- The original physical source center pulled back from a normalized phase center. -/
def normalizedSourcePhaseCenter
    (T : Matrix (Fin (finrank ℝ S.covector.ker)) (Fin (finrank ℝ S.covector.ker)) ℝ)
    (cut : ℝ) (z₀ p₀ : Fin (finrank ℝ S.covector.ker) → ℝ) (a : ℝ) :=
  T⁻¹ *ᵥ z₀ - D.sourcePhaseLeg cut a *ᵥ (Tᵀ *ᵥ p₀)

/-- A deterministic original input cell uses the same normalized compliance and inverse frame. -/
def normalizedSourcePhaseCell
    (T : Matrix (Fin (finrank ℝ S.covector.ker)) (Fin (finrank ℝ S.covector.ker)) ℝ)
    (cut : ℝ) (z₀ p₀ : Fin (finrank ℝ S.covector.ker) → ℝ) (R : ℝ) :
    Set (LegalMarkedPhysicalPoint (finrank ℝ S.covector.ker)) :=
  markedPhaseSourceCell T⁻¹ (fun a ↦ T * D.sourcePhaseLeg cut a * Tᵀ)
    (D.normalizedSourcePhaseCenter T cut z₀ p₀) (D.sourcePhaseClocks cut) R

@[simp] theorem normalizedSourcePhaseCenter_zero
    (T : Matrix (Fin (finrank ℝ S.covector.ker)) (Fin (finrank ℝ S.covector.ker)) ℝ)
    (cut : ℝ) : D.normalizedSourcePhaseCenter T cut 0 0 = 0 := by
  funext a
  simp [normalizedSourcePhaseCenter]

theorem measurable_normalizedSourcePhaseCenter
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    (T : Matrix (Fin (finrank ℝ S.covector.ker)) (Fin (finrank ℝ S.covector.ker)) ℝ)
    {cut : ℝ} (hcut : cut ∈ Ioo D.lo D.hi)
    (z₀ p₀ : Fin (finrank ℝ S.covector.ker) → ℝ) :
    Measurable (D.normalizedSourcePhaseCenter T cut z₀ p₀) :=
  measurable_const.sub ((completePathMatrixApply (Tᵀ *ᵥ p₀)).continuous.measurable.comp
    (D.measurable_sourcePhaseLeg hF hw hcut))

theorem measurable_normalizedSourcePhaseLeg
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    (T : Matrix (Fin (finrank ℝ S.covector.ker)) (Fin (finrank ℝ S.covector.ker)) ℝ)
    {cut : ℝ} (hcut : cut ∈ Ioo D.lo D.hi) :
    Measurable (fun a ↦ T * D.sourcePhaseLeg cut a * Tᵀ) := by
  apply Measurable.of_eval_matrix
  intro i j
  simp only [Matrix.mul_apply]
  apply Finset.measurable_sum
  intro k _
  apply Measurable.mul _ measurable_const
  apply Finset.measurable_sum
  intro l _
  exact measurable_const.mul (D.measurable_sourcePhaseLeg hF hw hcut).eval.eval

theorem normalizedSourcePhaseLeg_posSemidef
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    (T : Matrix (Fin (finrank ℝ S.covector.ker)) (Fin (finrank ℝ S.covector.ker)) ℝ)
    {cut : ℝ} (hcut : cut ∈ Ioo D.lo D.hi) (a : ℝ) :
    (T * D.sourcePhaseLeg cut a * Tᵀ).PosSemidef := by
  simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
    (D.sourcePhaseLeg_posSemidef hF hw hcut a).mul_mul_conjTranspose_same T

theorem measurableSet_normalizedSourcePhaseCell
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    (T : Matrix (Fin (finrank ℝ S.covector.ker)) (Fin (finrank ℝ S.covector.ker)) ℝ)
    {cut : ℝ} (hcut : cut ∈ Ioo D.lo D.hi)
    (z₀ p₀ : Fin (finrank ℝ S.covector.ker) → ℝ) (R : ℝ) :
    MeasurableSet (D.normalizedSourcePhaseCell T cut z₀ p₀ R) :=
  measurableSet_markedPhaseSourceCell T⁻¹
    (D.measurable_normalizedSourcePhaseLeg hF hw T hcut)
    (D.measurable_normalizedSourcePhaseCenter hF hw T hcut z₀ p₀)
    (D.measurableSet_sourcePhaseClocks cut) R

theorem normalizedSourcePhaseCell_intensity_lt_top [SFinite μ]
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    (T : Matrix (Fin (finrank ℝ S.covector.ker)) (Fin (finrank ℝ S.covector.ker)) ℝ)
    [Invertible T] {cut : ℝ} (hcut : cut ∈ Ioo D.lo D.hi)
    (z₀ p₀ : Fin (finrank ℝ S.covector.ker) → ℝ) (R : ℝ) :
    ((volume : Measure (Fin (finrank ℝ S.covector.ker) → ℝ)).prod μ)
      (D.normalizedSourcePhaseCell T cut z₀ p₀ R) < (⊤ : ℝ≥0∞) :=
  D.sourcePhaseCell_congruence_intensity_lt_top hF hw hcut T
    (T.isUnit_nonsing_inv_det (Matrix.isUnit_det_of_invertible T))
    (D.measurable_normalizedSourcePhaseCenter hF hw T hcut z₀ p₀)
    (fun _ ha ↦ ha) R

/-- Normalized centers change no original cell intensity. -/
theorem normalizedSourcePhaseCell_intensity_eq_zeroCenter [SFinite μ]
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    (T : Matrix (Fin (finrank ℝ S.covector.ker)) (Fin (finrank ℝ S.covector.ker)) ℝ)
    [Invertible T] {cut : ℝ} (hcut : cut ∈ Ioo D.lo D.hi)
    (z₀ p₀ : Fin (finrank ℝ S.covector.ker) → ℝ) (R : ℝ) :
    ((volume : Measure (Fin (finrank ℝ S.covector.ker) → ℝ)).prod μ)
      (D.normalizedSourcePhaseCell T cut z₀ p₀ R) =
      ((volume : Measure (Fin (finrank ℝ S.covector.ker) → ℝ)).prod μ)
        (D.normalizedSourcePhaseCell T cut 0 0 R) := by
  unfold normalizedSourcePhaseCell
  rw [prod_volume_markedPhaseSourceCell
    (T.isUnit_nonsing_inv_det (Matrix.isUnit_det_of_invertible T))
    (D.measurable_normalizedSourcePhaseLeg hF hw T hcut)
    (D.normalizedSourcePhaseLeg_posSemidef hF hw T hcut)
    (D.measurable_normalizedSourcePhaseCenter hF hw T hcut z₀ p₀)
    (D.measurableSet_sourcePhaseClocks cut) μ R,
    prod_volume_markedPhaseSourceCell
    (T.isUnit_nonsing_inv_det (Matrix.isUnit_det_of_invertible T))
    (D.measurable_normalizedSourcePhaseLeg hF hw T hcut)
    (D.normalizedSourcePhaseLeg_posSemidef hF hw T hcut)
    (D.measurable_normalizedSourcePhaseCenter hF hw T hcut 0 0)
    (D.measurableSet_sourcePhaseClocks cut) μ R]

/-- An actual normalized path/momentum cell forces its unchanged source into
this deterministic original-input cell, at the identical radius. -/
theorem original_normalized_pathPhase_source_mem
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    (T : Matrix (Fin (finrank ℝ S.covector.ker)) (Fin (finrank ℝ S.covector.ker)) ℝ)
    [Invertible T] {cut : ℝ} (hcut : cut ∈ Ioo D.lo D.hi)
    (x z₀ p₀ : Fin (finrank ℝ S.covector.ker) → ℝ)
    (m : PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker)))
    (ha : m.1.1 ∈ D.sourcePhaseClocks cut) {R : ℝ} (hR : 0 ≤ R)
    (hz : ‖T *ᵥ originalSeedCompletePath S w x m (cut + S.level) - z₀‖ ≤ R)
    (hp : ‖(Tᵀ)⁻¹ *ᵥ originalSeedPairMomentum S w m - p₀‖ ≤ R) :
    (x, m.1.1) ∈ D.normalizedSourcePhaseCell T cut z₀ p₀ R := by
  have hm := mk_add_mulVec_sub_mem_markedPhaseSourceCell
    (T.isUnit_nonsing_inv_det (Matrix.isUnit_det_of_invertible T))
    (D.normalizedSourcePhaseLeg_posSemidef hF hw T hcut)
    (D.normalizedSourcePhaseCenter T cut z₀ p₀) ha hR hz hp
  have hleft (v : Fin (finrank ℝ S.covector.ker) → ℝ) :
      T⁻¹ *ᵥ (T *ᵥ v) = v := by
    rw [Matrix.mulVec_mulVec, Matrix.inv_mul_of_invertible, Matrix.one_mulVec]
  have hcong (v : Fin (finrank ℝ S.covector.ker) → ℝ) :
      T⁻¹ *ᵥ ((T * D.sourcePhaseLeg cut m.1.1 * Tᵀ) *ᵥ v) =
        D.sourcePhaseLeg cut m.1.1 *ᵥ (Tᵀ *ᵥ v) := by
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hleft]
  have hpath : originalSeedCompletePath S w x m (cut + S.level) =
      x + D.sourcePhaseLeg cut m.1.1 *ᵥ originalSeedPairMomentum S w m := by
    simp only [originalSeedCompletePath, sourcePhaseLeg, indicator_of_mem ha, add_sub_cancel_right]
  have heq : D.normalizedSourcePhaseCenter T cut z₀ p₀ m.1.1 + T⁻¹ *ᵥ
      ((T *ᵥ originalSeedCompletePath S w x m (cut + S.level) - z₀) -
        (T * D.sourcePhaseLeg cut m.1.1 * Tᵀ) *ᵥ
          ((Tᵀ)⁻¹ *ᵥ originalSeedPairMomentum S w m - p₀)) = x := by
    simp only [normalizedSourcePhaseCenter, Matrix.mulVec_sub,
      compliance_congruence_path_offset, hleft, hcong, hpath]
    abel
  rwa [heq] at hm

end OriginalSeedConditionalMoments
end OTSelector.Reconstruction
