import OTSelector.Reconstruction.FinslerOriginalPhaseSourceCells
import OTSelector.Reconstruction.FinslerOriginalCommonCutCompliance

/-!
# Actual path phase cells are contained in deterministic original-input envelopes

A bounded actual path position and bounded actual momentum deviation give an
original source or target point in the fixed marked envelope. Its center depends
only on the deterministic phase-cell center and the original compliance leg.
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

/-- A deterministic phase-cell center pulls back through the actual source leg. -/
def sourcePhaseCenter (cut : ℝ)
    (z₀ p₀ : Fin (finrank ℝ S.covector.ker) → ℝ) (a : ℝ) :=
  z₀ - D.sourcePhaseLeg cut a *ᵥ p₀

/-- The same phase-cell center pulls forward through the actual target leg. -/
def targetPhaseCenter (cut : ℝ)
    (z₀ p₀ : Fin (finrank ℝ S.covector.ker) → ℝ) (b : ℝ) :=
  z₀ + D.targetPhaseLeg cut b *ᵥ p₀

omit [BorelSpace E] in
theorem measurable_sourcePhaseCenter (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {cut : ℝ} (hcut : cut ∈ Ioo D.lo D.hi)
    (z₀ p₀ : Fin (finrank ℝ S.covector.ker) → ℝ) :
    Measurable (D.sourcePhaseCenter cut z₀ p₀) :=
  measurable_const.sub ((completePathMatrixApply p₀).continuous.measurable.comp
    (D.measurable_sourcePhaseLeg hF hw hcut))

omit [BorelSpace E] in
theorem measurable_targetPhaseCenter (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {cut : ℝ} (hcut : cut ∈ Ioo D.lo D.hi)
    (z₀ p₀ : Fin (finrank ℝ S.covector.ker) → ℝ) :
    Measurable (D.targetPhaseCenter cut z₀ p₀) :=
  measurable_const.add ((completePathMatrixApply p₀).continuous.measurable.comp
    (D.measurable_targetPhaseLeg hF hw hcut))

omit [BorelSpace E] in
/-- Actual source points of a bounded original path phase cell lie in its deterministic envelope. -/
theorem original_pathPhase_source_mem
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {cut : ℝ} (hcut : cut ∈ Ioo D.lo D.hi)
    (x z₀ p₀ : Fin (finrank ℝ S.covector.ker) → ℝ)
    (m : PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker)))
    (ha : m.1.1 ∈ D.sourcePhaseClocks cut) {R : ℝ} (hR : 0 ≤ R)
    (hz : ‖originalSeedCompletePath S w x m (cut + S.level) - z₀‖ ≤ R)
    (hp : ‖originalSeedPairMomentum S w m - p₀‖ ≤ R) :
    (x, m.1.1) ∈ markedPhaseSourceCell 1 (D.sourcePhaseLeg cut)
      (D.sourcePhaseCenter cut z₀ p₀) (D.sourcePhaseClocks cut) R := by
  have h := mk_add_mulVec_sub_mem_markedPhaseSourceCell
    (L := (1 : Matrix (Fin (finrank ℝ S.covector.ker)) _ ℝ))
    (by simp) (D.sourcePhaseLeg_posSemidef hF hw hcut)
    (D.sourcePhaseCenter cut z₀ p₀) ha hR hz hp
  have heq : D.sourcePhaseCenter cut z₀ p₀ m.1.1 +
      (1 : Matrix (Fin (finrank ℝ S.covector.ker)) _ ℝ) *ᵥ
        ((originalSeedCompletePath S w x m (cut + S.level) - z₀) -
          D.sourcePhaseLeg cut m.1.1 *ᵥ (originalSeedPairMomentum S w m - p₀)) = x := by
    simp only [Matrix.one_mulVec, sourcePhaseCenter, originalSeedCompletePath,
      sourcePhaseLeg, indicator_of_mem ha, add_sub_cancel_right, Matrix.mulVec_sub]
    abel_nf
  rwa [heq] at h

/-- The unchanged actual target belongs to the analogous deterministic original target envelope. -/
theorem original_pathPhase_target_mem
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {cut : ℝ} (hcut : cut ∈ Ioo D.lo D.hi)
    (x z₀ p₀ : Fin (finrank ℝ S.covector.ker) → ℝ)
    (m : PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker)))
    (ha : m.1.1 - (S.level : ℝ) ∈ Ioo D.lo D.hi)
    (hb : m.1.2 ∈ D.targetPhaseClocks cut) (hab : m.1.1 < m.1.2)
    {R : ℝ} (hR : 0 ≤ R)
    (hz : ‖originalSeedCompletePath S w x m (cut + S.level) - z₀‖ ≤ R)
    (hp : ‖originalSeedPairMomentum S w m - p₀‖ ≤ R) :
    (x + m.2, m.1.2) ∈ markedPhaseSourceCell 1 (D.targetPhaseLeg cut)
      (D.targetPhaseCenter cut z₀ p₀) (D.targetPhaseClocks cut) R := by
  have hneg : ‖-(originalSeedPairMomentum S w m - p₀)‖ ≤ R := by simpa only [norm_neg] using hp
  have h := mk_add_mulVec_sub_mem_markedPhaseSourceCell
    (L := (1 : Matrix (Fin (finrank ℝ S.covector.ker)) _ ℝ))
    (by simp) (D.targetPhaseLeg_posSemidef hF hw hcut)
    (D.targetPhaseCenter cut z₀ p₀) hb hR hz hneg
  have hb' : m.1.2 - (S.level : ℝ) ∈ Ioo D.lo D.hi :=
    ⟨hcut.1.trans hb.1, hb.2⟩
  have htarget := D.originalSeedCompletePath_target_eq_cut_add_leg hF hw x m ha
    (by simpa using hcut) hb' hab (c := cut + S.level)
  have heq : D.targetPhaseCenter cut z₀ p₀ m.1.2 +
      (1 : Matrix (Fin (finrank ℝ S.covector.ker)) _ ℝ) *ᵥ
        ((originalSeedCompletePath S w x m (cut + S.level) - z₀) -
          D.targetPhaseLeg cut m.1.2 *ᵥ (-(originalSeedPairMomentum S w m - p₀))) = x + m.2 := by
    rw [htarget]
    simp only [Matrix.one_mulVec, targetPhaseCenter, targetPhaseLeg, indicator_of_mem hb,
      originalSeedClockCompliance, add_sub_cancel_right, Matrix.mulVec_neg, Matrix.mulVec_sub]
    abel_nf
  rwa [heq] at h

end OriginalSeedConditionalMoments
end OTSelector.Reconstruction
