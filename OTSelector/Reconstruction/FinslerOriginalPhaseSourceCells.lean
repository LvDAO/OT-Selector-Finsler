import OTSelector.Reconstruction.MarkedPhaseSourceCellVolume
import OTSelector.Reconstruction.FinslerOriginalPhaseLegEnvelope

/-!
# Finite-intensity phase source sets from the original Finsler geometry

The compliance extensions below are Borel, positive, and agree with the actual
left source and right target legs on their original active clocks. Their phase
source sets have finite unchanged physical intensity by the proved original
focal determinant moments.
-/
open Set Function MeasureTheory Module Manifold Matrix
open scoped ContDiff Topology Matrix.Norms.Operator Classical ENNReal
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Geometry ContinuousFinslerNorm
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {S : CalibratedLevelSeedPatch F u} {w : S.covector.ker} {μ ν : Measure ℝ}
namespace OriginalSeedConditionalMoments
variable (D : OriginalSeedConditionalMoments S w μ ν)

/-- Original source clocks on the left of a fixed actual relative cut. -/
def sourcePhaseClocks (cut : ℝ) : Set ℝ := {a | a - (S.level : ℝ) ∈ Ioo D.lo cut}

/-- Original target clocks on the right of the same actual relative cut. -/
def targetPhaseClocks (cut : ℝ) : Set ℝ := {b | b - (S.level : ℝ) ∈ Ioo cut D.hi}

/-- A Borel extension of the actual source compliance leg; it is zero outside active clocks. -/
def sourcePhaseLeg (cut a : ℝ) := (D.sourcePhaseClocks cut).indicator
  (fun a ↦ ∫ t in (a - S.level)..cut, originalSeedKernel S w t) a

/-- A Borel extension of the actual target compliance leg. -/
def targetPhaseLeg (cut b : ℝ) := (D.targetPhaseClocks cut).indicator
  (fun b ↦ ∫ t in cut..(b - S.level), originalSeedKernel S w t) b

omit [BorelSpace E] in
theorem measurableSet_sourcePhaseClocks (cut : ℝ) : MeasurableSet (D.sourcePhaseClocks cut) :=
  measurableSet_Ioo.preimage (measurable_id.sub_const _)

omit [BorelSpace E] in
theorem measurableSet_targetPhaseClocks (cut : ℝ) : MeasurableSet (D.targetPhaseClocks cut) :=
  measurableSet_Ioo.preimage (measurable_id.sub_const _)

omit [BorelSpace E] in
/-- The actual source leg extension is globally Borel, including focal endpoint singularities. -/
theorem measurable_sourcePhaseLeg (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {cut : ℝ} (hcut : cut ∈ Ioo D.lo D.hi) : Measurable (D.sourcePhaseLeg cut) := by
  have hprim := continuousOn_compliancePrimitive (D.original_kernel_regular hF hw).1 hcut
  have hc : ContinuousOn (fun a ↦ ∫ t in cut..(a - S.level), originalSeedKernel S w t)
      (D.sourcePhaseClocks cut) := by
    exact hprim.comp ((continuous_id.sub continuous_const).continuousOn)
      (fun a ha ↦ ⟨ha.1, ha.2.trans hcut.2⟩)
  have heq : (fun a ↦ ∫ t in (a - S.level)..cut, originalSeedKernel S w t) =
      (fun a ↦ -(∫ t in cut..(a - S.level), originalSeedKernel S w t)) := by
    funext a
    exact intervalIntegral.integral_symm _ _
  have hc' : ContinuousOn (fun a ↦ ∫ t in (a - S.level)..cut, originalSeedKernel S w t)
      (D.sourcePhaseClocks cut) := heq ▸ hc.neg
  exact hc'.measurable_piecewise continuousOn_const (D.measurableSet_sourcePhaseClocks cut)

omit [BorelSpace E] in
/-- The actual target leg extension is globally Borel. -/
theorem measurable_targetPhaseLeg (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {cut : ℝ} (hcut : cut ∈ Ioo D.lo D.hi) : Measurable (D.targetPhaseLeg cut) := by
  have hprim := continuousOn_compliancePrimitive (D.original_kernel_regular hF hw).1 hcut
  have hc : ContinuousOn (fun b ↦ ∫ t in cut..(b - S.level), originalSeedKernel S w t)
      (D.targetPhaseClocks cut) := by
    exact hprim.comp ((continuous_id.sub continuous_const).continuousOn)
      (fun b hb ↦ ⟨hcut.1.trans hb.1, hb.2⟩)
  exact hc.measurable_piecewise continuousOn_const (D.measurableSet_targetPhaseClocks cut)

omit [BorelSpace E] in
/-- Both actual extensions are positive semidefinite at every original clock. -/
theorem sourcePhaseLeg_posSemidef (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {cut : ℝ} (hcut : cut ∈ Ioo D.lo D.hi) (a : ℝ) :
    (D.sourcePhaseLeg cut a).PosSemidef := by
  by_cases ha : a ∈ D.sourcePhaseClocks cut
  · rw [sourcePhaseLeg, indicator_of_mem ha]
    apply posSemidef_intervalIntegral ha.2.le
    intro t ht
    exact ((D.original_kernel_regular hF hw).2 t ⟨ha.1.trans_le ht.1, ht.2.trans_lt hcut.2⟩).posSemidef
  · simp only [sourcePhaseLeg, indicator_of_notMem ha]
    exact Matrix.PosSemidef.zero

omit [BorelSpace E] in
theorem targetPhaseLeg_posSemidef (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {cut : ℝ} (hcut : cut ∈ Ioo D.lo D.hi) (b : ℝ) :
    (D.targetPhaseLeg cut b).PosSemidef := by
  by_cases hb : b ∈ D.targetPhaseClocks cut
  · rw [targetPhaseLeg, indicator_of_mem hb]
    apply posSemidef_intervalIntegral hb.1.le
    intro t ht
    exact ((D.original_kernel_regular hF hw).2 t ⟨hcut.1.trans_le ht.1, ht.2.trans_lt hb.2⟩).posSemidef
  · simp only [targetPhaseLeg, indicator_of_notMem hb]
    exact Matrix.PosSemidef.zero

omit [BorelSpace E] in
/-- The source extension retains the proved original focal determinant moment. -/
theorem integrable_sourcePhaseLeg_determinant
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {cut : ℝ} (hcut : cut ∈ Ioo D.lo D.hi) :
    Integrable ((D.sourcePhaseClocks cut).indicator (fun a ↦ (1 + D.sourcePhaseLeg cut a).det)) μ := by
  apply (D.integrable_original_source_phaseLeg_determinant hF hw hcut).congr
  filter_upwards [D.support.source.ae_open] with a ha
  by_cases hact : a - (S.level : ℝ) < cut
  · have hmem : a ∈ D.sourcePhaseClocks cut := ⟨ha.1, hact⟩
    simp [sourcePhaseLeg, hmem, hact]
  · have hmem : a ∉ D.sourcePhaseClocks cut := fun h ↦ hact h.2
    simp [sourcePhaseLeg, hmem, hact]

omit [BorelSpace E] in
theorem integrable_targetPhaseLeg_determinant
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {cut : ℝ} (hcut : cut ∈ Ioo D.lo D.hi) :
    Integrable ((D.targetPhaseClocks cut).indicator (fun b ↦ (1 + D.targetPhaseLeg cut b).det)) ν := by
  apply (D.integrable_original_target_phaseLeg_determinant hF hw hcut).congr
  filter_upwards [D.support.target.ae_open] with b hb
  by_cases hact : cut < b - (S.level : ℝ)
  · have hmem : b ∈ D.targetPhaseClocks cut := ⟨hact, hb.2⟩
    simp [targetPhaseLeg, hmem, hact]
  · have hmem : b ∉ D.targetPhaseClocks cut := fun h ↦ hact h.1
    simp [targetPhaseLeg, hmem, hact]

omit [BorelSpace E] in
/-- Every original source phase cell has finite true intensity; no spatial boundedness is needed. -/
theorem sourcePhaseCell_intensity_lt_top [SFinite μ]
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {cut : ℝ} (hcut : cut ∈ Ioo D.lo D.hi)
    {L : Matrix (Fin (finrank ℝ S.covector.ker)) (Fin (finrank ℝ S.covector.ker)) ℝ}
    (hL : IsUnit L.det) {c : ℝ → (Fin (finrank ℝ S.covector.ker) → ℝ)}
    (hc : Measurable c) (R : ℝ) :
    ((volume : Measure (Fin (finrank ℝ S.covector.ker) → ℝ)).prod μ)
      (markedPhaseSourceCell L (D.sourcePhaseLeg cut) c (D.sourcePhaseClocks cut) R) < (∞ : ℝ≥0∞) :=
  prod_volume_markedPhaseSourceCell_lt_top hL (D.measurable_sourcePhaseLeg hF hw hcut)
    (D.sourcePhaseLeg_posSemidef hF hw hcut) hc (D.measurableSet_sourcePhaseClocks cut) μ R
    (D.integrable_sourcePhaseLeg_determinant hF hw hcut)

omit [BorelSpace E] in
/-- The same finite original intensity holds for target phase cells. -/
theorem targetPhaseCell_intensity_lt_top [SFinite ν]
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {cut : ℝ} (hcut : cut ∈ Ioo D.lo D.hi)
    {L : Matrix (Fin (finrank ℝ S.covector.ker)) (Fin (finrank ℝ S.covector.ker)) ℝ}
    (hL : IsUnit L.det) {c : ℝ → (Fin (finrank ℝ S.covector.ker) → ℝ)}
    (hc : Measurable c) (R : ℝ) :
    ((volume : Measure (Fin (finrank ℝ S.covector.ker) → ℝ)).prod ν)
      (markedPhaseSourceCell L (D.targetPhaseLeg cut) c (D.targetPhaseClocks cut) R) < (∞ : ℝ≥0∞) :=
  prod_volume_markedPhaseSourceCell_lt_top hL (D.measurable_targetPhaseLeg hF hw hcut)
    (D.targetPhaseLeg_posSemidef hF hw hcut) hc (D.measurableSet_targetPhaseClocks cut) ν R
    (D.integrable_targetPhaseLeg_determinant hF hw hcut)

end OriginalSeedConditionalMoments
end OTSelector.Reconstruction
