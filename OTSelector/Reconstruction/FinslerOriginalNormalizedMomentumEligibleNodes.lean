import OTSelector.Reconstruction.FinslerOriginalMomentumEligibleNodes

/-! Actual complete-path nodes in a fixed anisotropic geometric phase frame. -/
open Set Function Filter MeasureTheory Matrix Module Manifold
open scoped ENNReal NNReal ContDiff Matrix.Norms.Operator Classical
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Geometry ContinuousFinslerNorm OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option linter.unusedSectionVars false

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {S : CalibratedLevelSeedPatch F u} {w : S.covector.ker} {μ ν : Measure ℝ}

/-- Actual complete-path position in the chosen internal geometric phase frame. -/
def normalizedMomentumNodePosition (S : CalibratedLevelSeedPatch F u)
    (w : S.covector.ker)
    (T : Matrix (Fin (finrank ℝ S.covector.ker)) (Fin (finrank ℝ S.covector.ker)) ℝ)
    (c : ℝ) (e : LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker)) :
    Fin (finrank ℝ S.covector.ker) → ℝ :=
  T *ᵥ originalMomentumNodePosition S w c e

/-- The covariantly transformed momentum of the same actual original edge. -/
def normalizedMomentumNodeValue (S : CalibratedLevelSeedPatch F u)
    (w : S.covector.ker)
    (T : Matrix (Fin (finrank ℝ S.covector.ker)) (Fin (finrank ℝ S.covector.ker)) ℝ)
    (e : LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker)) :
    Fin (finrank ℝ S.covector.ker) → ℝ :=
  (Tᵀ)⁻¹ *ᵥ originalMomentumNodeValue S w e

theorem measurable_normalizedMomentumNodePosition
    (S : CalibratedLevelSeedPatch F u) (hF : F.IsSmoothStronglyConvex)
    {w : S.covector.ker} (hw : w ∈ S.labels)
    (T : Matrix (Fin (finrank ℝ S.covector.ker)) (Fin (finrank ℝ S.covector.ker)) ℝ)
    (c : ℝ) : Measurable (normalizedMomentumNodePosition S w T c) :=
  (continuous_const.matrix_mulVec continuous_id).measurable.comp
    (measurable_originalMomentumNodePosition S hF hw c)

theorem measurable_normalizedMomentumNodeValue
    (S : CalibratedLevelSeedPatch F u) (hF : F.IsSmoothStronglyConvex)
    {w : S.covector.ker} (hw : w ∈ S.labels)
    (T : Matrix (Fin (finrank ℝ S.covector.ker)) (Fin (finrank ℝ S.covector.ker)) ℝ) :
    Measurable (normalizedMomentumNodeValue S w T) :=
  (continuous_const.matrix_mulVec continuous_id).measurable.comp
    (measurable_originalMomentumNodeValue S hF hw)

theorem normalizedMomentumNodePosition_reroot
    (S : CalibratedLevelSeedPatch F u) (w : S.covector.ker)
    (T : Matrix (Fin (finrank ℝ S.covector.ker)) (Fin (finrank ℝ S.covector.ker)) ℝ)
    (c : ℝ) (v : Fin (finrank ℝ S.covector.ker) → ℝ)
    (e : LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker)) :
    normalizedMomentumNodePosition S w T c (physicalSceneEdgeReroot v e) =
      normalizedMomentumNodePosition S w T c e - T *ᵥ v := by
  simp only [normalizedMomentumNodePosition, originalMomentumNodePosition_reroot, mulVec_sub]

theorem normalizedMomentumNodeValue_reroot
    (S : CalibratedLevelSeedPatch F u) (w : S.covector.ker)
    (T : Matrix (Fin (finrank ℝ S.covector.ker)) (Fin (finrank ℝ S.covector.ker)) ℝ)
    (v : Fin (finrank ℝ S.covector.ker) → ℝ)
    (e : LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker)) :
    normalizedMomentumNodeValue S w T (physicalSceneEdgeReroot v e) =
      normalizedMomentumNodeValue S w T e := by
  simp only [normalizedMomentumNodeValue, originalMomentumNodeValue_reroot]

namespace OriginalSeedConditionalMoments
variable (D : OriginalSeedConditionalMoments S w μ ν)

/-- Actual eligible common-cut edges. The clock level and two compliance-leg
thresholds are internal geometric levels, and retain the unchanged scalar supports. -/
def normalizedMomentumPhaseEligibleEdges
    (T : Matrix (Fin (finrank ℝ S.covector.ker)) (Fin (finrank ℝ S.covector.ker)) ℝ)
    (cut h : ℝ) :
    Set (LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker)) :=
  {e | e.1.2 ∈ D.sourcePhaseClocks cut ∧ e.2.2 ∈ D.targetPhaseClocks cut ∧
    e.1.2 ∈ μ.support ∧ e.2.2 ∈ ν.support ∧
    (T * D.sourcePhaseLeg cut e.1.2 * Tᵀ - h • 1).PosSemidef ∧
    (T * D.targetPhaseLeg cut e.2.2 * Tᵀ - h • 1).PosSemidef}

theorem measurableSet_normalizedMomentumPhaseEligibleEdges
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    (T : Matrix (Fin (finrank ℝ S.covector.ker)) (Fin (finrank ℝ S.covector.ker)) ℝ)
    {cut : ℝ} (hcut : cut ∈ Ioo D.lo D.hi) (h : ℝ) :
    MeasurableSet (D.normalizedMomentumPhaseEligibleEdges T cut h) := by
  apply ((D.measurableSet_sourcePhaseClocks cut).preimage measurable_fst.snd).inter
  apply ((D.measurableSet_targetPhaseClocks cut).preimage measurable_snd.snd).inter
  apply (μ.isClosed_support.measurableSet.preimage measurable_fst.snd).inter
  apply (ν.isClosed_support.measurableSet.preimage measurable_snd.snd).inter
  apply (Matrix.posSemidef_is_closed.measurableSet.preimage
    ((measurable_const.mul
      ((D.measurable_sourcePhaseLeg hF hw hcut).comp measurable_fst.snd)).mul
        measurable_const |>.sub_const (h • 1))).inter
  exact Matrix.posSemidef_is_closed.measurableSet.preimage
    ((measurable_const.mul
      ((D.measurable_targetPhaseLeg hF hw hcut).comp measurable_snd.snd)).mul
        measurable_const |>.sub_const (h • 1))

theorem normalizedMomentumPhaseEligibleEdges_reroot_iff
    (T : Matrix (Fin (finrank ℝ S.covector.ker)) (Fin (finrank ℝ S.covector.ker)) ℝ)
    (cut h : ℝ)
    (v : Fin (finrank ℝ S.covector.ker) → ℝ)
    (e : LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker)) :
    physicalSceneEdgeReroot v e ∈ D.normalizedMomentumPhaseEligibleEdges T cut h ↔
      e ∈ D.normalizedMomentumPhaseEligibleEdges T cut h := Iff.rfl

/-- The literal original occupied-edge measure on this actual common-cut geometric level. -/
def normalizedMomentumPhaseNodeMeasure
    (T : Matrix (Fin (finrank ℝ S.covector.ker)) (Fin (finrank ℝ S.covector.ker)) ℝ)
    (cut h : ℝ)
    (s : LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker)) :
    LocalFiniteMeasure (LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker)) :=
  originalCountingNodeRestriction (D.normalizedMomentumPhaseEligibleEdges T cut h) s.1.1

theorem measurable_normalizedMomentumPhaseNodeMeasure
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    (T : Matrix (Fin (finrank ℝ S.covector.ker)) (Fin (finrank ℝ S.covector.ker)) ℝ)
    {cut : ℝ} (hcut : cut ∈ Ioo D.lo D.hi) (h : ℝ) :
    Measurable (D.normalizedMomentumPhaseNodeMeasure T cut h) :=
  (measurable_originalCountingNodeRestriction
    (D.measurableSet_normalizedMomentumPhaseEligibleEdges hF hw T hcut h)).comp measurable_fst.fst

theorem normalizedMomentumPhaseNodeMeasure_reroot
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    (T : Matrix (Fin (finrank ℝ S.covector.ker)) (Fin (finrank ℝ S.covector.ker)) ℝ)
    {cut : ℝ} (hcut : cut ∈ Ioo D.lo D.hi) (h : ℝ)
    (v : Fin (finrank ℝ S.covector.ker) → ℝ)
    (s : LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker)) :
    D.normalizedMomentumPhaseNodeMeasure T cut h (legalMarkedInputSceneReroot _ v s) =
      localFiniteMapHomeomorph (physicalSceneEdgeReroot v)
        (D.normalizedMomentumPhaseNodeMeasure T cut h s) :=
  originalCountingNodeRestriction_mapHomeomorph _
    (D.measurableSet_normalizedMomentumPhaseEligibleEdges hF hw T hcut h) _
    (D.normalizedMomentumPhaseEligibleEdges_reroot_iff T cut h v) s.1.1

end OriginalSeedConditionalMoments
end OTSelector.Reconstruction
