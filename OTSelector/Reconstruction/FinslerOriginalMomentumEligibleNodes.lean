import OTSelector.Reconstruction.OriginalCountingRestrictedNodes
import OTSelector.Reconstruction.FinslerOriginalPhaseSourceCells
import OTSelector.Reconstruction.FinslerOriginalPathMeasurability
import OTSelector.Reconstruction.MarkedStationaryValueLegalInputJointStationarity
import Mathlib.Analysis.Matrix.Order

/-! Actual complete-path momentum nodes at one geometric common-cut level. -/
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

/-- Literal physical complete-path position of an original edge at a fixed clock. -/
def originalMomentumNodePosition (S : CalibratedLevelSeedPatch F u)
    (w : S.covector.ker) (c : ℝ)
    (e : LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker)) :
    Fin (finrank ℝ S.covector.ker) → ℝ :=
  originalSeedCompletePath S w e.1.1 (physicalPairAnchor e).2 c

/-- Literal original inverse-compliance momentum of that same complete edge. -/
def originalMomentumNodeValue (S : CalibratedLevelSeedPatch F u)
    (w : S.covector.ker)
    (e : LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker)) :
    Fin (finrank ℝ S.covector.ker) → ℝ :=
  originalSeedPairMomentum S w (physicalPairAnchor e).2

theorem measurable_originalMomentumNodePosition
    (S : CalibratedLevelSeedPatch F u) (hF : F.IsSmoothStronglyConvex)
    {w : S.covector.ker} (hw : w ∈ S.labels) (c : ℝ) :
    Measurable (originalMomentumNodePosition S w c) :=
  (measurable_originalSeedCompletePath S hF hw).comp
    ((measurable_fst.fst.prodMk measurable_physicalPairAnchor.snd).prodMk measurable_const)

theorem measurable_originalMomentumNodeValue
    (S : CalibratedLevelSeedPatch F u) (hF : F.IsSmoothStronglyConvex)
    {w : S.covector.ker} (hw : w ∈ S.labels) : Measurable (originalMomentumNodeValue S w) :=
  (measurable_originalSeedPairMomentum S hF hw).comp measurable_physicalPairAnchor.snd

theorem physicalPairAnchor_mark_reroot
    (v : Fin (finrank ℝ S.covector.ker) → ℝ)
    (e : LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker)) :
    (physicalPairAnchor (physicalSceneEdgeReroot v e)).2 = (physicalPairAnchor e).2 := by
  change ((e.1.2, e.2.2), (e.2.1 - v) - (e.1.1 - v)) = _
  rw [sub_sub_sub_cancel_right]
  rfl

theorem originalMomentumNodePosition_reroot
    (S : CalibratedLevelSeedPatch F u) (w : S.covector.ker) (c : ℝ)
    (v : Fin (finrank ℝ S.covector.ker) → ℝ)
    (e : LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker)) :
    originalMomentumNodePosition S w c (physicalSceneEdgeReroot v e) =
      originalMomentumNodePosition S w c e - v := by
  rw [originalMomentumNodePosition, physicalPairAnchor_mark_reroot]
  rw [originalSeedCompletePath_eq_anchor_add_offset,
    originalMomentumNodePosition, originalSeedCompletePath_eq_anchor_add_offset]
  change (e.1.1 - v) + _ = (e.1.1 + _) - v
  abel

theorem originalMomentumNodeValue_reroot
    (S : CalibratedLevelSeedPatch F u) (w : S.covector.ker)
    (v : Fin (finrank ℝ S.covector.ker) → ℝ)
    (e : LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker)) :
    originalMomentumNodeValue S w (physicalSceneEdgeReroot v e) =
      originalMomentumNodeValue S w e := by
  simp only [originalMomentumNodeValue, physicalPairAnchor_mark_reroot]

namespace OriginalSeedConditionalMoments
variable (D : OriginalSeedConditionalMoments S w μ ν)

/-- Actual eligible common-cut edges. The clock level and two compliance-leg
thresholds are internal geometric levels, and retain the unchanged scalar supports. -/
def momentumPhaseEligibleEdges (cut h : ℝ) :
    Set (LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker)) :=
  {e | e.1.2 ∈ D.sourcePhaseClocks cut ∧ e.2.2 ∈ D.targetPhaseClocks cut ∧
    e.1.2 ∈ μ.support ∧ e.2.2 ∈ ν.support ∧
    (D.sourcePhaseLeg cut e.1.2 - h • 1).PosSemidef ∧
    (D.targetPhaseLeg cut e.2.2 - h • 1).PosSemidef}

theorem measurableSet_momentumPhaseEligibleEdges
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {cut : ℝ} (hcut : cut ∈ Ioo D.lo D.hi) (h : ℝ) :
    MeasurableSet (D.momentumPhaseEligibleEdges cut h) := by
  apply ((D.measurableSet_sourcePhaseClocks cut).preimage measurable_fst.snd).inter
  apply ((D.measurableSet_targetPhaseClocks cut).preimage measurable_snd.snd).inter
  apply (μ.isClosed_support.measurableSet.preimage measurable_fst.snd).inter
  apply (ν.isClosed_support.measurableSet.preimage measurable_snd.snd).inter
  apply (Matrix.posSemidef_is_closed.measurableSet.preimage
    (((D.measurable_sourcePhaseLeg hF hw hcut).comp measurable_fst.snd).sub_const (h • 1))).inter
  exact Matrix.posSemidef_is_closed.measurableSet.preimage
    (((D.measurable_targetPhaseLeg hF hw hcut).comp measurable_snd.snd).sub_const (h • 1))

theorem momentumPhaseEligibleEdges_reroot_iff (cut h : ℝ)
    (v : Fin (finrank ℝ S.covector.ker) → ℝ)
    (e : LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker)) :
    physicalSceneEdgeReroot v e ∈ D.momentumPhaseEligibleEdges cut h ↔
      e ∈ D.momentumPhaseEligibleEdges cut h := Iff.rfl

/-- The literal original occupied-edge measure on this actual common-cut geometric level. -/
def momentumPhaseNodeMeasure (cut h : ℝ)
    (s : LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker)) :
    LocalFiniteMeasure (LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker)) :=
  originalCountingNodeRestriction (D.momentumPhaseEligibleEdges cut h) s.1.1

theorem measurable_momentumPhaseNodeMeasure
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {cut : ℝ} (hcut : cut ∈ Ioo D.lo D.hi) (h : ℝ) :
    Measurable (D.momentumPhaseNodeMeasure cut h) :=
  (measurable_originalCountingNodeRestriction
    (D.measurableSet_momentumPhaseEligibleEdges hF hw hcut h)).comp measurable_fst.fst

theorem momentumPhaseNodeMeasure_reroot
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {cut : ℝ} (hcut : cut ∈ Ioo D.lo D.hi) (h : ℝ)
    (v : Fin (finrank ℝ S.covector.ker) → ℝ)
    (s : LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker)) :
    D.momentumPhaseNodeMeasure cut h (legalMarkedInputSceneReroot _ v s) =
      localFiniteMapHomeomorph (physicalSceneEdgeReroot v) (D.momentumPhaseNodeMeasure cut h s) :=
  originalCountingNodeRestriction_mapHomeomorph _
    (D.measurableSet_momentumPhaseEligibleEdges hF hw hcut h) _
    (D.momentumPhaseEligibleEdges_reroot_iff cut h v) s.1.1

end OriginalSeedConditionalMoments
end OTSelector.Reconstruction
