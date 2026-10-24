import OTSelector.Reconstruction.OriginalCubeTraceCompactnessMarkedPositionMeasure
import OTSelector.Reconstruction.OriginalCubeTraceCompactnessClockSlabFTC
import OTSelector.Reconstruction.OriginalClockCutDecomposition

/-! Actual positive source, target and cut measures for the original infinite-scene slab. -/
open Set Function Filter MeasureTheory Module Manifold
open scoped ENNReal Topology ContDiff
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OTSelector.Reconstruction
open OTSelector.Geometry ContinuousFinslerNorm OTSelector.Probability

/-- Original source positions whose unchanged source clock starts in this slab. -/
def originalSceneSlabSourceMeasure {q : ℕ} (s t : ℝ)
    (scene : LegalMarkedOptimalInputScene q) : Measure (Fin q → ℝ) :=
  originalSceneMarkedPositionMeasure (fun _ ↦ 0) {m | s ≤ m.1.1 ∧ m.1.1 < t} scene

/-- Original target positions whose unchanged target clock finishes in this slab. -/
def originalSceneSlabTargetMeasure {q : ℕ} (s t : ℝ)
    (scene : LegalMarkedOptimalInputScene q) : Measure (Fin q → ℝ) :=
  originalSceneMarkedPositionMeasure (fun m ↦ m.2) {m | s < m.1.2 ∧ m.1.2 ≤ t} scene

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}

/-- Actual original positions at the physical clock cut, from precisely the original
pairs whose unchanged clock endpoints strictly straddle that cut. -/
def originalSceneActiveCutMeasure (S : CalibratedLevelSeedPatch F u) (w : S.covector.ker)
    (c : ℝ) (scene : LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker)) :
    Measure (Fin (finrank ℝ S.covector.ker) → ℝ) :=
  originalSceneMarkedPositionMeasure (originalSeedPathOffset S w c)
    {m | m.1.1 < c ∧ c < m.1.2} scene

private theorem measurableSet_sourceSlabMarks {q : ℕ} (s t : ℝ) :
    MeasurableSet {m : PhysicalPairPalmMark (Fin q) | s ≤ m.1.1 ∧ m.1.1 < t} :=
  (measurableSet_le measurable_const measurable_fst.fst).inter
    (measurableSet_lt measurable_fst.fst measurable_const)

private theorem measurableSet_targetSlabMarks {q : ℕ} (s t : ℝ) :
    MeasurableSet {m : PhysicalPairPalmMark (Fin q) | s < m.1.2 ∧ m.1.2 ≤ t} :=
  (measurableSet_lt measurable_const measurable_fst.snd).inter
    (measurableSet_le measurable_fst.snd measurable_const)

private theorem measurableSet_activeCutMarks {q : ℕ} (c : ℝ) :
    MeasurableSet {m : PhysicalPairPalmMark (Fin q) | m.1.1 < c ∧ c < m.1.2} :=
  (measurableSet_lt measurable_fst.fst measurable_const).inter
    (measurableSet_lt measurable_const measurable_fst.snd)

/-- Every actual original source, target and active-cut measure is locally finite on one
full-measure scene set for these fixed cuts, directly from original marked Campbell counts. -/
theorem ae_originalSceneSlabCharges_finiteOnCompacts
    (S : CalibratedLevelSeedPatch F u) (hF : F.IsSmoothStronglyConvex)
    {w : S.covector.ker} (hw : w ∈ S.labels)
    {μ ν : Measure ℝ} {kin : ℝ → ℝ → (Fin (finrank ℝ S.covector.ker) → ℝ) → ℝ}
    {g : ℝ → ℝ → ℝ}
    (Q : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν kin g)
    (s t : ℝ) :
    ∀ᵐ scene ∂(Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))),
      IsFiniteMeasureOnCompacts (originalSceneSlabSourceMeasure s t scene) ∧
      IsFiniteMeasureOnCompacts (originalSceneSlabTargetMeasure s t scene) ∧
      IsFiniteMeasureOnCompacts (originalSceneActiveCutMeasure S w s scene) ∧
      IsFiniteMeasureOnCompacts (originalSceneActiveCutMeasure S w t scene) := by
  filter_upwards [
    Q.ae_originalSceneMarkedPositionMeasure_finiteOnCompacts
      (d := fun _ ↦ 0) measurable_const (measurableSet_sourceSlabMarks s t),
    Q.ae_originalSceneMarkedPositionMeasure_finiteOnCompacts
      (d := fun m ↦ m.2) measurable_snd (measurableSet_targetSlabMarks s t),
    Q.ae_originalSceneMarkedPositionMeasure_finiteOnCompacts
      (measurable_originalSeedPathOffset S hF hw s) (measurableSet_activeCutMarks s),
    Q.ae_originalSceneMarkedPositionMeasure_finiteOnCompacts
      (measurable_originalSeedPathOffset S hF hw t) (measurableSet_activeCutMarks t)]
    with scene hsrc htgt hs ht
  exact ⟨hsrc, htgt, hs, ht⟩

namespace OriginalSeedConditionalMoments
variable {S : CalibratedLevelSeedPatch F u} {w : S.covector.ker} {μ ν : Measure ℝ}
  (D : OriginalSeedConditionalMoments S w μ ν)
include D

/-- The actual infinite-scene weak slab has the exact four positive source, target and
incoming/outgoing-cut measures. Every compact C¹ test is genuinely integrable in each term;
no finite-edge representation or signed residual identity is assumed. -/
theorem ae_all_originalWeakSlab_positiveCharge_balance
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {kin : ℝ → ℝ → (Fin (finrank ℝ S.covector.ker) → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (Q : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν kin g)
    {s t : ℝ} (hst : s ≤ t) :
    ∀ᵐ scene ∂(Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))),
      ∀ φ : (Fin (finrank ℝ S.covector.ker) → ℝ) → ℝ,
        ContDiff ℝ 1 φ → HasCompactSupport φ →
        -originalSeedPathWeakSlabReadout S w φ s t scene =
          (∫ x, φ x ∂originalSceneSlabSourceMeasure s t scene) -
          (∫ x, φ x ∂originalSceneSlabTargetMeasure s t scene) +
          (∫ x, φ x ∂originalSceneActiveCutMeasure S w s scene) -
          (∫ x, φ x ∂originalSceneActiveCutMeasure S w t scene) := by
  filter_upwards [ae_originalSceneSlabCharges_finiteOnCompacts S hF hw Q s t,
    D.ae_ae_original_pairKernel_interior_forward Q,
    D.ae_all_originalClockSlab_testDerivative_eq_weakSlab Q,
    D.ae_all_originalClockSlab_testDerivative_eq_endpoints hF hw Q]
    with scene hfinite hlegal hweak hFTC
  intro φ hφ hcφ
  have : IsFiniteMeasureOnCompacts (originalSceneSlabSourceMeasure s t scene) := hfinite.1
  have : IsFiniteMeasureOnCompacts (originalSceneSlabTargetMeasure s t scene) := hfinite.2.1
  have : IsFiniteMeasureOnCompacts (originalSceneActiveCutMeasure S w s scene) := hfinite.2.2.1
  have : IsFiniteMeasureOnCompacts (originalSceneActiveCutMeasure S w t scene) := hfinite.2.2.2
  have hsrc : Integrable φ (originalSceneSlabSourceMeasure s t scene) :=
    hφ.continuous.integrable_of_hasCompactSupport hcφ
  have htgt : Integrable φ (originalSceneSlabTargetMeasure s t scene) :=
    hφ.continuous.integrable_of_hasCompactSupport hcφ
  have hcuts : Integrable φ (originalSceneActiveCutMeasure S w s scene) :=
    hφ.continuous.integrable_of_hasCompactSupport hcφ
  have hcutt : Integrable φ (originalSceneActiveCutMeasure S w t scene) :=
    hφ.continuous.integrable_of_hasCompactSupport hcφ
  let src := fun a : (Fin (finrank ℝ S.covector.ker) → ℝ) ×
      PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker)) ↦
    if s ≤ a.2.1.1 ∧ a.2.1.1 < t then φ a.1 else 0
  let tgt := fun a : (Fin (finrank ℝ S.covector.ker) → ℝ) ×
      PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker)) ↦
    if s < a.2.1.2 ∧ a.2.1.2 ≤ t then φ (a.1 + a.2.2) else 0
  let cut := fun c (a : (Fin (finrank ℝ S.covector.ker) → ℝ) ×
      PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker))) ↦
    if a.2.1.1 < c ∧ c < a.2.1.2 then φ (a.1 + originalSeedPathOffset S w c a.2) else 0
  have isrc : Integrable src (physicalScenePairKernel scene.1) := by
    simpa only [src, Set.indicator_apply, mem_ofPred_eq, add_zero] using
      integrable_originalSceneMarkedPositionReadout_of_integrable measurable_const
        (measurableSet_sourceSlabMarks s t) scene hsrc
  have itgt : Integrable tgt (physicalScenePairKernel scene.1) := by
    simpa only [tgt, Set.indicator_apply, mem_ofPred_eq] using
      integrable_originalSceneMarkedPositionReadout_of_integrable measurable_snd
        (measurableSet_targetSlabMarks s t) scene htgt
  have icuts : Integrable (cut s) (physicalScenePairKernel scene.1) := by
    simpa only [cut, Set.indicator_apply, mem_ofPred_eq] using
      integrable_originalSceneMarkedPositionReadout_of_integrable
        (measurable_originalSeedPathOffset S hF hw s) (measurableSet_activeCutMarks s) scene hcuts
  have icutt : Integrable (cut t) (physicalScenePairKernel scene.1) := by
    simpa only [cut, Set.indicator_apply, mem_ofPred_eq] using
      integrable_originalSceneMarkedPositionReadout_of_integrable
        (measurable_originalSeedPathOffset S hF hw t) (measurableSet_activeCutMarks t) scene hcutt
  have esrc : (∫ x, φ x ∂originalSceneSlabSourceMeasure s t scene) =
      ∫ a, src a ∂physicalScenePairKernel scene.1 := by
    simpa only [originalSceneSlabSourceMeasure, src, Set.indicator_apply, mem_ofPred_eq, add_zero]
      using integral_originalSceneMarkedPositionMeasure_eq_markedReadout (d := fun _ ↦ 0) measurable_const
        (measurableSet_sourceSlabMarks s t) scene hφ.continuous.stronglyMeasurable
  have etgt : (∫ x, φ x ∂originalSceneSlabTargetMeasure s t scene) =
      ∫ a, tgt a ∂physicalScenePairKernel scene.1 := by
    simpa only [originalSceneSlabTargetMeasure, tgt, Set.indicator_apply, mem_ofPred_eq]
      using integral_originalSceneMarkedPositionMeasure_eq_markedReadout measurable_snd
        (measurableSet_targetSlabMarks s t) scene hφ.continuous.stronglyMeasurable
  have ecuts : (∫ x, φ x ∂originalSceneActiveCutMeasure S w s scene) =
      ∫ a, cut s a ∂physicalScenePairKernel scene.1 := by
    simpa only [originalSceneActiveCutMeasure, cut, Set.indicator_apply, mem_ofPred_eq]
      using integral_originalSceneMarkedPositionMeasure_eq_markedReadout
        (measurable_originalSeedPathOffset S hF hw s) (measurableSet_activeCutMarks s)
        scene hφ.continuous.stronglyMeasurable
  have ecutt : (∫ x, φ x ∂originalSceneActiveCutMeasure S w t scene) =
      ∫ a, cut t a ∂physicalScenePairKernel scene.1 := by
    simpa only [originalSceneActiveCutMeasure, cut, Set.indicator_apply, mem_ofPred_eq]
      using integral_originalSceneMarkedPositionMeasure_eq_markedReadout
        (measurable_originalSeedPathOffset S hF hw t) (measurableSet_activeCutMarks t)
        scene hφ.continuous.stronglyMeasurable
  have hbalance : originalSeedPathWeakSlabReadout S w φ s t scene =
      ∫ a, cut t a - cut s a + tgt a - src a ∂physicalScenePairKernel scene.1 := by
    rw [← hweak φ s t hst, hFTC φ hφ s t hst]
    apply integral_congr_ae
    filter_upwards [hlegal] with a ha
    simpa only [cut, tgt, src, originalSeedCompletePath_eq_anchor_add_offset] using
      D.original_complete_path_clock_cut_decomposition hF hw a.1 a.2
        ha.1 ha.2.1 ha.2.2 hst φ
  have isub := integral_sub ((icutt.sub icuts).add itgt) isrc
  have isum := integral_add (icutt.sub icuts) itgt
  have idiff := integral_sub icutt icuts
  simp only [Pi.sub_apply, Pi.add_apply] at isub isum idiff
  rw [hbalance, isub, isum, idiff, esrc, etgt, ecuts, ecutt]
  ring

end OriginalSeedConditionalMoments
end OTSelector.Reconstruction
