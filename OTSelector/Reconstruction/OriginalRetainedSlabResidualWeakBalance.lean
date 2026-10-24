import OTSelector.Reconstruction.OriginalRetainedSlabResidualPositionMeasures
import OTSelector.Reconstruction.OriginalCubeTraceCompactnessSlabResidualMeasures

/-! Exact positive weak-slab balances for any retained restriction and its actual complement. -/
open Set Function Filter MeasureTheory Module Manifold Matrix
open scoped ENNReal Topology ContDiff
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OTSelector.Reconstruction
open OTSelector.Geometry ContinuousFinslerNorm OTSelector.Probability

/-- The unchanged original sources in the slab and in the literal selected path set. -/
def originalRestrictedSceneSlabSourceMeasure {q : ℕ}
    (A : Set ((Fin q → ℝ) × PhysicalPairPalmMark (Fin q))) (s t : ℝ)
    (scene : LegalMarkedOptimalInputScene q) : Measure (Fin q → ℝ) :=
  originalRestrictedSceneMarkedPositionMeasure A (fun _ ↦ 0)
    {m | s ≤ m.1.1 ∧ m.1.1 < t} scene

/-- The unchanged original targets in the slab and in that same selected path set. -/
def originalRestrictedSceneSlabTargetMeasure {q : ℕ}
    (A : Set ((Fin q → ℝ) × PhysicalPairPalmMark (Fin q))) (s t : ℝ)
    (scene : LegalMarkedOptimalInputScene q) : Measure (Fin q → ℝ) :=
  originalRestrictedSceneMarkedPositionMeasure A (fun m ↦ m.2)
    {m | s < m.1.2 ∧ m.1.2 ≤ t} scene

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}

/-- A positive cut of exactly the selected original paths, without any endpoint cube filter. -/
def originalRestrictedSceneActiveCutMeasure (S : CalibratedLevelSeedPatch F u)
    (w : S.covector.ker)
    (A : Set ((Fin (finrank ℝ S.covector.ker) → ℝ) ×
      PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker))))
    (c : ℝ) (scene : LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker)) :
    Measure (Fin (finrank ℝ S.covector.ker) → ℝ) :=
  originalRestrictedSceneMarkedPositionMeasure A (originalSeedPathOffset S w c)
    {m | m.1.1 < c ∧ c < m.1.2} scene

/-- The actual one-pair derivative integral between its unchanged clipped clock cuts. -/
def originalSeedSlabPairDerivativeIntegral (S : CalibratedLevelSeedPatch F u)
    (w : S.covector.ker) (φ : (Fin (finrank ℝ S.covector.ker) → ℝ) → ℝ) (s t : ℝ)
    (p : (Fin (finrank ℝ S.covector.ker) → ℝ) ×
      PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker))) : ℝ :=
  ∫ r in max p.2.1.1 (min s p.2.1.2)..max p.2.1.1 (min t p.2.1.2),
    fderiv ℝ φ (originalSeedCompletePath S w p.1 p.2 r)
      (originalSeedKernel S w (r - (S.level : ℝ)) *ᵥ originalSeedPairMomentum S w p.2) ∂volume

/-- The original clipped weak slab, restricted only by the same actual complete-path set. -/
def originalRestrictedSeedPathWeakSlabReadout (S : CalibratedLevelSeedPatch F u)
    (w : S.covector.ker)
    (A : Set ((Fin (finrank ℝ S.covector.ker) → ℝ) ×
      PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker))))
    (φ : (Fin (finrank ℝ S.covector.ker) → ℝ) → ℝ) (s t : ℝ)
    (scene : LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker)) : ℝ :=
  ∫ p in A, originalSeedSlabPairDerivativeIntegral S w φ s t p ∂physicalScenePairKernel scene.1

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

theorem ae_originalRestrictedSceneSlabCharges_finiteOnCompacts
    (S : CalibratedLevelSeedPatch F u) (hF : F.IsSmoothStronglyConvex)
    {w : S.covector.ker} (hw : w ∈ S.labels)
    {μ ν : Measure ℝ} {kin : ℝ → ℝ → (Fin (finrank ℝ S.covector.ker) → ℝ) → ℝ}
    {g : ℝ → ℝ → ℝ}
    (Q : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν kin g)
    (A : Set ((Fin (finrank ℝ S.covector.ker) → ℝ) ×
      PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker)))) (s t : ℝ) :
    ∀ᵐ scene ∂(Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))),
      IsFiniteMeasureOnCompacts (originalRestrictedSceneSlabSourceMeasure A s t scene) ∧
      IsFiniteMeasureOnCompacts (originalRestrictedSceneSlabTargetMeasure A s t scene) ∧
      IsFiniteMeasureOnCompacts (originalRestrictedSceneActiveCutMeasure S w A s scene) ∧
      IsFiniteMeasureOnCompacts (originalRestrictedSceneActiveCutMeasure S w A t scene) := by
  filter_upwards [
    Q.ae_originalRestrictedPositionMeasure_finiteOnCompacts A
      (d := fun _ ↦ 0) measurable_const (measurableSet_sourceSlabMarks s t),
    Q.ae_originalRestrictedPositionMeasure_finiteOnCompacts A
      (d := fun m ↦ m.2) measurable_snd (measurableSet_targetSlabMarks s t),
    Q.ae_originalRestrictedPositionMeasure_finiteOnCompacts A
      (measurable_originalSeedPathOffset S hF hw s) (measurableSet_activeCutMarks s),
    Q.ae_originalRestrictedPositionMeasure_finiteOnCompacts A
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
theorem ae_all_originalRestrictedWeakSlab_integrable_balance
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {kin : ℝ → ℝ → (Fin (finrank ℝ S.covector.ker) → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (Q : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν kin g)
    (A : Set ((Fin (finrank ℝ S.covector.ker) → ℝ) ×
      PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker)))) {s t : ℝ} (hst : s ≤ t) :
    ∀ᵐ scene ∂(Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))),
      ∀ φ : (Fin (finrank ℝ S.covector.ker) → ℝ) → ℝ,
        ContDiff ℝ 1 φ → HasCompactSupport φ →
        Integrable (originalSeedSlabPairDerivativeIntegral S w φ s t)
          ((physicalScenePairKernel scene.1).restrict A) ∧
        -originalRestrictedSeedPathWeakSlabReadout S w A φ s t scene =
          (∫ x, φ x ∂originalRestrictedSceneSlabSourceMeasure A s t scene) -
          (∫ x, φ x ∂originalRestrictedSceneSlabTargetMeasure A s t scene) +
          (∫ x, φ x ∂originalRestrictedSceneActiveCutMeasure S w A s scene) -
          (∫ x, φ x ∂originalRestrictedSceneActiveCutMeasure S w A t scene) := by
  filter_upwards [ae_originalRestrictedSceneSlabCharges_finiteOnCompacts S hF hw Q A s t,
    D.ae_ae_original_pairKernel_interior_forward Q]
    with scene hfinite hlegal
  intro φ hφ hcφ
  have : IsFiniteMeasureOnCompacts (originalRestrictedSceneSlabSourceMeasure A s t scene) := hfinite.1
  have : IsFiniteMeasureOnCompacts (originalRestrictedSceneSlabTargetMeasure A s t scene) := hfinite.2.1
  have : IsFiniteMeasureOnCompacts (originalRestrictedSceneActiveCutMeasure S w A s scene) := hfinite.2.2.1
  have : IsFiniteMeasureOnCompacts (originalRestrictedSceneActiveCutMeasure S w A t scene) := hfinite.2.2.2
  have hsrc : Integrable φ (originalRestrictedSceneSlabSourceMeasure A s t scene) :=
    hφ.continuous.integrable_of_hasCompactSupport hcφ
  have htgt : Integrable φ (originalRestrictedSceneSlabTargetMeasure A s t scene) :=
    hφ.continuous.integrable_of_hasCompactSupport hcφ
  have hcuts : Integrable φ (originalRestrictedSceneActiveCutMeasure S w A s scene) :=
    hφ.continuous.integrable_of_hasCompactSupport hcφ
  have hcutt : Integrable φ (originalRestrictedSceneActiveCutMeasure S w A t scene) :=
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
  have isrc : Integrable src ((physicalScenePairKernel scene.1).restrict A) := by
    simpa only [src, Set.indicator_apply, mem_ofPred_eq, add_zero] using
      integrable_originalRestrictedPositionReadout_of_integrable A measurable_const
        (measurableSet_sourceSlabMarks s t) scene hsrc
  have itgt : Integrable tgt ((physicalScenePairKernel scene.1).restrict A) := by
    simpa only [tgt, Set.indicator_apply, mem_ofPred_eq] using
      integrable_originalRestrictedPositionReadout_of_integrable A measurable_snd
        (measurableSet_targetSlabMarks s t) scene htgt
  have icuts : Integrable (cut s) ((physicalScenePairKernel scene.1).restrict A) := by
    simpa only [cut, Set.indicator_apply, mem_ofPred_eq] using
      integrable_originalRestrictedPositionReadout_of_integrable A
        (measurable_originalSeedPathOffset S hF hw s) (measurableSet_activeCutMarks s) scene hcuts
  have icutt : Integrable (cut t) ((physicalScenePairKernel scene.1).restrict A) := by
    simpa only [cut, Set.indicator_apply, mem_ofPred_eq] using
      integrable_originalRestrictedPositionReadout_of_integrable A
        (measurable_originalSeedPathOffset S hF hw t) (measurableSet_activeCutMarks t) scene hcutt
  have esrc : (∫ x, φ x ∂originalRestrictedSceneSlabSourceMeasure A s t scene) =
      ∫ a, src a ∂((physicalScenePairKernel scene.1).restrict A) := by
    simpa only [originalRestrictedSceneSlabSourceMeasure, src, Set.indicator_apply, mem_ofPred_eq, add_zero]
      using integral_originalRestrictedPositionMeasure_eq_readout A (d := fun _ ↦ 0) measurable_const
        (measurableSet_sourceSlabMarks s t) scene hφ.continuous.stronglyMeasurable
  have etgt : (∫ x, φ x ∂originalRestrictedSceneSlabTargetMeasure A s t scene) =
      ∫ a, tgt a ∂((physicalScenePairKernel scene.1).restrict A) := by
    simpa only [originalRestrictedSceneSlabTargetMeasure, tgt, Set.indicator_apply, mem_ofPred_eq]
      using integral_originalRestrictedPositionMeasure_eq_readout A measurable_snd
        (measurableSet_targetSlabMarks s t) scene hφ.continuous.stronglyMeasurable
  have ecuts : (∫ x, φ x ∂originalRestrictedSceneActiveCutMeasure S w A s scene) =
      ∫ a, cut s a ∂((physicalScenePairKernel scene.1).restrict A) := by
    simpa only [originalRestrictedSceneActiveCutMeasure, cut, Set.indicator_apply, mem_ofPred_eq]
      using integral_originalRestrictedPositionMeasure_eq_readout A
        (measurable_originalSeedPathOffset S hF hw s) (measurableSet_activeCutMarks s)
        scene hφ.continuous.stronglyMeasurable
  have ecutt : (∫ x, φ x ∂originalRestrictedSceneActiveCutMeasure S w A t scene) =
      ∫ a, cut t a ∂((physicalScenePairKernel scene.1).restrict A) := by
    simpa only [originalRestrictedSceneActiveCutMeasure, cut, Set.indicator_apply, mem_ofPred_eq]
      using integral_originalRestrictedPositionMeasure_eq_readout A
        (measurable_originalSeedPathOffset S hF hw t) (measurableSet_activeCutMarks t)
        scene hφ.continuous.stronglyMeasurable
  have hpoint : originalSeedSlabPairDerivativeIntegral S w φ s t =ᵐ[
      (physicalScenePairKernel scene.1).restrict A]
      fun a ↦ cut t a - cut s a + tgt a - src a := by
    filter_upwards [ae_restrict_of_ae hlegal] with a ha
    unfold originalSeedSlabPairDerivativeIntegral
    rw [D.integral_originalSeedCompletePath_slab_eq_endpoints hF hw a.1 a.2
      ha.1 ha.2.1 ha.2.2.le hst hφ]
    simpa only [cut, tgt, src, originalSeedCompletePath_eq_anchor_add_offset] using
      D.original_complete_path_clock_cut_decomposition hF hw a.1 a.2
        ha.1 ha.2.1 ha.2.2 hst φ
  refine ⟨(((icutt.sub icuts).add itgt).sub isrc).congr hpoint.symm, ?_⟩
  have hbalance : originalRestrictedSeedPathWeakSlabReadout S w A φ s t scene =
      ∫ a, cut t a - cut s a + tgt a - src a ∂((physicalScenePairKernel scene.1).restrict A) :=
    integral_congr_ae hpoint
  have isub := integral_sub ((icutt.sub icuts).add itgt) isrc
  have isum := integral_add (icutt.sub icuts) itgt
  have idiff := integral_sub icutt icuts
  simp only [Pi.sub_apply, Pi.add_apply] at isub isum idiff
  rw [hbalance, isub, isum, idiff, esrc, etgt, ecuts, ecutt]
  ring

/-- The omitted weak slab is exactly the full original slab minus the same retained slab.
All four omitted positive charges remain present, including cuts of edges with exterior endpoints. -/
theorem ae_all_originalWeakSlab_sub_restricted_positive_balance
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {kin : ℝ → ℝ → (Fin (finrank ℝ S.covector.ker) → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (Q : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν kin g)
    {A : Set ((Fin (finrank ℝ S.covector.ker) → ℝ) ×
      PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker)))} (hA : MeasurableSet A)
    {s t : ℝ} (hst : s ≤ t) :
    ∀ᵐ scene ∂(Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))),
      ∀ φ : (Fin (finrank ℝ S.covector.ker) → ℝ) → ℝ,
        ContDiff ℝ 1 φ → HasCompactSupport φ →
        originalSeedPathWeakSlabReadout S w φ s t scene =
          originalRestrictedSeedPathWeakSlabReadout S w A φ s t scene +
          originalRestrictedSeedPathWeakSlabReadout S w Aᶜ φ s t scene ∧
        -(originalSeedPathWeakSlabReadout S w φ s t scene -
            originalRestrictedSeedPathWeakSlabReadout S w A φ s t scene) =
          (∫ x, φ x ∂originalRestrictedSceneSlabSourceMeasure Aᶜ s t scene) -
          (∫ x, φ x ∂originalRestrictedSceneSlabTargetMeasure Aᶜ s t scene) +
          (∫ x, φ x ∂originalRestrictedSceneActiveCutMeasure S w Aᶜ s scene) -
          (∫ x, φ x ∂originalRestrictedSceneActiveCutMeasure S w Aᶜ t scene) := by
  filter_upwards [D.ae_all_originalRestrictedWeakSlab_integrable_balance hF hw Q univ hst,
    D.ae_all_originalRestrictedWeakSlab_integrable_balance hF hw Q Aᶜ hst]
    with scene hfull homitted
  intro φ hφ hcφ
  have hi : Integrable (originalSeedSlabPairDerivativeIntegral S w φ s t)
      (physicalScenePairKernel scene.1) := by
    simpa only [Measure.restrict_univ] using (hfull φ hφ hcφ).1
  have hsplit := integral_add_compl hA hi
  change originalRestrictedSeedPathWeakSlabReadout S w A φ s t scene +
      originalRestrictedSeedPathWeakSlabReadout S w Aᶜ φ s t scene =
        originalSeedPathWeakSlabReadout S w φ s t scene at hsplit
  refine ⟨hsplit.symm, ?_⟩
  have hb := (homitted φ hφ hcφ).2
  linarith

end OriginalSeedConditionalMoments
end OTSelector.Reconstruction
