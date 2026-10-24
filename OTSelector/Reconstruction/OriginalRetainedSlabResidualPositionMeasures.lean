import OTSelector.Reconstruction.OriginalCubeTraceCompactnessMarkedPositionMeasure
import OTSelector.Reconstruction.OriginalRetainedPathTraffic
import OTSelector.Reconstruction.OriginalWindowPortConservation

/-! Positive marked-position measures of the unchanged retained and omitted original paths. -/
open Set Function Filter MeasureTheory Module Manifold
open scoped ENNReal Topology ContDiff
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OTSelector.Reconstruction

/-- A literal anchor/mark restriction of the original scene, followed by its true position map. -/
def originalRestrictedSceneMarkedPositionMeasure {q : ℕ}
    (A : Set ((Fin q → ℝ) × PhysicalPairPalmMark (Fin q)))
    (d : PhysicalPairPalmMark (Fin q) → Fin q → ℝ) (B : Set (PhysicalPairPalmMark (Fin q)))
    (scene : LegalMarkedOptimalInputScene q) : Measure (Fin q → ℝ) :=
  (((physicalScenePairKernel scene.1).restrict A).restrict {a | a.2 ∈ B}).map
    (fun a ↦ a.1 + d a.2)

/-- Every retained or omitted positive position measure is dominated by the original one. -/
theorem originalRestrictedSceneMarkedPositionMeasure_le {q : ℕ}
    (A : Set ((Fin q → ℝ) × PhysicalPairPalmMark (Fin q)))
    {d : PhysicalPairPalmMark (Fin q) → Fin q → ℝ} (hd : Measurable d)
    (B : Set (PhysicalPairPalmMark (Fin q))) (scene : LegalMarkedOptimalInputScene q) :
    originalRestrictedSceneMarkedPositionMeasure A d B scene ≤
      originalSceneMarkedPositionMeasure d B scene := by
  exact Measure.map_mono (Measure.restrict_mono_measure Measure.restrict_le_self _)
    (measurable_fst.add (hd.comp measurable_snd))

/-- A Borel retained set and its exact complement partition the full positive cut or endpoint. -/
theorem originalRestrictedSceneMarkedPositionMeasure_add_compl {q : ℕ}
    {A : Set ((Fin q → ℝ) × PhysicalPairPalmMark (Fin q))} (hA : MeasurableSet A)
    {d : PhysicalPairPalmMark (Fin q) → Fin q → ℝ} (hd : Measurable d)
    (B : Set (PhysicalPairPalmMark (Fin q))) (scene : LegalMarkedOptimalInputScene q) :
    originalRestrictedSceneMarkedPositionMeasure A d B scene +
      originalRestrictedSceneMarkedPositionMeasure Aᶜ d B scene =
        originalSceneMarkedPositionMeasure d B scene := by
  have hpos : Measurable (fun a : (Fin q → ℝ) × PhysicalPairPalmMark (Fin q) ↦
      a.1 + d a.2) := measurable_fst.add (hd.comp measurable_snd)
  rw [originalRestrictedSceneMarkedPositionMeasure, originalRestrictedSceneMarkedPositionMeasure,
    ← Measure.map_add _ _ hpos,
    ← Measure.restrict_add, Measure.restrict_add_restrict_compl hA]
  rfl

/-- Campbell local finiteness of the full original position measure controls every restriction. -/
theorem LegalWeightedStationaryPoissonMatching.ae_originalRestrictedPositionMeasure_finiteOnCompacts
    {q : ℕ} {α β : Measure ℝ} {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (Q : LegalWeightedStationaryPoissonMatching q α β kin g)
    (A : Set ((Fin q → ℝ) × PhysicalPairPalmMark (Fin q)))
    {d : PhysicalPairPalmMark (Fin q) → Fin q → ℝ} (hd : Measurable d)
    {B : Set (PhysicalPairPalmMark (Fin q))} (hB : MeasurableSet B) :
    ∀ᵐ scene ∂(Q.law : Measure (LegalMarkedOptimalInputScene q)),
      IsFiniteMeasureOnCompacts (originalRestrictedSceneMarkedPositionMeasure A d B scene) := by
  filter_upwards [Q.ae_originalSceneMarkedPositionMeasure_finiteOnCompacts hd hB]
    with scene hscene
  refine ⟨fun {K} hK ↦ ?_⟩
  exact (originalRestrictedSceneMarkedPositionMeasure_le A hd B scene K).trans_lt
    (hscene.lt_top_of_isCompact hK)

/-- The actual restricted positive position measure integrates the original restricted readout. -/
theorem integral_originalRestrictedPositionMeasure_eq_readout {q : ℕ}
    (A : Set ((Fin q → ℝ) × PhysicalPairPalmMark (Fin q)))
    {d : PhysicalPairPalmMark (Fin q) → Fin q → ℝ} (hd : Measurable d)
    {B : Set (PhysicalPairPalmMark (Fin q))} (hB : MeasurableSet B)
    (scene : LegalMarkedOptimalInputScene q)
    {φ : (Fin q → ℝ) → ℝ} (hφ : StronglyMeasurable φ) :
    (∫ x, φ x ∂originalRestrictedSceneMarkedPositionMeasure A d B scene) =
      ∫ a in A, {a : (Fin q → ℝ) × PhysicalPairPalmMark (Fin q) | a.2 ∈ B}.indicator
        (fun a ↦ φ (a.1 + d a.2)) a ∂physicalScenePairKernel scene.1 := by
  have hpos : Measurable (fun a : (Fin q → ℝ) × PhysicalPairPalmMark (Fin q) ↦
      a.1 + d a.2) := measurable_fst.add (hd.comp measurable_snd)
  rw [originalRestrictedSceneMarkedPositionMeasure, integral_map hpos.aemeasurable
      hφ.aestronglyMeasurable]
  exact (integral_indicator (hB.preimage measurable_snd)).symm

/-- The literal marked readout is integrable under the actual restricted original pair measure. -/
theorem integrable_originalRestrictedPositionReadout_of_integrable {q : ℕ}
    (A : Set ((Fin q → ℝ) × PhysicalPairPalmMark (Fin q)))
    {d : PhysicalPairPalmMark (Fin q) → Fin q → ℝ} (hd : Measurable d)
    {B : Set (PhysicalPairPalmMark (Fin q))} (hB : MeasurableSet B)
    (scene : LegalMarkedOptimalInputScene q) {φ : (Fin q → ℝ) → ℝ}
    (hi : Integrable φ (originalRestrictedSceneMarkedPositionMeasure A d B scene)) :
    Integrable (fun a ↦
      {a : (Fin q → ℝ) × PhysicalPairPalmMark (Fin q) | a.2 ∈ B}.indicator
        (fun a ↦ φ (a.1 + d a.2)) a) ((physicalScenePairKernel scene.1).restrict A) := by
  have hir := hi.comp_aemeasurable
    (measurable_fst.add (hd.comp measurable_snd)).aemeasurable
  exact (integrable_indicator_iff (hB.preimage measurable_snd)).mpr hir

end OTSelector.Reconstruction
