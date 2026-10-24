import OTSelector.Reconstruction.OriginalMarkedWindowCounts
import Mathlib.Topology.MetricSpace.ProperSpace.Real
import Mathlib.MeasureTheory.Integral.CompactlySupported

/-! Actual positive original marked-position measures are locally finite by their Campbell law. -/
open Set Function Filter MeasureTheory Metric ProbabilityTheory
open scoped ENNReal
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OTSelector.Reconstruction

/-- The actual original scene pair kernel, restricted by an unchanged paired-mark event and
pushed to its literal mark-dependent spatial position. -/
def originalSceneMarkedPositionMeasure {q : ℕ}
    (d : PhysicalPairPalmMark (Fin q) → Fin q → ℝ) (B : Set (PhysicalPairPalmMark (Fin q)))
    (scene : LegalMarkedOptimalInputScene q) : Measure (Fin q → ℝ) :=
  ((physicalScenePairKernel scene.1).restrict {a | a.2 ∈ B}).map (fun a ↦ a.1 + d a.2)

/-- Actual spatial mass is precisely its unchanged original marked-window count. -/
theorem originalSceneMarkedPositionMeasure_apply {q : ℕ}
    {d : PhysicalPairPalmMark (Fin q) → Fin q → ℝ} (hd : Measurable d)
    (B : Set (PhysicalPairPalmMark (Fin q))) (scene : LegalMarkedOptimalInputScene q)
    {W : Set (Fin q → ℝ)} (hW : MeasurableSet W) :
    originalSceneMarkedPositionMeasure d B scene W =
      physicalScenePairKernel scene.1 {a | a.1 + d a.2 ∈ W ∧ a.2 ∈ B} := by
  have hpos : Measurable (fun a : (Fin q → ℝ) × PhysicalPairPalmMark (Fin q) ↦
      a.1 + d a.2) := measurable_fst.add (hd.comp measurable_snd)
  rw [originalSceneMarkedPositionMeasure, Measure.map_apply hpos hW,
    Measure.restrict_apply (hW.preimage hpos)]
  rfl

/-- The actual positive position measure has exactly its original spatial/Palm intensity. -/
theorem LegalWeightedStationaryPoissonMatching.lintegral_originalSceneMarkedPositionMeasure
    {q : ℕ} {α β : Measure ℝ} {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (Q : LegalWeightedStationaryPoissonMatching q α β kin g)
    {d : PhysicalPairPalmMark (Fin q) → Fin q → ℝ} (hd : Measurable d)
    {B : Set (PhysicalPairPalmMark (Fin q))} (hB : MeasurableSet B)
    {W : Set (Fin q → ℝ)} (hW : MeasurableSet W) :
    (∫⁻ scene, originalSceneMarkedPositionMeasure d B scene W
      ∂(Q.law : Measure (LegalMarkedOptimalInputScene q))) =
      volume W * legalMarkedJointPalm q Q.law B := by
  simp_rw [originalSceneMarkedPositionMeasure_apply hd B _ hW]
  exact Q.lintegral_original_markedWindow_count d hd hW hB

/-- One full-measure set of original scenes has finite marked-position mass on every compact
spatial set. This follows from actual Campbell counts on countably many closed balls. -/
theorem LegalWeightedStationaryPoissonMatching.ae_originalSceneMarkedPositionMeasure_finiteOnCompacts
    {q : ℕ} {α β : Measure ℝ} {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (Q : LegalWeightedStationaryPoissonMatching q α β kin g)
    {d : PhysicalPairPalmMark (Fin q) → Fin q → ℝ} (hd : Measurable d)
    {B : Set (PhysicalPairPalmMark (Fin q))} (hB : MeasurableSet B) :
    ∀ᵐ scene ∂(Q.law : Measure (LegalMarkedOptimalInputScene q)),
      IsFiniteMeasureOnCompacts (originalSceneMarkedPositionMeasure d B scene) := by
  have : IsProbabilityMeasure (legalMarkedJointPalm q Q.law) := Q.palm_probability
  have hballs (n : ℕ) : ∀ᵐ scene ∂(Q.law : Measure (LegalMarkedOptimalInputScene q)),
      originalSceneMarkedPositionMeasure d B scene (closedBall 0 (n : ℝ)) < (∞ : ℝ≥0∞) := by
    have hA : MeasurableSet {a : (Fin q → ℝ) × PhysicalPairPalmMark (Fin q) |
        a.1 + d a.2 ∈ closedBall 0 (n : ℝ) ∧ a.2 ∈ B} :=
      (measurableSet_closedBall.preimage (measurable_fst.add (hd.comp measurable_snd))).inter
        (hB.preimage measurable_snd)
    have hm : Measurable (fun scene : LegalMarkedOptimalInputScene q ↦
        originalSceneMarkedPositionMeasure d B scene (closedBall 0 (n : ℝ))) := by
      simp_rw [originalSceneMarkedPositionMeasure_apply hd B _ measurableSet_closedBall]
      exact (Kernel.measurable_coe physicalScenePairKernel hA).comp measurable_fst
    apply ae_lt_top hm
    rw [Q.lintegral_originalSceneMarkedPositionMeasure hd hB measurableSet_closedBall]
    exact (ENNReal.mul_lt_top (isCompact_closedBall (0 : Fin q → ℝ) (n : ℝ)).measure_lt_top
      (measure_lt_top (legalMarkedJointPalm q Q.law) B)).ne
  filter_upwards [ae_all_iff.mpr hballs] with scene hs
  refine ⟨fun {K} hK ↦ ?_⟩
  obtain ⟨r, hr⟩ := hK.isBounded.subset_closedBall (0 : Fin q → ℝ)
  obtain ⟨n, hn⟩ := exists_nat_gt r
  exact (measure_mono (hr.trans (closedBall_subset_closedBall hn.le))).trans_lt (hs n)

/-- The same original positive position measure integrates every continuous compact test on
one full-measure scene set. No local finiteness of a selected cloud is postulated. -/
theorem LegalWeightedStationaryPoissonMatching.ae_all_integrable_originalSceneMarkedPositionMeasure
    {q : ℕ} {α β : Measure ℝ} {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (Q : LegalWeightedStationaryPoissonMatching q α β kin g)
    {d : PhysicalPairPalmMark (Fin q) → Fin q → ℝ} (hd : Measurable d)
    {B : Set (PhysicalPairPalmMark (Fin q))} (hB : MeasurableSet B) :
    ∀ᵐ scene ∂(Q.law : Measure (LegalMarkedOptimalInputScene q)),
      ∀ φ : (Fin q → ℝ) → ℝ, Continuous φ → HasCompactSupport φ →
        Integrable φ (originalSceneMarkedPositionMeasure d B scene) := by
  filter_upwards [Q.ae_originalSceneMarkedPositionMeasure_finiteOnCompacts hd hB]
    with scene hscene
  intro φ hφ hcφ
  have := hscene
  exact hφ.integrable_of_hasCompactSupport hcφ

/-- Integration against the actual positive position measure is the literal original
mark-restricted scene readout. The map and restriction are genuine measure operations. -/
theorem integral_originalSceneMarkedPositionMeasure_eq_markedReadout {q : ℕ}
    {d : PhysicalPairPalmMark (Fin q) → Fin q → ℝ} (hd : Measurable d)
    {B : Set (PhysicalPairPalmMark (Fin q))} (hB : MeasurableSet B)
    (scene : LegalMarkedOptimalInputScene q)
    {φ : (Fin q → ℝ) → ℝ} (hφ : StronglyMeasurable φ) :
    (∫ x, φ x ∂originalSceneMarkedPositionMeasure d B scene) =
      ∫ a, {a : (Fin q → ℝ) × PhysicalPairPalmMark (Fin q) | a.2 ∈ B}.indicator
        (fun a ↦ φ (a.1 + d a.2)) a ∂physicalScenePairKernel scene.1 := by
  have hpos : Measurable (fun a : (Fin q → ℝ) × PhysicalPairPalmMark (Fin q) ↦
      a.1 + d a.2) := measurable_fst.add (hd.comp measurable_snd)
  rw [originalSceneMarkedPositionMeasure, integral_map hpos.aemeasurable hφ.aestronglyMeasurable]
  exact (integral_indicator (hB.preimage measurable_snd)).symm

/-- A genuinely integrable test of the actual positive position measure has an integrable
literal marked readout under the same original scene pair kernel. -/
theorem integrable_originalSceneMarkedPositionReadout_of_integrable {q : ℕ}
    {d : PhysicalPairPalmMark (Fin q) → Fin q → ℝ} (hd : Measurable d)
    {B : Set (PhysicalPairPalmMark (Fin q))} (hB : MeasurableSet B)
    (scene : LegalMarkedOptimalInputScene q)
    {φ : (Fin q → ℝ) → ℝ}
    (hi : Integrable φ (originalSceneMarkedPositionMeasure d B scene)) :
    Integrable (fun a ↦
      {a : (Fin q → ℝ) × PhysicalPairPalmMark (Fin q) | a.2 ∈ B}.indicator
        (fun a ↦ φ (a.1 + d a.2)) a) (physicalScenePairKernel scene.1) := by
  have hpos : Measurable (fun a : (Fin q → ℝ) × PhysicalPairPalmMark (Fin q) ↦
      a.1 + d a.2) := measurable_fst.add (hd.comp measurable_snd)
  have hir := hi.comp_aemeasurable hpos.aemeasurable
  exact (integrable_indicator_iff (hB.preimage measurable_snd)).mpr hir

end OTSelector.Reconstruction
