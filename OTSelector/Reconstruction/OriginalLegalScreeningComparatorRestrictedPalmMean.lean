import OTSelector.Reconstruction.OriginalStageResidualDensityWindowPorts
import OTSelector.Reconstruction.MarkedStationaryValueLegalOriginalWeightedSourceReadout

/-! Exact Campbell averaging of one original product restriction. -/
open Set Function Filter MeasureTheory ProbabilityTheory
open scoped ENNReal Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OTSelector.Reconstruction
open OTSelector.Probability

/-- Restricting unchanged original edges by a finite spatial window and a
measurable complete-mark event gives its exact Palm mean and actual scene L1.
The window and mark event may be selected after fixing the original law. -/
theorem LegalWeightedStationaryPoissonMatching.productRestrictedPlan_palmReadout_mean
    {q : ℕ} {α β : Measure ℝ}
    {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (Q : LegalWeightedStationaryPoissonMatching q α β kin g)
    {C : Set (Fin q → ℝ)} (hC : MeasurableSet C) (hCfin : volume C ≠ ∞)
    {B : Set (PhysicalPairPalmMark (Fin q))} (hB : MeasurableSet B)
    (f : PhysicalPairPalmMark (Fin q) → ℝ)
    (hf : Measurable f) (hi : Integrable f (legalMarkedJointPalm q Q.law)) :
    Integrable (fun scene ↦ ∫ e, f (physicalPairAnchor e).2
      ∂(originalStageRestrictedPathPlan (C ×ˢ B) scene : Measure (LegalMarkedPhysicalEdge q)))
      (Q.law : Measure (LegalMarkedOptimalInputScene q)) ∧
    (∫ scene, ∫ e, f (physicalPairAnchor e).2
      ∂(originalStageRestrictedPathPlan (C ×ˢ B) scene : Measure (LegalMarkedPhysicalEdge q))
      ∂(Q.law : Measure (LegalMarkedOptimalInputScene q))) =
      volume.real C * ∫ m in B, f m ∂legalMarkedJointPalm q Q.law := by
  classical
  let H := C.indicator (fun _ ↦ (1 : ℝ))
  let F := B.indicator f
  have hH : Integrable H (volume : Measure (Fin q → ℝ)) :=
    (integrableOn_const hCfin).integrable_indicator hC
  have hFI : Integrable F (legalMarkedJointPalm q Q.law) := hi.indicator hB
  have hFM : Measurable F := hf.indicator hB
  have hread := Q.pathWindowReadout_integrable_and_integral
    (fun _ ↦ 0) measurable_const hH hFI
  have heq : (fun scene ↦ ∫ e, f (physicalPairAnchor e).2
      ∂(originalStageRestrictedPathPlan (C ×ˢ B) scene : Measure (LegalMarkedPhysicalEdge q))) =
      legalMarkedPathWindowReadout q (fun _ ↦ 0) H F := by
    funext scene
    let G := fun p : (Fin q → ℝ) × PhysicalPairPalmMark (Fin q) ↦ H (p.1 + 0) * F p.2
    have hG : Measurable G :=
      ((measurable_const.indicator hC).comp (measurable_fst.add measurable_const)).mul
        (hFM.comp measurable_snd)
    change (∫ e in physicalPairAnchor ⁻¹' (C ×ˢ B),
      f (physicalPairAnchor e).2 ∂(scene.1.1 : Measure _)) =
      ∫ p, G p ∂physicalScenePairKernel scene.1
    rw [physicalScenePairKernel_apply,
      integral_map measurable_physicalPairAnchor.aemeasurable hG.aestronglyMeasurable,
      ← integral_indicator ((hC.prod hB).preimage measurable_physicalPairAnchor)]
    apply integral_congr_ae
    exact .of_forall (fun e ↦ by
      by_cases hx : (physicalPairAnchor e).1 ∈ C <;>
        by_cases hm : (physicalPairAnchor e).2 ∈ B <;> simp [G, H, F, hx, hm])
  rw [heq]
  exact ⟨hread.1, by simpa only [H, F, integral_indicator hC, integral_indicator hB,
    setIntegral_const, smul_eq_mul, mul_one] using hread.2⟩

end OTSelector.Reconstruction
