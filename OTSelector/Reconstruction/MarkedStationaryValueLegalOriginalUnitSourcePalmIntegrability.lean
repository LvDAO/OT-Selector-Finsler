import OTSelector.Reconstruction.MarkedStationaryValueLegalOriginalGridExchangeExpectedSaving

/-! Exact unit-window/kernel equivalences and nonnegative Palm integrability. -/
open Set Function MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Classical
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 900000
set_option linter.unusedSectionVars false

variable {q : ℕ}

/-- The actual unchanged source unit-window of an arbitrary full original mark observable. -/
def originalUnitSourceMarkReadout (f : PhysicalPairPalmMark (Fin q) → ℝ)
    (s : LegalMarkedOptimalInputScene q) : ℝ :=
  ∫ e : LegalMarkedPhysicalEdge q,
    legalMarkedUnitWindowWeight q e.1.1 * f ((e.1.2, e.2.2), e.2.1 - e.1.1)
    ∂(s.1.1 : Measure (LegalMarkedPhysicalEdge q))

private theorem originalUnitSourceIndicator_eq
    (f : PhysicalPairPalmMark (Fin q) → ℝ) (e : LegalMarkedPhysicalEdge q) :
    (palmUnitCube (Fin q) ×ˢ (Set.univ : Set (PhysicalPairPalmMark (Fin q)))).indicator
      (fun p ↦ f p.2) (physicalPairAnchor e) =
      legalMarkedUnitWindowWeight q e.1.1 * f ((e.1.2, e.2.2), e.2.1 - e.1.1) := by
  by_cases hx : e.1.1 ∈ palmUnitCube (Fin q) <;>
    simp [legalMarkedUnitWindowWeight, physicalPairAnchor, hx]

/-- Actual edge-window integrability is precisely local full-mark Palm-kernel
integrability; no global stationarity or moment hypothesis is needed. -/
theorem integrable_originalUnitSourceMark_iff
    (f : PhysicalPairPalmMark (Fin q) → ℝ) (hf : Measurable f)
    (s : LegalMarkedOptimalInputScene q) :
    Integrable f (legalMarkedSceneUnitPalmKernel q s) ↔
      Integrable (fun e : LegalMarkedPhysicalEdge q ↦
        legalMarkedUnitWindowWeight q e.1.1 * f ((e.1.2, e.2.2), e.2.1 - e.1.1))
        (s.1.1 : Measure (LegalMarkedPhysicalEdge q)) := by
  let R := palmUnitCube (Fin q) ×ˢ (Set.univ : Set (PhysicalPairPalmMark (Fin q)))
  have hR : MeasurableSet R := (measurableSet_palmUnitCube (Fin q)).prod MeasurableSet.univ
  have hF : Measurable (R.indicator (fun p ↦ f p.2)) :=
    (hf.comp measurable_snd).indicator hR
  rw [legalMarkedSceneUnitPalmKernel_apply, cubePalm,
    integrable_map_measure hf.aestronglyMeasurable measurable_snd.aemeasurable]
  change IntegrableOn (fun p ↦ f p.2) R (physicalScenePairKernel s.1) ↔ _
  rw [← integrable_indicator_iff hR, physicalScenePairKernel_apply,
    integrable_map_measure hF.aestronglyMeasurable measurable_physicalPairAnchor.aemeasurable]
  rw [show (R.indicator (fun p ↦ f p.2)) ∘ physicalPairAnchor =
      (fun e : LegalMarkedPhysicalEdge q ↦ legalMarkedUnitWindowWeight q e.1.1 *
        f ((e.1.2, e.2.2), e.2.1 - e.1.1)) from funext (originalUnitSourceIndicator_eq f)]

/-- The literal physical unit-source integral is exactly the same scene's
unit Palm-kernel readout, with every original paired clock and displacement. -/
theorem legalMarkedScenePalmReadout_eq_originalUnitSourceMarkReadout
    (f : PhysicalPairPalmMark (Fin q) → ℝ) (hf : Measurable f)
    (s : LegalMarkedOptimalInputScene q) :
    legalMarkedScenePalmReadout q f s = originalUnitSourceMarkReadout f s := by
  let R := palmUnitCube (Fin q) ×ˢ (Set.univ : Set (PhysicalPairPalmMark (Fin q)))
  have hR : MeasurableSet R := (measurableSet_palmUnitCube (Fin q)).prod MeasurableSet.univ
  have hF : Measurable (R.indicator (fun p ↦ f p.2)) :=
    (hf.comp measurable_snd).indicator hR
  rw [legalMarkedScenePalmReadout, legalMarkedSceneUnitPalmKernel_apply, cubePalm,
    integral_map measurable_snd.aemeasurable hf.aestronglyMeasurable]
  change (∫ p in R, f p.2 ∂physicalScenePairKernel s.1) = _
  rw [← integral_indicator hR, physicalScenePairKernel_apply,
    integral_map measurable_physicalPairAnchor.aemeasurable hF.aestronglyMeasurable]
  apply integral_congr_ae
  exact Eventually.of_forall (originalUnitSourceIndicator_eq f)

/-- For a nonnegative genuine Palm observable, integrable actual scene
readouts and AE fiber integrability give its full Palm L1 integrability. -/
theorem integrable_nonneg_jointPalm_of_scene_readout
    (Q : ProbabilityMeasure (LegalMarkedOptimalInputScene q))
    (f : PhysicalPairPalmMark (Fin q) → ℝ) (hf : Measurable f) (hfn : ∀ m, 0 ≤ f m)
    (hfiber : ∀ᵐ s ∂(Q : Measure (LegalMarkedOptimalInputScene q)),
      Integrable f (legalMarkedSceneUnitPalmKernel q s))
    (hread : Integrable (legalMarkedScenePalmReadout q f)
      (Q : Measure (LegalMarkedOptimalInputScene q))) :
    Integrable f (legalMarkedJointPalm q Q) := by
  rw [legalMarkedJointPalm_eq_unitPalmKernel_comp]
  apply (Measure.integrable_comp_iff hf.aestronglyMeasurable).mpr
  refine ⟨hfiber, ?_⟩
  convert hread using 1
  funext s
  apply integral_congr_ae
  exact Eventually.of_forall (fun m ↦ Real.norm_of_nonneg (hfn m))

end OTSelector.Reconstruction
