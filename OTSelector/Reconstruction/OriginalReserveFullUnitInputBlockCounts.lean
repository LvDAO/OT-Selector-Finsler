import OTSelector.Reconstruction.OriginalReserveFullUnitInputExperiment
import OTSelector.Reconstruction.OriginalReserveDilatedBlockCounts
import OTSelector.Probability.PoissonPairDiscrepancyTransfer
import OTSelector.Reconstruction.OriginalClasswiseOriginalAtomRepairClockSlabBlocksSets

/-! Exact unit-intensity clock-block count laws in the full original joined experiment. -/
open Set Function MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators Classical
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000

/-- A genuine full-input marginal determines the actual block-count pair;
no matching law is imposed on the new scene or its auxiliary witnesses. -/
theorem hasLaw_originalPhysicalBlockCountPair_of_inputLaw {q : ℕ}
    {α β : Measure ℝ} [IsProbabilityMeasure α] [IsProbabilityMeasure β]
    {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (Q : LegalWeightedStationaryPoissonMatching q α β kin g)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (input : Ω → LocalFiniteMeasure (LegalColoredInputPoint q)) (hinput : Measurable input)
    (hlaw : P.map input = (Q.law : Measure (LegalMarkedOptimalInputScene q)).map Prod.snd)
    {K : Set (Fin q → ℝ)} (hK : IsCompact K) {S T : Set ℝ}
    (hS : MeasurableSet S) (hT : MeasurableSet T) :
    HasLaw (fun p ↦
      (⌊(input p : Measure (LegalColoredInputPoint q)).real ((K ×ˢ S) ×ˢ {0})⌋₊,
        ⌊(input p : Measure (LegalColoredInputPoint q)).real ((K ×ˢ T) ×ˢ {1})⌋₊))
      ((poissonMeasure ((volume K).toNNReal * (α S).toNNReal)).prod
        (poissonMeasure ((volume K).toNNReal * (β T).toNNReal))) P := by
  let counts : LocalFiniteMeasure (LegalColoredInputPoint q) → ℕ × ℕ := fun ζ ↦
    (⌊(ζ : Measure (LegalColoredInputPoint q)).real ((K ×ˢ S) ×ˢ {0})⌋₊,
      ⌊(ζ : Measure (LegalColoredInputPoint q)).real ((K ×ˢ T) ×ˢ {1})⌋₊)
  have hc : Measurable counts :=
    ((((Measure.measurable_coe ((hK.measurableSet.prod hS).prod (measurableSet_singleton 0))).comp
      measurable_localFiniteMeasure_coe).ennreal_toReal).nat_floor).prodMk
    ((((Measure.measurable_coe ((hK.measurableSet.prod hT).prod (measurableSet_singleton 1))).comp
      measurable_localFiniteMeasure_coe).ennreal_toReal).nat_floor)
  refine ⟨(hc.comp hinput).aemeasurable, ?_⟩
  change P.map (counts ∘ input) = _
  rw [← Measure.map_map hc hinput, hlaw, Measure.map_map hc measurable_snd]
  exact (Q.hasLaw_originalMainPhysicalBlockCount_pair hK hS hT).map_eq

namespace OriginalReserveFullUnitInputExperiment
variable {q : ℕ} {α β : Measure ℝ} [IsProbabilityMeasure α] [IsProbabilityMeasure β]
  {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
  {Main Reserve : LegalWeightedStationaryPoissonMatching q α β kin g}
  {b : OrthonormalBasis (Fin q) ℝ (EuclideanSpace ℝ (Fin q))}
  {θ R : ℝ} {hθ : 0 < θ} {hθ1 : θ < 1}
  (X : OriginalReserveFullUnitInputExperiment Main Reserve b θ hθ hθ1 R)

/-- The full original joining preserves the entire actual unit-scene marginal. -/
theorem fullLaw_unit_scene :
    (X.fullLaw : Measure (OriginalReserveUnitExperimentSpace q × TwoMarkedCloudSpace q ℝ ℝ)).map
      (fun p ↦ originalReserveUnitInputReadout q θ hθ hθ1 p.1) =
      (legalOriginalIntensityReserveLaw Main Reserve θ hθ hθ1 : Measure (LegalMarkedOptimalInputScene q)) := by
  change (X.fullLaw : Measure (OriginalReserveUnitExperimentSpace q × TwoMarkedCloudSpace q ℝ ℝ)).map
    (originalReserveUnitInputReadout q θ hθ hθ1 ∘ Prod.fst) = _
  rw [← Measure.map_map (measurable_originalReserveUnitInputReadout q θ hθ hθ1) measurable_fst,
    X.fullLaw_fst, X.baseLaw_unit_input]

/-- The complete colored unit-input random measure in the same full experiment
retains the original unit-intensity input law. -/
theorem fullLaw_colored_unit_input (hq : 0 < q) :
    (X.fullLaw : Measure (OriginalReserveUnitExperimentSpace q × TwoMarkedCloudSpace q ℝ ℝ)).map
      (fun p ↦ (originalReserveUnitInputReadout q θ hθ hθ1 p.1).2) =
      (Main.law : Measure (LegalMarkedOptimalInputScene q)).map Prod.snd := by
  have hm : Measurable (fun p : OriginalReserveUnitExperimentSpace q × TwoMarkedCloudSpace q ℝ ℝ ↦
      originalReserveUnitInputReadout q θ hθ hθ1 p.1) :=
    (measurable_originalReserveUnitInputReadout q θ hθ hθ1).comp measurable_fst
  change (X.fullLaw : Measure (OriginalReserveUnitExperimentSpace q × TwoMarkedCloudSpace q ℝ ℝ)).map
    (Prod.snd ∘ (fun p ↦ originalReserveUnitInputReadout q θ hθ hθ1 p.1)) = _
  rw [← Measure.map_map measurable_snd hm, X.fullLaw_unit_scene]
  exact originalReserveUnitInputLaw_map_input_eq_original hq Main Reserve hθ hθ1

/-- Every compact-window actual unit block-count pair has its true independent
Poisson(V alpha(S), V beta(T)) law under the same full original joining. -/
theorem hasLaw_unitBlockCount_pair (hq : 0 < q)
    {K : Set (Fin q → ℝ)} (hK : IsCompact K) {S T : Set ℝ}
    (hS : MeasurableSet S) (hT : MeasurableSet T) :
    HasLaw (fun p : OriginalReserveUnitExperimentSpace q × TwoMarkedCloudSpace q ℝ ℝ ↦
      (originalMainPhysicalBlockCount K S 0 (originalReserveUnitInputReadout q θ hθ hθ1 p.1),
        originalMainPhysicalBlockCount K T 1 (originalReserveUnitInputReadout q θ hθ hθ1 p.1)))
      ((poissonMeasure ((volume K).toNNReal * (α S).toNNReal)).prod
        (poissonMeasure ((volume K).toNNReal * (β T).toNNReal)))
      (X.fullLaw : Measure (OriginalReserveUnitExperimentSpace q × TwoMarkedCloudSpace q ℝ ℝ)) :=
  hasLaw_originalPhysicalBlockCountPair_of_inputLaw Main
    (X.fullLaw : Measure (OriginalReserveUnitExperimentSpace q × TwoMarkedCloudSpace q ℝ ℝ))
    (fun p : OriginalReserveUnitExperimentSpace q × TwoMarkedCloudSpace q ℝ ℝ ↦
      (originalReserveUnitInputReadout q θ hθ hθ1 p.1).2)
    (measurable_snd.comp ((measurable_originalReserveUnitInputReadout q θ hθ hθ1).comp measurable_fst))
    (X.fullLaw_colored_unit_input hq) hK hS hT

/-- Actual equal-mass unit blocks have the true L1 discrepancy and square-root
volume budget on this joining, retaining all bad-event correlations. -/
theorem unitBlock_discrepancy (hq : 0 < q)
    {K : Set (Fin q → ℝ)} (hK : IsCompact K) {S T : Set ℝ}
    (hS : MeasurableSet S) (hT : MeasurableSet T) (hbal : α S = β T) :
    Integrable (fun p : OriginalReserveUnitExperimentSpace q × TwoMarkedCloudSpace q ℝ ℝ ↦
      |(originalMainPhysicalBlockCount K S 0 (originalReserveUnitInputReadout q θ hθ hθ1 p.1) : ℝ) -
        (originalMainPhysicalBlockCount K T 1 (originalReserveUnitInputReadout q θ hθ hθ1 p.1) : ℝ)|)
      (X.fullLaw : Measure _) ∧
    (∫ p : OriginalReserveUnitExperimentSpace q × TwoMarkedCloudSpace q ℝ ℝ,
      |(originalMainPhysicalBlockCount K S 0 (originalReserveUnitInputReadout q θ hθ hθ1 p.1) : ℝ) -
        (originalMainPhysicalBlockCount K T 1 (originalReserveUnitInputReadout q θ hθ hθ1 p.1) : ℝ)|
      ∂(X.fullLaw : Measure _)) ≤ Real.sqrt (2 * volume.real K * α.real S) := by
  have hlaw := X.hasLaw_unitBlockCount_pair hq hK hS hT
  rw [← hbal] at hlaw
  have hm : Measurable (fun p : OriginalReserveUnitExperimentSpace q × TwoMarkedCloudSpace q ℝ ℝ ↦
      (originalMainPhysicalBlockCount K S 0 (originalReserveUnitInputReadout q θ hθ hθ1 p.1),
        originalMainPhysicalBlockCount K T 1 (originalReserveUnitInputReadout q θ hθ hθ1 p.1))) :=
    ((measurable_originalMainPhysicalBlockCount hK.measurableSet hS 0).prodMk
    (measurable_originalMainPhysicalBlockCount hK.measurableSet hT 1)).comp
    ((measurable_originalReserveUnitInputReadout q θ hθ hθ1).comp measurable_fst)
  have h := poissonPair_discrepancy_of_hasLaw _ _ hm _ hlaw
  simpa only [NNReal.coe_mul, ENNReal.coe_toNNReal_eq_toReal, measureReal_def, mul_assoc] using h

/-- The actual same-grid Hall block supplies equal law masses internally. -/
theorem clockSlabBlock_unit_discrepancy (hq : 0 < q)
    (G : OriginalStageClockGrid) (block : G.ClockSlabBlock α β) :
    let K := originalCenteredPhysicalCubeRegion b (2 * R)
    Integrable (fun p : OriginalReserveUnitExperimentSpace q × TwoMarkedCloudSpace q ℝ ℝ ↦
      |(originalMainPhysicalBlockCount K (G.sourceBlockCell α β block) 0
          (originalReserveUnitInputReadout q θ hθ hθ1 p.1) : ℝ) -
        (originalMainPhysicalBlockCount K (G.targetBlockCell α β block) 1
          (originalReserveUnitInputReadout q θ hθ hθ1 p.1) : ℝ)|) (X.fullLaw : Measure _) ∧
    (∫ p : OriginalReserveUnitExperimentSpace q × TwoMarkedCloudSpace q ℝ ℝ,
      |(originalMainPhysicalBlockCount K (G.sourceBlockCell α β block) 0
          (originalReserveUnitInputReadout q θ hθ hθ1 p.1) : ℝ) -
        (originalMainPhysicalBlockCount K (G.targetBlockCell α β block) 1
          (originalReserveUnitInputReadout q θ hθ hθ1 p.1) : ℝ)| ∂(X.fullLaw : Measure _)) ≤
      Real.sqrt (2 * volume.real K * α.real (G.sourceBlockCell α β block)) := by
  exact X.unitBlock_discrepancy hq (isCompact_originalStagePhysicalCube b _)
    (G.blockCells_measurable block).1 (G.blockCells_measurable block).2
    ((ENNReal.toReal_eq_toReal_iff' (measure_ne_top α _) (measure_ne_top β _)).mp
      (G.block_mass_balance block))

end OriginalReserveFullUnitInputExperiment
end OTSelector.Reconstruction
