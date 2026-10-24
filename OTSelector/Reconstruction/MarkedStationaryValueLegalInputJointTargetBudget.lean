import OTSelector.Reconstruction.MarkedStationaryValueLegalInputJointBudget
import OTSelector.Reconstruction.MarkedStationaryValueLegalOptimalTargetTail

/-! The same original target deficit and actual compact source escape pay target cutoffs. -/
open Set Function MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace
open scoped ENNReal NNReal CompactlySupported
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
local instance markedStationaryValueLegalInputJointTargetBudgetInputPolish (q : ℕ) : PolishSpace
    (LocalFiniteMeasure (LegalColoredInputPoint q)) := LocalFiniteMeasure.instPolishSpace
local instance markedStationaryValueLegalInputJointTargetBudgetPlanPolish (q : ℕ) : PolishSpace
    (LocalFiniteMeasure (LegalMarkedPhysicalEdge q)) := LocalFiniteMeasure.instPolishSpace

/-- This target readout retains color one and cuts off the actual opposite
source endpoint, with no reversal of the strict-clock legal graph. -/
def legalMarkedInputTargetCutoffDefect (q : ℕ)
    (f χ : C_c(LegalMarkedPhysicalPoint q, ℝ)) (s : LegalMarkedOptimalInputScene q) : ℝ :=
  LocalFiniteMeasure.testIntegral s.2 (cavityProductTest f (legalInputColorTest 1)) -
    LocalFiniteMeasure.testIntegral s.1.1 (cavityProductTest χ f)

theorem continuous_legalMarkedInputTargetCutoffDefect (q : ℕ)
    (f χ : C_c(LegalMarkedPhysicalPoint q, ℝ)) : Continuous (legalMarkedInputTargetCutoffDefect q f χ) :=
  ((LocalFiniteMeasure.continuous_testIntegral _).comp continuous_snd).sub
    ((LocalFiniteMeasure.continuous_testIntegral _).comp continuous_fst.fst)

theorem integral_legalMarkedRootedColoredInputMeasure_targetColor
    (q : ℕ) {L : ℝ} (hL : 0 < L) (f : C_c(LegalMarkedPhysicalPoint q, ℝ))
    (p : TwoMarkedCloudSpace q ℝ ℝ × (Fin q → ℝ)) :
    (∫ x, cavityProductTest f (legalInputColorTest 1) x ∂legalMarkedRootedColoredInputMeasure q L p) =
      legalMarkedRootedTargetInputTest q L f p.1 p.2 := by
  rw [integral_legalMarkedRootedColoredInputMeasure q hL]
  have h0 : (fun x ↦ cavityProductTest f (legalInputColorTest 1) (x, 0)) = fun _ ↦ 0 := by
    funext x
    change f x * (if (0 : Fin 2) = 1 then 1 else 0) = 0
    norm_num
  have h1 : (fun x ↦ cavityProductTest f (legalInputColorTest 1) (x, 1)) = f := by
    funext x
    change f x * (if (1 : Fin 2) = 1 then 1 else 0) = f x
    simp
  rw [h0, h1]
  simp only [legalMarkedRootedSourceInputTest, Finset.sum_const_zero, zero_add]

private theorem abs_integral_target_sub_product_le_tail
    (q : ℕ) (μ : Measure (LegalMarkedPhysicalEdge q)) [IsFiniteMeasure μ]
    (f χ : C_c(LegalMarkedPhysicalPoint q, ℝ))
    (hχ : ∀ x, χ x ∈ Icc 0 1) {T : Set (LegalMarkedPhysicalPoint q)}
    (hT : MeasurableSet T) (hχT : EqOn χ 1 T) :
    |(∫ e, f e.2 ∂μ) - ∫ e, cavityProductTest χ f e ∂μ| ≤
      ‖f.toBoundedContinuousFunction‖ * μ.real (Tᶜ ×ˢ tsupport f) := by
  let σ := μ.map Prod.swap
  have hfi : Integrable (fun e : LegalMarkedPhysicalEdge q ↦ f e.1) σ :=
    Integrable.of_bound (f.continuous.measurable.comp measurable_fst).aestronglyMeasurable
      ‖f.toBoundedContinuousFunction‖ (.of_forall (fun e ↦ f.toBoundedContinuousFunction.norm_coe_le_norm _))
  have htail := abs_integral_source_sub_product_le_tail σ f χ hfi hχ T hχT (measure_lt_top _ _)
  have heq : (fun e : LegalMarkedPhysicalEdge q ↦ cavityProductTest f χ (Prod.swap e)) =
      fun e ↦ cavityProductTest χ f e := by
    funext e
    exact mul_comm _ _
  have hset : Prod.swap ⁻¹' (tsupport f ×ˢ Tᶜ) = Tᶜ ×ˢ tsupport f := by
    ext e
    exact and_comm
  dsimp only [σ] at htail
  rw [integral_map (f := fun e : LegalMarkedPhysicalEdge q ↦ f e.1)
    measurable_swap.aemeasurable (f.continuous.comp continuous_fst).aestronglyMeasurable,
    integral_map (f := fun e : LegalMarkedPhysicalEdge q ↦ cavityProductTest f χ e)
      measurable_swap.aemeasurable (cavityProductTest f χ).continuous.aestronglyMeasurable,
    heq] at htail
  simpa only [Prod.swap, Measure.real, Measure.map_apply measurable_swap (f.hasCompactSupport.measurableSet.prod hT.compl), hset] using htail

/-- Target test loss is paid by the actual original unmatched targets and the
actual source escape, inside the same joint finite observation. -/
theorem ofReal_abs_legalMarkedInputTargetCutoffDefect_observation_le
    (q : ℕ) {L : ℝ} (hL : 0 < L)
    (kin : ℝ → ℝ → (Fin q → ℝ) → ℝ) (g : ℝ → ℝ → ℝ) (t : ℝ)
    (f χ : C_c(LegalMarkedPhysicalPoint q, ℝ))
    (hχ : ∀ x, χ x ∈ Icc 0 1) {T : Set (LegalMarkedPhysicalPoint q)}
    (hT : MeasurableSet T) (hχT : EqOn χ 1 T)
    (p : TwoMarkedCloudSpace q ℝ ℝ × (Fin q → ℝ)) :
    ENNReal.ofReal |legalMarkedInputTargetCutoffDefect q f χ
      (legalMarkedOptimalInputObservation q hL kin g t p)| ≤
      ENNReal.ofReal |legalMarkedRootedTargetTest q L kin g t f p.1 p.2 -
        legalMarkedRootedTargetInputTest q L f p.1 p.2| +
      ENNReal.ofReal ‖f.toBoundedContinuousFunction‖ *
        ((legalMarkedOptimalInputObservation q hL kin g t p).1.1 : Measure (LegalMarkedPhysicalEdge q))
          (Tᶜ ×ˢ tsupport f) := by
  let Γ := legalMarkedNormalizedOptimalPlan q L kin g t p.1
  have : IsFiniteMeasure Γ := isFiniteMeasure_legalMarkedNormalizedOptimalPlan q hL kin g t p.1
  let μ := physicalSceneRootedPlan Γ (legalMarkedCenteredCoordinate q L) Prod.snd (L ^ q) p.2
  have : IsFiniteMeasure μ := isFiniteMeasure_physicalSceneRootedPlan Γ _ _ _ _
  have htail := abs_integral_target_sub_product_le_tail q μ f χ hχ hT hχT
  have htread : (∫ e, f e.2 ∂μ) = legalMarkedRootedTargetTest q L kin g t f p.1 p.2 :=
    integral_actualRooted_legalMarkedNormalizedOptimalPlan_target q hL kin g t
      (h := fun x ↦ f x) f.continuous.measurable p.1 p.2
  rw [htread] at htail
  have htriangle : |legalMarkedRootedTargetInputTest q L f p.1 p.2 -
      ∫ e, cavityProductTest χ f e ∂μ| ≤
      |legalMarkedRootedTargetTest q L kin g t f p.1 p.2 -
        legalMarkedRootedTargetInputTest q L f p.1 p.2| +
      ‖f.toBoundedContinuousFunction‖ * μ.real (Tᶜ ×ˢ tsupport f) := by
    calc
      _ ≤ |legalMarkedRootedTargetInputTest q L f p.1 p.2 -
          legalMarkedRootedTargetTest q L kin g t f p.1 p.2| +
        |legalMarkedRootedTargetTest q L kin g t f p.1 p.2 -
          ∫ e, cavityProductTest χ f e ∂μ| := abs_sub_le _ _ _
      _ ≤ _ := add_le_add (by rw [abs_sub_comm]) htail
  change ENNReal.ofReal |(∫ x, cavityProductTest f (legalInputColorTest 1) x
    ∂legalMarkedRootedColoredInputMeasure q L p) - ∫ e, cavityProductTest χ f e ∂μ| ≤ _
  rw [integral_legalMarkedRootedColoredInputMeasure_targetColor q hL]
  have h := ENNReal.ofReal_le_ofReal htriangle
  rw [ENNReal.ofReal_add (abs_nonneg _) (mul_nonneg (norm_nonneg _) measureReal_nonneg),
    ENNReal.ofReal_mul (norm_nonneg _), ofReal_measureReal] at h
  exact h

end OTSelector.Reconstruction
