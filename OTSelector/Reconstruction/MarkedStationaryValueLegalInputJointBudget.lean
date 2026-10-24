import OTSelector.Reconstruction.MarkedStationaryValueLegalInputJointDomination
import OTSelector.Reconstruction.MarkedStationaryValueLegalOptimalCompactEscape

/-!
# Original endpoint deficit and actual target escape pay compact-input defects

Every term belongs to the same actual joint observation. The complete original
input minus the retained compact source test loses only original unmatched rows
and target mass leaving the chosen genuine compact cutoff.
-/
open Set Function MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace
open scoped ENNReal NNReal CompactlySupported
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
local instance markedStationaryValueLegalInputJointBudgetLocalInputPolish (q : ℕ) : PolishSpace
    (LocalFiniteMeasure (LegalColoredInputPoint q)) := LocalFiniteMeasure.instPolishSpace
local instance markedStationaryValueLegalInputJointBudgetLocalPlanPolish (q : ℕ) : PolishSpace
    (LocalFiniteMeasure (LegalMarkedPhysicalEdge q)) := LocalFiniteMeasure.instPolishSpace

/-- The original input-color readout, compared with one genuine compact
matching test, is a continuous readout on the actual joint carrier. -/
def legalMarkedInputSourceCutoffDefect (q : ℕ)
    (f χ : C_c(LegalMarkedPhysicalPoint q, ℝ)) (s : LegalMarkedOptimalInputScene q) : ℝ :=
  LocalFiniteMeasure.testIntegral s.2 (cavityProductTest f (legalInputColorTest 0)) -
    LocalFiniteMeasure.testIntegral s.1.1 (cavityProductTest f χ)

theorem continuous_legalMarkedInputSourceCutoffDefect (q : ℕ)
    (f χ : C_c(LegalMarkedPhysicalPoint q, ℝ)) : Continuous (legalMarkedInputSourceCutoffDefect q f χ) :=
  ((LocalFiniteMeasure.continuous_testIntegral _).comp continuous_snd).sub
    ((LocalFiniteMeasure.continuous_testIntegral _).comp continuous_fst.fst)

/-- Source color readout keeps exactly every unchanged original source point. -/
theorem integral_legalMarkedRootedColoredInputMeasure_sourceColor
    (q : ℕ) {L : ℝ} (hL : 0 < L) (f : C_c(LegalMarkedPhysicalPoint q, ℝ))
    (p : TwoMarkedCloudSpace q ℝ ℝ × (Fin q → ℝ)) :
    (∫ x, cavityProductTest f (legalInputColorTest 0) x ∂legalMarkedRootedColoredInputMeasure q L p) =
      legalMarkedRootedSourceInputTest q L f p.1 p.2 := by
  rw [integral_legalMarkedRootedColoredInputMeasure q hL]
  have h0 : (fun x ↦ cavityProductTest f (legalInputColorTest 0) (x, 0)) = f := by
    funext x
    change f x * (if (0 : Fin 2) = 0 then 1 else 0) = f x
    simp
  have h1 : (fun x ↦ cavityProductTest f (legalInputColorTest 0) (x, 1)) = fun _ ↦ 0 := by
    funext x
    change f x * (if (1 : Fin 2) = 0 then 1 else 0) = 0
    norm_num
  rw [h0, h1]
  simp only [legalMarkedRootedTargetInputTest, Finset.sum_const_zero, add_zero]

/-- The true actual finite source-cutoff error has only its original unmatched
source test and its actual compact-target escape as costs. -/
theorem ofReal_abs_legalMarkedInputSourceCutoffDefect_observation_le
    (q : ℕ) {L : ℝ} (hL : 0 < L)
    (kin : ℝ → ℝ → (Fin q → ℝ) → ℝ) (g : ℝ → ℝ → ℝ) (t : ℝ)
    (f χ : C_c(LegalMarkedPhysicalPoint q, ℝ))
    (hχ : ∀ x, χ x ∈ Icc 0 1) (T : Set (LegalMarkedPhysicalPoint q)) (hχT : EqOn χ 1 T)
    (p : TwoMarkedCloudSpace q ℝ ℝ × (Fin q → ℝ)) :
    ENNReal.ofReal |legalMarkedInputSourceCutoffDefect q f χ
      (legalMarkedOptimalInputObservation q hL kin g t p)| ≤
      ENNReal.ofReal |legalMarkedRootedSourceTest q L kin g t f p.1 p.2 -
        legalMarkedRootedSourceInputTest q L f p.1 p.2| +
      ENNReal.ofReal ‖f.toBoundedContinuousFunction‖ *
        ((legalMarkedOptimalInputObservation q hL kin g t p).1.1 : Measure (LegalMarkedPhysicalEdge q))
          (tsupport f ×ˢ Tᶜ) := by
  let Γ := legalMarkedNormalizedOptimalPlan q L kin g t p.1
  have : IsFiniteMeasure Γ := isFiniteMeasure_legalMarkedNormalizedOptimalPlan q hL kin g t p.1
  let μ := physicalSceneRootedPlan Γ (legalMarkedCenteredCoordinate q L) Prod.snd (L ^ q) p.2
  have : IsFiniteMeasure μ := isFiniteMeasure_physicalSceneRootedPlan Γ _ _ _ _
  have hfi : Integrable (fun e : LegalMarkedPhysicalEdge q ↦ f e.1) μ :=
    Integrable.of_bound (f.continuous.measurable.comp measurable_fst).aestronglyMeasurable
      ‖f.toBoundedContinuousFunction‖ (.of_forall (fun e ↦ f.toBoundedContinuousFunction.norm_coe_le_norm _))
  have htail := abs_integral_source_sub_product_le_tail μ f χ hfi hχ T hχT (measure_lt_top _ _)
  have hsread : (∫ e, f e.1 ∂μ) = legalMarkedRootedSourceTest q L kin g t f p.1 p.2 :=
    integral_actualRooted_legalMarkedNormalizedOptimalPlan_source q hL kin g t
      (h := fun x ↦ f x) f.continuous.measurable p.1 p.2
  rw [hsread] at htail
  have htriangle : |legalMarkedRootedSourceInputTest q L f p.1 p.2 -
      ∫ e, cavityProductTest f χ e ∂μ| ≤
      |legalMarkedRootedSourceTest q L kin g t f p.1 p.2 -
        legalMarkedRootedSourceInputTest q L f p.1 p.2| +
      ‖f.toBoundedContinuousFunction‖ * μ.real (tsupport f ×ˢ Tᶜ) := by
    calc
      _ ≤ |legalMarkedRootedSourceInputTest q L f p.1 p.2 -
          legalMarkedRootedSourceTest q L kin g t f p.1 p.2| +
        |legalMarkedRootedSourceTest q L kin g t f p.1 p.2 -
          ∫ e, cavityProductTest f χ e ∂μ| := abs_sub_le _ _ _
      _ ≤ _ := add_le_add (by rw [abs_sub_comm]) htail
  change ENNReal.ofReal |(∫ x, cavityProductTest f (legalInputColorTest 0) x
    ∂legalMarkedRootedColoredInputMeasure q L p) - ∫ e, cavityProductTest f χ e ∂μ| ≤ _
  rw [integral_legalMarkedRootedColoredInputMeasure_sourceColor q hL]
  have h := ENNReal.ofReal_le_ofReal htriangle
  rw [ENNReal.ofReal_add (abs_nonneg _) (mul_nonneg (norm_nonneg _) measureReal_nonneg),
    ENNReal.ofReal_mul (norm_nonneg _), ofReal_measureReal] at h
  exact h

end OTSelector.Reconstruction
