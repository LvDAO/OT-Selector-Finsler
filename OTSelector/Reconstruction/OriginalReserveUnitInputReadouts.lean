import OTSelector.Reconstruction.OriginalLegalWeightedReserveCompletion
import OTSelector.Reconstruction.MarkedStationaryValueLegalReserveIntensity

/-! Read the actual complementary-dilation unit input and retained main from one original experiment. -/
open Set Function MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators Classical
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
local instance originalReserveUnitReadoutInputPolish (q : ℕ) : PolishSpace
    (LocalFiniteMeasure (LegalColoredInputPoint q)) := LocalFiniteMeasure.instPolishSpace
local instance originalReserveUnitReadoutPlanPolish (q : ℕ) : PolishSpace
    (LocalFiniteMeasure (LegalMarkedPhysicalEdge q)) := LocalFiniteMeasure.instPolishSpace

/-- The actual unit-intensity input keeps the first original matching plan
and adds the independently dilated whole reserve input without replacing either scene. -/
def originalReserveUnitInputReadout (q : ℕ) (θ : ℝ) (hθ : 0 < θ) (hθ1 : θ < 1)
    (p : LegalMarkedOptimalInputScene q ×
      (LegalMarkedOptimalInputScene q × TwoMarkedCloudSpace q ℝ ℝ)) : LegalMarkedOptimalInputScene q :=
  legalOriginalDilatedReserveScene q (legalIntensityDilation q (1 - θ))
    (legalIntensityDilation q θ) (legalIntensityDilation_pos q (sub_pos.mpr hθ1)).ne'
      (legalIntensityDilation_pos q hθ).ne' (p.1, p.2.1)

/-- The physical retained main and unchanged original cube sampler form the
actual iid-consumer marginal. The whole reserve identity witness is omitted. -/
def originalReserveMainSamplerReadout (q : ℕ) (θ : ℝ) (hθ1 : θ < 1)
    (p : LegalMarkedOptimalInputScene q ×
      (LegalMarkedOptimalInputScene q × TwoMarkedCloudSpace q ℝ ℝ)) :
    LegalMarkedOptimalInputScene q × TwoMarkedCloudSpace q ℝ ℝ :=
  (legalMarkedInputSceneDilation q (legalIntensityDilation q (1 - θ))
    (legalIntensityDilation_pos q (sub_pos.mpr hθ1)).ne' p.1, p.2.2)

theorem measurable_originalReserveUnitInputReadout (q : ℕ) (θ : ℝ)
    (hθ : 0 < θ) (hθ1 : θ < 1) :
    Measurable (originalReserveUnitInputReadout q θ hθ hθ1) :=
  (measurable_legalOriginalDilatedReserveScene q _ _ _ _).comp
    (measurable_fst.prodMk measurable_snd.fst)

theorem measurable_originalReserveMainSamplerReadout (q : ℕ) (θ : ℝ) (hθ1 : θ < 1) :
    Measurable (originalReserveMainSamplerReadout q θ hθ1) :=
  ((continuous_legalMarkedInputSceneDilation q _ _).measurable.comp measurable_fst).prodMk
    measurable_snd.snd

/-- The same actual unit input window is the sum of the retained main's whole
input window and the whole original dilated reserve window, exactly. -/
theorem originalReserveUnitInputReadout_window_decomposition (q : ℕ) (θ : ℝ)
    (hθ : 0 < θ) (hθ1 : θ < 1)
    (K : Set (Fin q → ℝ))
    (p : LegalMarkedOptimalInputScene q ×
      (LegalMarkedOptimalInputScene q × TwoMarkedCloudSpace q ℝ ℝ)) :
    ((originalReserveUnitInputReadout q θ hθ hθ1 p).2 :
      Measure (LegalColoredInputPoint q)).restrict ((Prod.fst ∘ Prod.fst) ⁻¹' K) =
      (((originalReserveMainSamplerReadout q θ hθ1 p).1).2 :
        Measure (LegalColoredInputPoint q)).restrict ((Prod.fst ∘ Prod.fst) ⁻¹' K) +
      ((legalMarkedInputSceneDilation q (legalIntensityDilation q θ)
        (legalIntensityDilation_pos q hθ).ne' p.2.1).2 :
          Measure (LegalColoredInputPoint q)).restrict ((Prod.fst ∘ Prod.fst) ⁻¹' K) :=
  Measure.restrict_add _ _ _

end OTSelector.Reconstruction
