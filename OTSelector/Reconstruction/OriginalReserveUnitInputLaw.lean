import OTSelector.Reconstruction.OriginalReserveUnitInputReadouts
import OTSelector.Reconstruction.MarkedStationaryValueLegalInputLaplaceFactorization

/-! The complete original unit-intensity input field retains its actual original Poisson law. -/
open Set Function MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators Classical CompactlySupported
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000
local instance originalReserveUnitInputLawInputPolish (q : ℕ) : PolishSpace
    (LocalFiniteMeasure (LegalColoredInputPoint q)) := LocalFiniteMeasure.instPolishSpace
local instance originalReserveUnitInputLawPlanPolish (q : ℕ) : PolishSpace
    (LocalFiniteMeasure (LegalMarkedPhysicalEdge q)) := LocalFiniteMeasure.instPolishSpace

/-- The actual complementary-dilation superposition has the same complete
colored original input random-measure law as the unit-intensity original main.
All marks and correlations inside that input are retained. -/
theorem originalReserveUnitInputLaw_map_input_eq_original
    {q : ℕ} (hq : 0 < q) {α β : Measure ℝ}
    [IsProbabilityMeasure α] [IsProbabilityMeasure β]
    {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (M N : LegalWeightedStationaryPoissonMatching q α β kin g)
    {θ : ℝ} (hθ : 0 < θ) (hθ1 : θ < 1) :
    (legalOriginalIntensityReserveLaw M N θ hθ hθ1 :
      Measure (LegalMarkedOptimalInputScene q)).map Prod.snd =
      (M.law : Measure (LegalMarkedOptimalInputScene q)).map Prod.snd := by
  let : IsProbabilityMeasure ((legalOriginalIntensityReserveLaw M N θ hθ hθ1 :
      Measure (LegalMarkedOptimalInputScene q)).map Prod.snd) :=
    Measure.isProbabilityMeasure_map measurable_snd.aemeasurable
  let : IsProbabilityMeasure ((M.law : Measure (LegalMarkedOptimalInputScene q)).map Prod.snd) :=
    Measure.isProbabilityMeasure_map measurable_snd.aemeasurable
  apply measure_eq_of_legalInput_compact_laplace
  intro F
  rw [integral_map measurable_snd.aemeasurable
      (legalInputMeasureLaplace F).continuous.aestronglyMeasurable,
    integral_map measurable_snd.aemeasurable
      (legalInputMeasureLaplace F).continuous.aestronglyMeasurable]
  change (∫ scene, legalMarkedInputSceneLaplace q F.1 F.2 scene
    ∂(legalOriginalIntensityReserveLaw M N θ hθ hθ1 : Measure (LegalMarkedOptimalInputScene q))) =
      ∫ scene, legalMarkedInputSceneLaplace q F.1 F.2 scene ∂(M.law : Measure _)
  rw [legalOriginalIntensityReserveLaw, integral_laplace_original_dilated_reserve,
    legalIntensityDilation_complementary_jacobians hq hθ hθ1, one_mul]
  exact (M.input_laplace_eq_global_exp F.1 F.2).symm

end OTSelector.Reconstruction
