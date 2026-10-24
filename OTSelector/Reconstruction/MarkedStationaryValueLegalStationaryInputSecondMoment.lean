import OTSelector.Reconstruction.MarkedStationaryValueLegalStationaryInputLawEquality
import OTSelector.Reconstruction.MarkedStationaryValueLegalInputWindowSecondMoment

/-! Actual compact-input second moments shared by all original matching laws. -/
open Set Function MeasureTheory Filter Topology TopologicalSpace
open scoped ENNReal NNReal CompactlySupported
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
local instance inputSecondMomentInputPolish (q : ℕ) : PolishSpace
    (LocalFiniteMeasure (LegalColoredInputPoint q)) := LocalFiniteMeasure.instPolishSpace
local instance inputSecondMomentPlanPolish (q : ℕ) : PolishSpace
    (LocalFiniteMeasure (LegalMarkedPhysicalEdge q)) := LocalFiniteMeasure.instPolishSpace

/-- Restriction on the actual support of a compact test retains its whole readout. -/
theorem testIntegral_inputRestriction_tsupport
    (q : ℕ) (μ : LocalFiniteMeasure (LegalColoredInputPoint q))
    (F : C_c(LegalColoredInputPoint q, ℝ)) :
    LocalFiniteMeasure.testIntegral (legalInputRestrictionLocal (tsupport F) μ) F =
      LocalFiniteMeasure.testIntegral μ F := by
  change (∫ x in tsupport F, F x ∂(μ : Measure (LegalColoredInputPoint q))) = _
  exact setIntegral_eq_integral_of_forall_compl_eq_zero
    (fun x hx ↦ image_eq_zero_of_notMem_tsupport hx)

/-- The genuine original matching's compact input test has a true second
moment, derived from its exact original finite Poisson window law. -/
theorem LegalWeightedStationaryPoissonMatching.integrable_sq_inputTest
    {q : ℕ} {α β : Measure ℝ} [IsProbabilityMeasure α] [IsProbabilityMeasure β]
    {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (M : LegalWeightedStationaryPoissonMatching q α β kin g)
    (F : C_c(LegalColoredInputPoint q, ℝ)) :
    Integrable (fun s ↦ LocalFiniteMeasure.testIntegral s.2 F ^ 2)
      (M.law : Measure (LegalMarkedOptimalInputScene q)) := by
  obtain ⟨S, hS, hlaw⟩ := M.map_inputRestrictionLocal_eq_originalPoisson F.hasCompactSupport
  let U := haarRootCube (Fin q) S
  have hUfin : volume U ≠ ∞ := isCompact_Icc.measure_ne_top
  have hUpos : volume U ≠ 0 := by
    rw [volume_haarRootCube (Fin q) hS.le, Fintype.card_fin]
    exact (ENNReal.ofReal_pos.mpr (pow_pos (by positivity : 0 < 2 * S) q)).ne'
  let κ := legalInputPoissonWindowLaw q U α β
  have hB := integrable_sq_originalPoisson_windowTest q hUfin hUpos α β F
  let read : LocalFiniteMeasure (LegalColoredInputPoint q) → ℝ :=
    fun μ ↦ LocalFiniteMeasure.testIntegral μ F ^ 2
  have hr : Measurable read := (LocalFiniteMeasure.continuous_testIntegral F).measurable.pow_const 2
  have hleft : Measurable (fun s : LegalMarkedOptimalInputScene q ↦
      legalInputRestrictionLocal (tsupport F) s.2) :=
    (measurable_legalInputRestrictionLocal F.hasCompactSupport.measurableSet).comp measurable_snd
  have hright : Measurable (fun b ↦
      legalInputRestrictionLocal (tsupport F) (legalInputTwoBlockLocal q b)) :=
    (measurable_legalInputRestrictionLocal F.hasCompactSupport.measurableSet).comp
      (measurable_legalInputTwoBlockLocal q)
  have hB' : Integrable (fun b ↦ read
      (legalInputRestrictionLocal (tsupport F) (legalInputTwoBlockLocal q b))) κ := by
    simpa only [read, testIntegral_inputRestriction_tsupport] using hB
  have hrightMap : Integrable read (κ.map (fun b ↦
      legalInputRestrictionLocal (tsupport F) (legalInputTwoBlockLocal q b))) :=
    (integrable_map_measure hr.aestronglyMeasurable hright.aemeasurable).mpr hB'
  have hleftMap : Integrable read ((M.law : Measure (LegalMarkedOptimalInputScene q)).map
      (fun s ↦ legalInputRestrictionLocal (tsupport F) s.2)) := by
    rw [hlaw]
    exact hrightMap
  have h := (integrable_map_measure hr.aestronglyMeasurable hleft.aemeasurable).mp hleftMap
  simpa only [Function.comp_def, read, testIntegral_inputRestriction_tsupport] using h

/-- The same immutable input law gives identical true second moments for every
pair of genuine original matchings, regardless of their selected edge plans. -/
theorem LegalWeightedStationaryPoissonMatching.integral_sq_inputTest_eq
    {q : ℕ} {α β : Measure ℝ}
    {kin₁ kin₂ : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g₁ g₂ : ℝ → ℝ → ℝ}
    (M : LegalWeightedStationaryPoissonMatching q α β kin₁ g₁)
    (N : LegalWeightedStationaryPoissonMatching q α β kin₂ g₂)
    (F : C_c(LegalColoredInputPoint q, ℝ)) :
    (∫ s, LocalFiniteMeasure.testIntegral s.2 F ^ 2
      ∂(M.law : Measure (LegalMarkedOptimalInputScene q))) =
      ∫ s, LocalFiniteMeasure.testIntegral s.2 F ^ 2
        ∂(N.law : Measure (LegalMarkedOptimalInputScene q)) := by
  have hr : Measurable (fun μ : LocalFiniteMeasure (LegalColoredInputPoint q) ↦
      LocalFiniteMeasure.testIntegral μ F ^ 2) :=
    (LocalFiniteMeasure.continuous_testIntegral F).measurable.pow_const 2
  rw [← integral_map measurable_snd.aemeasurable hr.aestronglyMeasurable,
    M.inputLaw_eq N, integral_map measurable_snd.aemeasurable hr.aestronglyMeasurable]

end OTSelector.Reconstruction
