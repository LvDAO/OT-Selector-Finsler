import OTSelector.Probability.ContinuousReadoutSecondMoment
import OTSelector.Reconstruction.MarkedStationaryValueLegalStationaryInputSecondMoment
import OTSelector.Reconstruction.MarkedStationaryValueLegalStationaryReadoutDomination

/-!
# Actual original edge readout convergence with no supplied moment oracle

The compact edge test chooses its immutable input majorant before any matching.
The exact original Poisson window law supplies a true finite second moment,
and the common full input law makes that bound uniform over all competitors.
-/
open Set Function MeasureTheory Filter Topology TopologicalSpace
open scoped ENNReal NNReal CompactlySupported
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
local instance edgeReadoutSecondMomentInputPolish (q : ℕ) : PolishSpace
    (LocalFiniteMeasure (LegalColoredInputPoint q)) := LocalFiniteMeasure.instPolishSpace
local instance edgeReadoutSecondMomentPlanPolish (q : ℕ) : PolishSpace
    (LocalFiniteMeasure (LegalMarkedPhysicalEdge q)) := LocalFiniteMeasure.instPolishSpace

/-- One genuine reference matching internally supplies a true uniform second
moment for the same compact edge readout under every original competitor. -/
theorem exists_uniform_original_edgeTest_sq_bound
    {q : ℕ} {α β : Measure ℝ} [IsProbabilityMeasure α] [IsProbabilityMeasure β]
    {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (M₀ : LegalWeightedStationaryPoissonMatching q α β kin g)
    (H : C_c(LegalMarkedPhysicalEdge q, ℝ)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ M : LegalWeightedStationaryPoissonMatching q α β kin g,
      Integrable (fun s ↦ LocalFiniteMeasure.testIntegral s.1.1 H ^ 2)
        (M.law : Measure (LegalMarkedOptimalInputScene q)) ∧
      (∫ s, LocalFiniteMeasure.testIntegral s.1.1 H ^ 2
        ∂(M.law : Measure (LegalMarkedOptimalInputScene q))) ≤ C := by
  obtain ⟨η, hη, hdom⟩ := exists_original_edgeTest_input_majorant q H
  let B := ‖H.toBoundedContinuousFunction‖
  let C := B ^ 2 * ∫ s, LocalFiniteMeasure.testIntegral s.2 η ^ 2
    ∂(M₀.law : Measure (LegalMarkedOptimalInputScene q))
  have hC : 0 ≤ C := mul_nonneg (sq_nonneg _) (integral_nonneg fun s ↦ sq_nonneg _)
  refine ⟨C, hC, ?_⟩
  intro M
  have hY := M.integrable_sq_inputTest η
  have hD := hY.const_mul (B ^ 2)
  have hpoint : ∀ᵐ s ∂(M.law : Measure (LegalMarkedOptimalInputScene q)),
      LocalFiniteMeasure.testIntegral s.1.1 H ^ 2 ≤
        B ^ 2 * LocalFiniteMeasure.testIntegral s.2 η ^ 2 := by
    filter_upwards [M.full_matching] with s hs
    have hn : 0 ≤ LocalFiniteMeasure.testIntegral s.2 η := integral_nonneg hη
    have hb : 0 ≤ B := norm_nonneg _
    have h := (sq_le_sq₀ (abs_nonneg _) (mul_nonneg hb hn)).mpr (hdom s hs)
    simpa only [sq_abs, mul_pow] using h
  have hm : Measurable (fun s : LegalMarkedOptimalInputScene q ↦
      LocalFiniteMeasure.testIntegral s.1.1 H ^ 2) :=
    ((LocalFiniteMeasure.continuous_testIntegral H).comp continuous_fst.fst).measurable.pow_const 2
  have hI : Integrable (fun s ↦ LocalFiniteMeasure.testIntegral s.1.1 H ^ 2)
      (M.law : Measure (LegalMarkedOptimalInputScene q)) := by
    apply hD.mono' hm.aestronglyMeasurable
    filter_upwards [hpoint] with s hs
    change |LocalFiniteMeasure.testIntegral s.1.1 H ^ 2| ≤
      B ^ 2 * LocalFiniteMeasure.testIntegral s.2 η ^ 2
    rw [abs_of_nonneg (sq_nonneg _)]
    exact hs
  refine ⟨hI, ?_⟩
  have h := integral_mono_ae hI hD hpoint
  rw [integral_const_mul, M.integral_sq_inputTest_eq M₀ η] at h
  exact h

/-- Actual continuous compact edge observations preserve expectations through
weak limits of genuine original matching laws. All second moments and limiting
integrability are produced internally from the unchanged Poisson input. -/
theorem integrable_and_tendsto_original_stationary_edgeTest_integral
    {q : ℕ} {α β : Measure ℝ} [IsProbabilityMeasure α] [IsProbabilityMeasure β]
    {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (M : ℕ → LegalWeightedStationaryPoissonMatching q α β kin g)
    {Q : ProbabilityMeasure (LegalMarkedOptimalInputScene q)}
    (hweak : Tendsto (fun n ↦ (M n).law) atTop (𝓝 Q))
    (H : C_c(LegalMarkedPhysicalEdge q, ℝ)) :
    Integrable (fun s ↦ LocalFiniteMeasure.testIntegral s.1.1 H ^ 2)
        (Q : Measure (LegalMarkedOptimalInputScene q)) ∧
      Integrable (fun s ↦ LocalFiniteMeasure.testIntegral s.1.1 H)
        (Q : Measure (LegalMarkedOptimalInputScene q)) ∧
      (∀ n, Integrable (fun s ↦ LocalFiniteMeasure.testIntegral s.1.1 H)
        ((M n).law : Measure (LegalMarkedOptimalInputScene q))) ∧
      Tendsto (fun n ↦ ∫ s, LocalFiniteMeasure.testIntegral s.1.1 H
        ∂((M n).law : Measure (LegalMarkedOptimalInputScene q))) atTop
        (𝓝 (∫ s, LocalFiniteMeasure.testIntegral s.1.1 H
          ∂(Q : Measure (LegalMarkedOptimalInputScene q)))) := by
  obtain ⟨C, hC, hbound⟩ := exists_uniform_original_edgeTest_sq_bound (M 0) H
  have h := integrable_and_tendsto_integral_of_probability_tendsto_of_sq_bound hweak
    ((LocalFiniteMeasure.continuous_testIntegral H).comp continuous_fst.fst) hC
    (fun n ↦ (hbound (M n)).1) (fun n ↦ (hbound (M n)).2)
  exact ⟨h.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩

end OTSelector.Reconstruction
