import OTSelector.PointProcess.MatchingSceneMomentConvergence

/-!
# Continuous unbounded readouts under weak laws with actual second moments

Continuous pushforward reduces the readout to the existing real clipping
argument.  The second-moment bound also supplies limiting integrability;
uniform integrability is derived by that proof and is not an extra premise.
-/
open MeasureTheory Filter Set Topology
open scoped ENNReal
noncomputable section
namespace OTSelector.Probability
set_option backward.isDefEq.respectTransparency false

/-- A continuous second moment is retained by the same actual weak limit,
with both integrability and the unchanged real upper bound. -/
theorem integrable_sq_and_bound_of_probability_tendsto
    {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
    {μ : ℕ → ProbabilityMeasure X} {ν : ProbabilityMeasure X}
    (hlim : Tendsto μ atTop (𝓝 ν)) {F : X → ℝ} (hF : Continuous F)
    {C : ℝ} (hC : 0 ≤ C)
    (hsq : ∀ n, Integrable (fun x ↦ F x ^ 2) (μ n : Measure X))
    (hbound : ∀ n, (∫ x, F x ^ 2 ∂(μ n : Measure X)) ≤ C) :
    Integrable (fun x ↦ F x ^ 2) (ν : Measure X) ∧
      (∫ x, F x ^ 2 ∂(ν : Measure X)) ≤ C := by
  have hmoment : (∫⁻ x, ENNReal.ofReal (F x ^ 2) ∂(ν : Measure X)) ≤ ENNReal.ofReal C := by
    apply PointProcess.lintegral_ofReal_le_of_probability_tendsto hlim (hF.pow 2)
    filter_upwards with n
    change (∫⁻ x, ENNReal.ofReal (F x ^ 2) ∂(μ n : Measure X)) ≤ ENNReal.ofReal C
    rw [← ofReal_integral_eq_lintegral_ofReal (hsq n) (.of_forall fun x ↦ sq_nonneg (F x))]
    exact ENNReal.ofReal_le_ofReal (hbound n)
  have hνsq : Integrable (fun x ↦ F x ^ 2) (ν : Measure X) := by
    refine ⟨(hF.measurable.pow_const 2).aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (.of_forall fun x ↦ sq_nonneg (F x))]
    exact hmoment.trans_lt ENNReal.ofReal_lt_top
  refine ⟨hνsq, ?_⟩
  rw [← ofReal_integral_eq_lintegral_ofReal hνsq (.of_forall fun x ↦ sq_nonneg (F x))] at hmoment
  have hh := ENNReal.toReal_mono ENNReal.ofReal_ne_top hmoment
  simpa only [ENNReal.toReal_ofReal (integral_nonneg fun x ↦ sq_nonneg (F x)),
    ENNReal.toReal_ofReal hC] using hh

/-- The true uniform second moment makes an unbounded continuous readout
integrable at the limit and preserves its actual expectation. -/
theorem integrable_and_tendsto_integral_of_probability_tendsto_of_sq_bound
    {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
    {μ : ℕ → ProbabilityMeasure X} {ν : ProbabilityMeasure X}
    (hlim : Tendsto μ atTop (𝓝 ν)) {F : X → ℝ} (hF : Continuous F)
    {C : ℝ} (hC : 0 ≤ C)
    (hsq : ∀ n, Integrable (fun x ↦ F x ^ 2) (μ n : Measure X))
    (hbound : ∀ n, (∫ x, F x ^ 2 ∂(μ n : Measure X)) ≤ C) :
    Integrable (fun x ↦ F x ^ 2) (ν : Measure X) ∧
      (∫ x, F x ^ 2 ∂(ν : Measure X)) ≤ C ∧
      Integrable F (ν : Measure X) ∧
      (∀ n, Integrable F (μ n : Measure X)) ∧
      Tendsto (fun n ↦ ∫ x, F x ∂(μ n : Measure X)) atTop
        (𝓝 (∫ x, F x ∂(ν : Measure X))) := by
  obtain ⟨hνsq, hνbound⟩ :=
    integrable_sq_and_bound_of_probability_tendsto hlim hF hC hsq hbound
  have hI (P : ProbabilityMeasure X) (hP : Integrable (fun x ↦ F x ^ 2) (P : Measure X)) :
      Integrable F (P : Measure X) := by
    have hLp : MemLp F 2 (P : Measure X) :=
      (memLp_two_iff_integrable_sq hF.measurable.aestronglyMeasurable).mpr hP
    exact hLp.integrable (by norm_num)
  refine ⟨hνsq, hνbound, hI ν hνsq, fun n ↦ hI (μ n) (hsq n), ?_⟩
  have hm := ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous μ ν hlim hF
  have hi (n : ℕ) : Integrable (fun x : ℝ ↦ x ^ 2)
      ((μ n).map hF.measurable.aemeasurable : Measure ℝ) := by
    rw [ProbabilityMeasure.toMeasure_map]
    exact (integrable_map_measure (show Measurable (fun x : ℝ ↦ x ^ 2) from by fun_prop).aestronglyMeasurable
      hF.measurable.aemeasurable).mpr (hsq n)
  have hb (n : ℕ) : (∫ x : ℝ, x ^ 2
      ∂((μ n).map hF.measurable.aemeasurable : Measure ℝ)) ≤ C := by
    rw [ProbabilityMeasure.toMeasure_map, integral_map hF.measurable.aemeasurable
      (show Measurable (fun x : ℝ ↦ x ^ 2) from by fun_prop).aestronglyMeasurable]
    exact hbound n
  have ht := tendsto_integral_id_of_probability_tendsto_of_sq_bound hm hC hi hb
  have hread (P : ProbabilityMeasure X) :
      (∫ y : ℝ, y ∂(P.map hF.measurable.aemeasurable : Measure ℝ)) =
        ∫ x, F x ∂(P : Measure X) := by
    rw [ProbabilityMeasure.toMeasure_map]
    exact integral_map hF.measurable.aemeasurable
      (show Measurable (fun y : ℝ ↦ y) from measurable_id).aestronglyMeasurable
  simpa only [hread] using ht

end OTSelector.Probability
