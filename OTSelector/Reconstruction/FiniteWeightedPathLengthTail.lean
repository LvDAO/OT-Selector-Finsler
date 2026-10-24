import OTSelector.Reconstruction.OriginalPathLengthTail
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! # Finite weighted path readouts have vanishing long-path tails -/
open Set Function Filter MeasureTheory
open scoped ENNReal Topology
noncomputable section
namespace OTSelector.Reconstruction
set_option maxHeartbeats 1600000

/-- A finite actual weighted integral has a vanishing tail in every measurable
real path readout. No moment of that readout is needed. -/
theorem tendsto_lintegral_weighted_real_readout_tail
    {X : Type*} [MeasurableSpace X] (μ : Measure X) {weight : X → ℝ≥0∞}
    (hfinite : (∫⁻ x, weight x ∂μ) ≠ ∞) {length : X → ℝ} (hlength : Measurable length) :
    Tendsto (fun R : ℝ ↦ ∫⁻ x, if R < length x then weight x else 0 ∂μ) atTop (𝓝 0) := by
  have : IsFiniteMeasure (μ.withDensity weight) := isFiniteMeasure_withDensity hfinite
  have ht := tendsto_measure_real_readout_gt_atTop (μ.withDensity weight) hlength
  convert ht using 1
  ext R
  rw [withDensity_apply weight (measurableSet_lt measurable_const hlength),
    ← lintegral_indicator (measurableSet_lt measurable_const hlength)]
  rfl

/-- The square of every dominated real tail is genuinely integrable and its
second moment vanishes on the same probability space. The event may depend
arbitrarily on the entire original scene. -/
theorem integrable_sq_and_tendsto_integral_sq_of_nonnegative_tail
    {X : Type*} [MeasurableSpace X] (μ : Measure X)
    {full : X → ℝ≥0∞} {tail : ℝ → X → ℝ≥0∞}
    (htail : ∀ R, Measurable (tail R))
    (hfinite : ∀ᵐ x ∂μ, full x ≠ ∞)
    (hfullI : Integrable (fun x ↦ (full x).toReal ^ 2) μ)
    (hdom : ∀ R x, tail R x ≤ full x)
    (hlim : ∀ᵐ x ∂μ, Tendsto (fun R ↦ tail R x) atTop (𝓝 0)) :
    (∀ R, Integrable (fun x ↦ (tail R x).toReal ^ 2) μ) ∧
      Tendsto (fun R : ℝ ↦ ∫ x, (tail R x).toReal ^ 2 ∂μ) atTop (𝓝 0) := by
  have hbound (R : ℝ) : ∀ᵐ x ∂μ, ‖(tail R x).toReal ^ 2‖ ≤ (full x).toReal ^ 2 := by
    filter_upwards [hfinite] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact pow_le_pow_left₀ ENNReal.toReal_nonneg (ENNReal.toReal_mono hx (hdom R x)) 2
  refine ⟨fun R ↦ hfullI.mono' ((htail R).ennreal_toReal.pow_const 2).aestronglyMeasurable (hbound R), ?_⟩
  have hconverge : ∀ᵐ x ∂μ, Tendsto (fun R ↦ (tail R x).toReal ^ 2) atTop (𝓝 (0 : ℝ)) := by
    filter_upwards [hlim] with x hx
    simpa using (((ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hx).pow 2)
  simpa using tendsto_integral_filter_of_dominated_convergence
    (bound := fun x ↦ (full x).toReal ^ 2)
    (Eventually.of_forall fun R ↦ ((htail R).ennreal_toReal.pow_const 2).aestronglyMeasurable)
    (Eventually.of_forall hbound) hfullI hconverge

end OTSelector.Reconstruction
