import OTSelector.Reconstruction.OriginalCoefficientLocalization
import Mathlib.Probability.Kernel.Composition.IntegralCompProd

/-!
# Uniform moment control after integrating the original root law

A common conditional moment bound integrates over the unchanged root measure.
A higher moment then controls all small removed events uniformly, even when the
conditional pairing kernel and removed event vary together.
-/

open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology ENNReal

noncomputable section
namespace OTSelector.Reconstruction

set_option backward.isDefEq.respectTransparency false

/-- A common conditional higher moment gives the same moment bound for the joint
root-pair law, with its original unnormalized root mass. -/
theorem integrable_compProd_norm_rpow_of_uniform_moment
    {Z X V : Type*} [MeasurableSpace Z] [MeasurableSpace X]
    [NormedAddCommGroup V] [MeasurableSpace V] [BorelSpace V]
    {lambda : Measure Z} [IsFiniteMeasure lambda]
    {k : Kernel Z X} [IsSFiniteKernel k] {f : Z × X → V} (hf : Measurable f)
    {r L : ℝ}
    (hints : ∀ᵐ z ∂lambda, Integrable (fun x ↦ ‖f (z, x)‖ ^ r) (k z))
    (hbound : ∀ᵐ z ∂lambda, (∫ x, ‖f (z, x)‖ ^ r ∂k z) ≤ L) :
    Integrable (fun q ↦ ‖f q‖ ^ r) (lambda ⊗ₘ k) ∧
      (∫ q, ‖f q‖ ^ r ∂(lambda ⊗ₘ k)) ≤ L * lambda.real univ := by
  have hm := (hf.norm.pow_const r).stronglyMeasurable
  have hbase := hm.integral_kernel_prod_right' (κ := k)
  have hn (q : Z × X) : 0 ≤ ‖f q‖ ^ r := Real.rpow_nonneg (norm_nonneg _) _
  have hbn (z : Z) : 0 ≤ ∫ x, ‖f (z, x)‖ ^ r ∂k z := integral_nonneg (fun x ↦ hn (z, x))
  have hbi : Integrable (fun z ↦ ∫ x, ‖f (z, x)‖ ^ r ∂k z) lambda :=
    (integrable_const L).mono' hbase.aestronglyMeasurable (by
      filter_upwards [hbound] with z hz
      simpa only [Real.norm_eq_abs, abs_of_nonneg (hbn z)] using hz)
  have hi : Integrable (fun q ↦ ‖f q‖ ^ r) (lambda ⊗ₘ k) := by
    apply (Measure.integrable_compProd_iff hm.aestronglyMeasurable).mpr
    refine ⟨hints, ?_⟩
    simpa only [Real.norm_eq_abs, abs_of_nonneg (hn _)] using hbi
  refine ⟨hi, ?_⟩
  rw [Measure.integral_compProd hi]
  simpa only [integral_const, smul_eq_mul, mul_comm L] using
    integral_mono_ae hbi (integrable_const L) hbound

/-- One moment upper bound gives a cutoff simultaneously for every finite measure
under consideration. The cutoff is independent of the choice of coupling. -/
theorem exists_uniform_norm_tail_of_rpow_bound
    {Ω V : Type*} [MeasurableSpace Ω] [NormedAddCommGroup V]
    [MeasurableSpace V] [BorelSpace V]
    {f : Ω → V} (hf : Measurable f) {r L ε : ℝ} (hr : 1 < r) (hε : 0 < ε) :
    ∃ R > 0, ∀ μ : Measure Ω, Integrable (fun x ↦ ‖f x‖ ^ r) μ →
      (∫ x, ‖f x‖ ^ r ∂μ) ≤ L →
      (∫ x in {x | R < ‖f x‖}, ‖f x‖ ∂μ) < ε := by
  have hlim : Tendsto (fun R : ℝ ↦ L / R ^ (r - 1)) atTop (𝓝 0) := by
    have hneg := (tendsto_rpow_neg_atTop (sub_pos.mpr hr)).const_mul L
    simp only [mul_zero] at hneg
    refine hneg.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR
    rw [Real.rpow_neg hR.le, div_eq_mul_inv]
  obtain ⟨R, hR, hsmall⟩ := ((eventually_gt_atTop (0 : ℝ)).and
    (hlim.eventually (gt_mem_nhds hε))).exists
  refine ⟨R, hR, fun μ hi hL ↦ ?_⟩
  exact ((integral_norm_tail_le_rpow hf hr hR hi).2.trans
    (div_le_div_of_nonneg_right hL (Real.rpow_nonneg hR.le _))).trans_lt hsmall

/-- Uniform higher moments control arbitrary small removed events for all finite
measures in the family, with one mass threshold chosen before the measure. -/
theorem exists_uniform_norm_small_sets_of_rpow_bound
    {Ω V : Type*} [MeasurableSpace Ω] [NormedAddCommGroup V] [SecondCountableTopology V]
    [MeasurableSpace V] [BorelSpace V]
    {f : Ω → V} (hf : Measurable f) {r L ε : ℝ} (hr : 1 < r) (hε : 0 < ε) :
    ∃ τ > 0, ∀ μ : Measure Ω, IsFiniteMeasure μ →
      Integrable (fun x ↦ ‖f x‖ ^ r) μ → (∫ x, ‖f x‖ ^ r ∂μ) ≤ L →
      ∀ s : Set Ω, MeasurableSet s → μ.real s ≤ τ → (∫ x in s, ‖f x‖ ∂μ) < ε := by
  obtain ⟨R, hR, htail⟩ := exists_uniform_norm_tail_of_rpow_bound hf hr (half_pos hε)
    (L := L)
  refine ⟨ε / (2 * R), by positivity, fun μ hfinite hi hL s hs hmass ↦ ?_⟩
  let : IsFiniteMeasure μ := hfinite
  have hnorm : Integrable (fun x ↦ ‖f x‖) μ := by
    have h := integrable_norm_rpow_of_le hf.aestronglyMeasurable
      (show (0 : ℝ) ≤ 1 by norm_num) (zero_lt_one.trans hr).le hr.le hi
    simpa only [Real.rpow_one] using h
  have hcut := setIntegral_norm_le_cutoff hf hnorm hR.le hs
  have hm : R * μ.real s ≤ ε / 2 := by
    calc
      R * μ.real s ≤ R * (ε / (2 * R)) := mul_le_mul_of_nonneg_left hmass hR.le
      _ = ε / 2 := by field_simp
  linarith only [hcut, hm, htail μ hi hL]

end OTSelector.Reconstruction
