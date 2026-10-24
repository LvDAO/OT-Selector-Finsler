import OTSelector.Geometry.JacobiComplianceReflection
import Mathlib.MeasureTheory.Function.JacobianOneDim

/-!
# Exact measure transfer through the actual graph clock

The original time density contains the absolute graph-clock velocity. A genuine
change of variables removes exactly that factor and retains every other weight,
including the fixed parameter normalization. Integrability transfers under this
same map, and a subsequent potential-clock shift keeps the original conditional law.
-/

open Set MeasureTheory
open scoped ENNReal

set_option backward.isDefEq.respectTransparency false

namespace OTSelector.Reconstruction

/-- A differentiable injective clock transports its Jacobian-weighted density
exactly, including clocks which are nonlinear or decrease along the old time. -/
theorem map_withDensity_abs_deriv_mul_comp
    {I : Set ℝ} (hI : MeasurableSet I) {s c : ℝ → ℝ}
    (hs : ∀ t ∈ I, HasDerivWithinAt s (c t) I t) (hinj : InjOn s I)
    {q : ℝ → ℝ≥0∞} (hq : Measurable q) :
    ((volume.restrict I).withDensity
      (fun t ↦ ENNReal.ofReal |c t| * q (s t))).map s =
        (volume.restrict (s '' I)).withDensity q := by
  have hsm : AEMeasurable s (volume.restrict I) :=
    (show ContinuousOn s I from fun t ht ↦
      (hs t ht).differentiableWithinAt.continuousWithinAt).aemeasurable hI
  have hcm : AEMeasurable (fun t ↦ ENNReal.ofReal |c t|) (volume.restrict I) := by
    simpa only [ContinuousLinearMap.det_toSpanSingleton] using
      aemeasurable_ofReal_abs_det_fderivWithin volume hI
        (fun t ht ↦ (hs t ht).hasFDerivWithinAt)
  have hqm : AEMeasurable (fun t ↦ ENNReal.ofReal |c t| * q (s t))
      (volume.restrict I) := hcm.mul (hq.comp_aemeasurable hsm)
  have hsw : AEMeasurable s ((volume.restrict I).withDensity
      (fun t ↦ ENNReal.ofReal |c t| * q (s t))) :=
    hsm.mono_ac (withDensity_absolutelyContinuous _ _)
  apply Measure.ext_of_lintegral _ _
  intro φ hφ
  have hφs : AEMeasurable (fun t ↦ φ (s t)) ((volume.restrict I).withDensity
      (fun t ↦ ENNReal.ofReal |c t| * q (s t))) := hφ.comp_aemeasurable hsw
  rw [lintegral_map' hφ.aemeasurable hsw,
    lintegral_withDensity_eq_lintegral_mul₀' hqm hφs,
    lintegral_withDensity_eq_lintegral_mul _ hq hφ]
  simpa only [Pi.mul_apply, mul_assoc] using
    (lintegral_image_eq_lintegral_abs_deriv_mul hI hs hinj (fun x ↦ q x * φ x)).symm

/-- Every integrable graph-clock observable pulls back to the same original-time law. -/
theorem integrable_comp_of_graph_clock_density
    {I : Set ℝ} (hI : MeasurableSet I) {s c : ℝ → ℝ}
    (hs : ∀ t ∈ I, HasDerivWithinAt s (c t) I t) (hinj : InjOn s I)
    {q : ℝ → ℝ≥0∞} (hq : Measurable q)
    {μ : Measure ℝ} (hμ : μ = (volume.restrict I).withDensity
      (fun t ↦ ENNReal.ofReal |c t| * q (s t)))
    {E : Type*} [NormedAddCommGroup E] {f : ℝ → E}
    (hf : Integrable f ((volume.restrict (s '' I)).withDensity q)) :
    Integrable (fun t ↦ f (s t)) μ := by
  have hmap : μ.map s = (volume.restrict (s '' I)).withDensity q := by
    rw [hμ]
    exact map_withDensity_abs_deriv_mul_comp hI hs hinj hq
  have hsm : AEMeasurable s μ := by
    rw [hμ]
    exact ((show ContinuousOn s I from fun t ht ↦
      (hs t ht).differentiableWithinAt.continuousWithinAt).aemeasurable hI).mono_ac
        (withDensity_absolutelyContinuous _ _)
  rw [← hmap] at hf
  exact hf.comp_aemeasurable hsm

/-- The original potential clock is an exact translation of the family time.
This equality transports any moment without changing its normalization. -/
theorem integrable_original_clock_iff
    {E : Type*} [NormedAddCommGroup E] (μ : Measure ℝ) (f : ℝ → E) (u₀ : ℝ) :
    Integrable (fun v ↦ f (v - u₀)) (μ.map (fun t ↦ t + u₀)) ↔ Integrable f μ := by
  rw [(measurableEmbedding_addRight u₀).integrable_map_iff]
  simp only [Function.comp_def, add_sub_cancel_right]

end OTSelector.Reconstruction
