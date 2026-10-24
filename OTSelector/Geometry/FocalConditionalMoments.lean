import OTSelector.Geometry.JacobiEndpoint
import Mathlib.MeasureTheory.Integral.IntegrableOn

/-!
# Conditional determinant moments at finite focal endpoints

The actual Jacobi compliance integral has integrable signed determinant factors against
its Jacobi volume density, multiplied by any bounded nonnegative physical density.
The density may vanish or have holes. The determinant cancellation supplies the bound;
no finite compliance limit or endpoint rank assumption is required.

The normalized-law theorem consumes an exact measure identity. Identifying that density
with a particular original conditional law is the geometric disintegration producer's task.
`FocalConditionalMomentsPositive` identifies the piecewise signed determinant with
the spectral matrix absolute value using positivity of the actual length Hessian.
-/

open Set MeasureTheory Matrix
open scoped Topology Matrix.Norms.Operator

namespace OTSelector.Geometry

private theorem integrable_withDensity_of_weighted_norm_bound
    {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsFiniteMeasure μ]
    {d f : X → ℝ} {K : ℝ} (hd : AEMeasurable d μ)
    (hd0 : ∀ᵐ x ∂μ, 0 ≤ d x) (hf : AEStronglyMeasurable f μ)
    (hb : ∀ᵐ x ∂μ, d x * ‖f x‖ ≤ K) :
    Integrable f (μ.withDensity (fun x ↦ ENNReal.ofReal (d x))) := by
  apply (integrable_withDensity_iff_integrable_smul₀'
    hd.ennreal_ofReal (ae_of_all _ fun _ ↦ ENNReal.ofReal_lt_top)).2
  apply (integrable_const K).mono'
    (hd.ennreal_ofReal.ennreal_toReal.aestronglyMeasurable.smul hf)
  filter_upwards [hd0, hb] with x hx hxb
  change ‖(ENNReal.ofReal (d x)).toReal * f x‖ ≤ K
  simpa only [norm_mul, ENNReal.toReal_ofReal hx, Real.norm_eq_abs, abs_of_nonneg hx]
    using hxb

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Both signed determinant factors of the actual compliance primitive are integrable
against the Jacobi volume density times a bounded nonnegative physical density. -/
theorem integrable_jacobi_determinants_withDensity
    {J P A B C : ℝ → Matrix n n ℝ} {a b c : ℝ}
    (hJ : ∀ t ∈ Ioo a b, HasDerivAt J (B t * J t + C t * P t) t)
    (hP : ∀ t ∈ Ioo a b, HasDerivAt P (-A t * J t - (B t)ᵀ * P t) t)
    (hA : ContinuousOn A (Icc a b)) (hB : ContinuousOn B (Icc a b))
    (hC : ContinuousOn C (Icc a b))
    (hAsym : ∀ t ∈ Ioo a b, (A t)ᵀ = A t)
    (hCsym : ∀ t ∈ Ioo a b, (C t)ᵀ = C t)
    (hd : ∀ t ∈ Ioo a b, (J t).det ≠ 0) (hc : c ∈ Ioo a b)
    (hinit : (J c)ᵀ * P c = (P c)ᵀ * J c)
    {ρ : ℝ → ℝ} {R : ℝ}
    (hρ : AEMeasurable ρ (volume.restrict (Ioo a b)))
    (hρ0 : ∀ t ∈ Ioo a b, 0 ≤ ρ t) (hρR : ∀ t ∈ Ioo a b, ρ t ≤ R) :
    let μ := (volume.restrict (Ioo a b)).withDensity
      (fun t ↦ ENNReal.ofReal (ρ t * |(J t).det|))
    Integrable (fun t ↦ (1 + jacobiCompliancePrimitive J C c t).det) μ ∧
      Integrable (fun t ↦ (1 - jacobiCompliancePrimitive J C c t).det) μ := by
  have hJdiff : DifferentiableOn ℝ J (Ioo a b) :=
    fun t ht ↦ (hJ t ht).differentiableAt.differentiableWithinAt
  have hT : ContinuousOn (jacobiCompliancePrimitive J C c) (Ioo a b) :=
    fun t ht ↦ (hasDerivAt_jacobiCompliancePrimitive hJdiff
      (hC.mono Ioo_subset_Icc_self) hd hc ht).continuousAt.continuousWithinAt
  have hJdet : ContinuousOn (fun t ↦ |(J t).det|) (Ioo a b) :=
    ((continuous_id.matrix_det).comp_continuousOn hJdiff.continuousOn).abs
  have hden : AEMeasurable (fun t ↦ ρ t * |(J t).det|)
      (volume.restrict (Ioo a b)) :=
    hρ.mul (hJdet.aemeasurable measurableSet_Ioo)
  have hden0 : ∀ᵐ t ∂volume.restrict (Ioo a b), 0 ≤ ρ t * |(J t).det| := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    exact mul_nonneg (hρ0 t ht) (abs_nonneg _)
  obtain ⟨M, hM⟩ := exists_integral_weighted_det_bound
    hJ hP hA hB hC hAsym hCsym hd hc hinit
  have hM0 : 0 ≤ M :=
    (mul_nonneg (abs_nonneg _) (abs_nonneg _)).trans (hM c hc).1
  have hbound (f : ℝ → ℝ)
      (hf : ∀ t ∈ Ioo a b, |f t| * |(J t).det| ≤ M) :
      ∀ᵐ t ∂volume.restrict (Ioo a b),
        (ρ t * |(J t).det|) * ‖f t‖ ≤ R * M := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    calc
      (ρ t * |(J t).det|) * ‖f t‖ = ρ t * (|f t| * |(J t).det|) := by
        rw [Real.norm_eq_abs]
        ring
      _ ≤ ρ t * M := mul_le_mul_of_nonneg_left (hf t ht) (hρ0 t ht)
      _ ≤ R * M := mul_le_mul_of_nonneg_right (hρR t ht) hM0
  constructor
  · exact integrable_withDensity_of_weighted_norm_bound hden hden0
      (((continuous_id.matrix_det).comp_continuousOn
        (continuousOn_const.add hT)).aestronglyMeasurable measurableSet_Ioo)
      (hbound _ fun t ht ↦ (hM t ht).1)
  · exact integrable_withDensity_of_weighted_norm_bound hden hden0
      (((continuous_id.matrix_det).comp_continuousOn
        (continuousOn_const.sub hT)).aestronglyMeasurable measurableSet_Ioo)
      (hbound _ fun t ht ↦ (hM t ht).2)

/-- A normalized original conditional law inherits both determinant moments from its
exact physical-density, coordinate-volume and Jacobi-determinant formula. -/
theorem integrable_jacobi_determinants_of_conditional_density
    {J P A B C : ℝ → Matrix n n ℝ} {a b c θ : ℝ}
    (hJ : ∀ t ∈ Ioo a b, HasDerivAt J (B t * J t + C t * P t) t)
    (hP : ∀ t ∈ Ioo a b, HasDerivAt P (-A t * J t - (B t)ᵀ * P t) t)
    (hA : ContinuousOn A (Icc a b)) (hB : ContinuousOn B (Icc a b))
    (hC : ContinuousOn C (Icc a b))
    (hAsym : ∀ t ∈ Ioo a b, (A t)ᵀ = A t)
    (hCsym : ∀ t ∈ Ioo a b, (C t)ᵀ = C t)
    (hd : ∀ t ∈ Ioo a b, (J t).det ≠ 0) (hc : c ∈ Ioo a b)
    (hinit : (J c)ᵀ * P c = (P c)ᵀ * J c)
    {ρ w : ℝ → ℝ} {R : ℝ} (hρ : Measurable ρ) (hw : ContinuousOn w (Icc a b))
    (hρ0 : ∀ t ∈ Ioo a b, 0 ≤ ρ t) (hρR : ∀ t ∈ Ioo a b, ρ t ≤ R)
    (hw0 : ∀ t ∈ Ioo a b, 0 ≤ w t) (hθ : 0 < θ)
    {μ : Measure ℝ}
    (hμ : μ = (volume.restrict (Ioo a b)).withDensity
      (fun t ↦ ENNReal.ofReal ((ρ t * w t / θ) * |(J t).det|))) :
    Integrable (fun t ↦ (1 + jacobiCompliancePrimitive J C c t).det) μ ∧
      Integrable (fun t ↦ (1 - jacobiCompliancePrimitive J C c t).det) μ ∧
      Integrable (fun t ↦ if t ≤ c then (1 - jacobiCompliancePrimitive J C c t).det
        else (1 + jacobiCompliancePrimitive J C c t).det) μ := by
  classical
  obtain ⟨W, hW⟩ := isCompact_Icc.bddAbove_image hw
  have hweight0 : ∀ t ∈ Ioo a b, 0 ≤ ρ t * w t / θ :=
    fun t ht ↦ div_nonneg (mul_nonneg (hρ0 t ht) (hw0 t ht)) hθ.le
  have hweightR : ∀ t ∈ Ioo a b, ρ t * w t / θ ≤ R * W / θ := by
    intro t ht
    apply div_le_div_of_nonneg_right _ hθ.le
    exact mul_le_mul (hρR t ht) (hW (mem_image_of_mem _ (Ioo_subset_Icc_self ht)))
      (hw0 t ht) ((hρ0 t ht).trans (hρR t ht))
  have hweight : AEMeasurable (fun t ↦ ρ t * w t / θ)
      (volume.restrict (Ioo a b)) := (hρ.aemeasurable.mul
    ((hw.mono Ioo_subset_Icc_self).aemeasurable measurableSet_Ioo)).div_const θ
  obtain ⟨hplus, hminus⟩ := integrable_jacobi_determinants_withDensity
    hJ hP hA hB hC hAsym hCsym hd hc hinit hweight hweight0 hweightR
  rw [← hμ] at hplus hminus
  refine ⟨hplus, hminus, ?_⟩
  exact Integrable.piecewise measurableSet_Iic hminus.integrableOn hplus.integrableOn

end OTSelector.Geometry
