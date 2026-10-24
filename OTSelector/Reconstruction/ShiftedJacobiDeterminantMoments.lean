import OTSelector.Reconstruction.ClosedJacobiConditionalMoments

/-!
# Determinant moments after changing the integration base

An arbitrary fixed matrix shift preserves the weighted determinant cancellation:
if `J T` extends continuously, then `J (D + T) = J D + J T` does as well.
This is the endpoint estimate needed when two actual graph charts have different
integration bases. It uses no high power moment of the compliance matrix.
-/

open Set MeasureTheory Matrix
open scoped Topology Matrix.Norms.Operator

namespace OTSelector.Reconstruction
open OTSelector.Geometry

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Continuous numerator and position extensions give both signed determinant
moments under the original Jacobi-weighted density. -/
theorem integrable_determinants_of_continuous_weighted_extension
    {J Q T : ℝ → Matrix n n ℝ} {a b c θ : ℝ}
    (hJ : ContinuousOn J (Icc a b)) (hQ : ContinuousOn Q (Icc a b))
    (hT : ContinuousOn T (Ioo a b)) (hQT : ∀ t ∈ Ioo a b, Q t = J t * T t)
    (hc : c ∈ Ioo a b)
    {ρ w : ℝ → ℝ} {R : ℝ} (hρ : Measurable ρ) (hw : ContinuousOn w (Icc a b))
    (hρ0 : ∀ t ∈ Ioo a b, 0 ≤ ρ t) (hρR : ∀ t ∈ Ioo a b, ρ t ≤ R)
    (hw0 : ∀ t ∈ Ioo a b, 0 ≤ w t) (hθ : 0 < θ)
    {μ : Measure ℝ}
    (hμ : μ = (volume.restrict (Ioo a b)).withDensity
      (fun t ↦ ENNReal.ofReal ((ρ t * w t / θ) * |(J t).det|))) :
    Integrable (fun t ↦ (1 + T t).det) μ ∧ Integrable (fun t ↦ (1 - T t).det) μ := by
  obtain ⟨M, hM⟩ := exists_weighted_det_cancellation_bound hJ hQ hQT
  have hM0 : 0 ≤ M :=
    (mul_nonneg (abs_nonneg _) (abs_nonneg _)).trans (hM c hc).1
  obtain ⟨W, hW⟩ := isCompact_Icc.bddAbove_image hw
  let d := fun t ↦ ρ t * w t / θ
  have hd0 : ∀ t ∈ Ioo a b, 0 ≤ d t :=
    fun t ht ↦ div_nonneg (mul_nonneg (hρ0 t ht) (hw0 t ht)) hθ.le
  have hdR : ∀ t ∈ Ioo a b, d t ≤ R * W / θ := by
    intro t ht
    apply div_le_div_of_nonneg_right _ hθ.le
    exact mul_le_mul (hρR t ht) (hW (mem_image_of_mem _ (Ioo_subset_Icc_self ht)))
      (hw0 t ht) ((hρ0 t ht).trans (hρR t ht))
  have hd : AEMeasurable d (volume.restrict (Ioo a b)) :=
    (hρ.aemeasurable.mul ((hw.mono Ioo_subset_Icc_self).aemeasurable
      measurableSet_Ioo)).div_const θ
  have hJdet : ContinuousOn (fun t ↦ |(J t).det|) (Ioo a b) :=
    (continuous_id.matrix_det.comp_continuousOn (hJ.mono Ioo_subset_Icc_self)).abs
  have hden : AEMeasurable (fun t ↦ d t * |(J t).det|)
      (volume.restrict (Ioo a b)) := hd.mul (hJdet.aemeasurable measurableSet_Ioo)
  have hbound (f : ℝ → ℝ) (hf : ContinuousOn f (Ioo a b))
      (hfb : ∀ t ∈ Ioo a b, |f t| * |(J t).det| ≤ M) : Integrable f μ := by
    rw [hμ]
    apply (integrable_withDensity_iff_integrable_smul₀' hden.ennreal_ofReal
      (ae_of_all _ fun _ ↦ ENNReal.ofReal_lt_top)).2
    apply (integrable_const ((R * W / θ) * M)).mono'
      (hden.ennreal_ofReal.ennreal_toReal.aestronglyMeasurable.smul
        (hf.aestronglyMeasurable measurableSet_Ioo))
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    change ‖(ENNReal.ofReal (d t * |(J t).det|)).toReal * f t‖ ≤ _
    rw [ENNReal.toReal_ofReal (mul_nonneg (hd0 t ht) (abs_nonneg _)), norm_mul,
      Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hd0 t ht) (abs_nonneg _)),
      Real.norm_eq_abs]
    calc
      (d t * |(J t).det|) * |f t| = d t * (|f t| * |(J t).det|) := by ring
      _ ≤ d t * M := mul_le_mul_of_nonneg_left (hfb t ht) (hd0 t ht)
      _ ≤ (R * W / θ) * M := mul_le_mul_of_nonneg_right (hdR t ht) hM0
  exact ⟨hbound _ (continuous_id.matrix_det.comp_continuousOn (continuousOn_const.add hT))
    (fun t ht ↦ (hM t ht).1),
    hbound _ (continuous_id.matrix_det.comp_continuousOn (continuousOn_const.sub hT))
    (fun t ht ↦ (hM t ht).2)⟩

/-- Changing the root by any finite matrix retains the determinant cancellation at
focal endpoints of the same actual closed Hamiltonian system. -/
theorem ClosedHamiltonianJacobiSystem.integrable_shifted_determinants
    {J P A B C : ℝ → Matrix n n ℝ} {a b c θ : ℝ}
    (H : ClosedHamiltonianJacobiSystem J P A B C a b)
    (hd : ∀ t ∈ Ioo a b, (J t).det ≠ 0) (hc : c ∈ Ioo a b) (D : Matrix n n ℝ)
    {ρ w : ℝ → ℝ} {R : ℝ} (hρ : Measurable ρ) (hw : ContinuousOn w (Icc a b))
    (hρ0 : ∀ t ∈ Ioo a b, 0 ≤ ρ t) (hρR : ∀ t ∈ Ioo a b, ρ t ≤ R)
    (hw0 : ∀ t ∈ Ioo a b, 0 ≤ w t) (hθ : 0 < θ)
    {μ : Measure ℝ}
    (hμ : μ = (volume.restrict (Ioo a b)).withDensity
      (fun t ↦ ENNReal.ofReal ((ρ t * w t / θ) * |(J t).det|))) :
    Integrable (fun t ↦ (1 + (D + jacobiCompliancePrimitive J C c t)).det) μ ∧
      Integrable (fun t ↦ (1 - (D + jacobiCompliancePrimitive J C c t)).det) μ := by
  have hJ := fun t (ht : t ∈ Ioo a b) ↦ H.position_derivative t (Ioo_subset_Icc_self ht)
  have hP := fun t (ht : t ∈ Ioo a b) ↦ H.momentum_derivative t (Ioo_subset_Icc_self ht)
  have hJcont : ContinuousOn J (Icc a b) :=
    fun t ht ↦ (H.position_derivative t ht).continuousAt.continuousWithinAt
  have hJdiff : DifferentiableOn ℝ J (Ioo a b) :=
    fun t ht ↦ (hJ t ht).differentiableAt.differentiableWithinAt
  have hT : ContinuousOn (jacobiCompliancePrimitive J C c) (Ioo a b) :=
    fun t ht ↦ (hasDerivAt_jacobiCompliancePrimitive hJdiff
      (H.continuous_C.mono Ioo_subset_Icc_self) hd hc ht).continuousAt.continuousWithinAt
  obtain ⟨Q, _, hQ, _, hQT, _⟩ := exists_continuous_integral_second_jacobi_extension
    hJ hP H.continuous_A H.continuous_B H.continuous_C
    (fun t ht ↦ H.symmetric_A t (Ioo_subset_Icc_self ht))
    (fun t ht ↦ H.symmetric_C t (Ioo_subset_Icc_self ht)) hd hc
    (H.wronskian c (Ioo_subset_Icc_self hc))
  apply integrable_determinants_of_continuous_weighted_extension hJcont
    ((hJcont.mul continuousOn_const).add hQ) (continuousOn_const.add hT)
    (Q := fun t ↦ J t * D + Q t) (c := c) ?_ hc hρ hw hρ0 hρR hw0 hθ hμ
  intro t ht
  simpa only [Pi.add_apply, Matrix.mul_add] using congrArg (J t * D + ·) (hQT ht)

end OTSelector.Reconstruction
