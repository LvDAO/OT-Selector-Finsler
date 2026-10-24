import OTSelector.Reconstruction.PhysicalJacobiMomentWindow
import OTSelector.Reconstruction.ShiftedJacobiDeterminantMoments

/-!
# Fixed-root determinant moments in each original physical window

The arbitrary original root may lie outside the endpoint chart. Exact rebasing
adds its finite integral to the local graph primitive, and continuous Jacobi
numerators preserve both determinant cancellations under that shift.
-/

open Set MeasureTheory Matrix
open scoped Topology Matrix.Norms.Operator Interval ENNReal

namespace OTSelector.Reconstruction
open OTSelector.Geometry

set_option backward.isDefEq.respectTransparency false

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The same physical conditional window has both signed determinant moments for
an arbitrary root in the full original interval, including roots outside the window. -/
theorem PhysicalJacobiMomentWindow.integrableOn_globalPrimitive_determinants
    {K : ℝ → Matrix n n ℝ} {μ : Measure ℝ} [IsFiniteMeasure μ]
    {l h a b c : ℝ} (W : PhysicalJacobiMomentWindow K μ l h)
    (hK : ContinuousOn K (Ioo a b)) (hc : c ∈ Ioo a b)
    (hsub : Ioo l h ⊆ Ioo a b) :
    IntegrableOn (fun t ↦ (1 + ∫ q in c..t, K q).det) (Ioo l h) μ ∧
      IntegrableOn (fun t ↦ (1 - ∫ q in c..t, K q).det) (Ioo l h) μ := by
  let d := (l + h) / 2
  have hd : d ∈ Ioo l h := ⟨by dsimp [d]; linarith [W.left_lt_right],
    by dsimp [d]; linarith [W.left_lt_right]⟩
  have hJdiff : DifferentiableOn ℝ W.J (Ioo W.a W.b) :=
    fun t ht ↦ (W.system.position_derivative t (Ioo_subset_Icc_self ht)).differentiableAt.differentiableWithinAt
  have hC := W.system.continuous_C.mono Ioo_subset_Icc_self
  have hmaps : MapsTo W.s (Ioo l h) (Ioo W.a W.b) := by
    intro t ht
    rw [← W.clock_image]
    exact mem_image_of_mem _ ht
  have hmap : (μ.restrict (Ioo l h)).map W.s =
      (volume.restrict (Ioo W.a W.b)).withDensity (fun t ↦
        ENNReal.ofReal ((W.ρ t * (W.κ * W.w t) / W.θ) * |(W.J t).det|)) := by
    rw [W.conditional_density]
    exact map_physical_jacobi_density measurableSet_Ioo
      (fun t ht ↦ (W.clock_derivative t ht).hasDerivWithinAt)
      W.clock_injective W.clock_image W.density_measurable
      (W.weight_continuous.mono Ioo_subset_Icc_self) hJdiff.continuousOn
  have hi := W.system.integrable_shifted_determinants W.interior_det (hmaps hd)
    (∫ q in c..d, K q) W.density_measurable (continuousOn_const.mul W.weight_continuous)
    W.density_nonneg W.density_bounded
    (fun t ht ↦ mul_nonneg W.normalization_nonneg (W.weight_nonneg t ht))
    W.normalizer_pos hmap
  have hsm : AEMeasurable W.s (μ.restrict (Ioo l h)) :=
    (show ContinuousOn W.s (Ioo l h) from fun t ht ↦
      (W.clock_derivative t ht).continuousAt.continuousWithinAt).aemeasurable measurableSet_Ioo
  have heq : ∀ᵐ t ∂μ.restrict (Ioo l h), (∫ q in c..t, K q) =
      (∫ q in c..d, K q) + jacobiCompliancePrimitive W.J W.C (W.s d) (W.s t) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    have hseg := ordConnected_Ioo.uIcc_subset hd ht
    exact compliancePrimitive_eq_add_graphPrimitive hK hc (hsub hd) (hsub ht)
      hJdiff hC W.interior_det (fun q hq ↦ W.clock_derivative q (hseg hq))
      (W.speed_continuous.mono hseg) (hmaps.mono_left hseg)
      (fun q hq ↦ W.kernel_eq q (hseg hq))
  constructor
  · apply (hi.1.comp_aemeasurable hsm).congr
    filter_upwards [heq] with t ht
    simp only [Function.comp_def, ht]
  · apply (hi.2.comp_aemeasurable hsm).congr
    filter_upwards [heq] with t ht
    simp only [Function.comp_def, ht]

end OTSelector.Reconstruction
