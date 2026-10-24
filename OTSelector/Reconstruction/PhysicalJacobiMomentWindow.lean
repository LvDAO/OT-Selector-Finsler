import OTSelector.Reconstruction.ClosedJacobiConditionalMoments
import OTSelector.Reconstruction.JacobiGraphDensity
import OTSelector.Reconstruction.CompliancePrimitiveRebasing

/-!
# A physical conditional window in one actual Jacobi frame

This intermediate data record retains the original conditional measure, the actual
nonlinear clock, its speed, and the fixed normalization. Its theorem derives a local
power moment from the Hamiltonian equations and physical density. Different endpoint
windows may use different graph charts while representing the same original kernel.
-/

open Set MeasureTheory Matrix
open scoped Topology Matrix.Norms.Operator Interval ENNReal

set_option backward.isDefEq.respectTransparency false

namespace OTSelector.Reconstruction
open OTSelector.Geometry

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Actual clock, matrix and density data on one whole physical interval.
The kernel is in the fixed original label basis, independently of the graph chart. -/
structure PhysicalJacobiMomentWindow (K : ℝ → Matrix n n ℝ)
    (μ : Measure ℝ) (l h : ℝ) where
  left_lt_right : l < h
  a : ℝ
  b : ℝ
  θ : ℝ
  κ : ℝ
  R : ℝ
  J : ℝ → Matrix n n ℝ
  P : ℝ → Matrix n n ℝ
  A : ℝ → Matrix n n ℝ
  B : ℝ → Matrix n n ℝ
  C : ℝ → Matrix n n ℝ
  s : ℝ → ℝ
  v : ℝ → ℝ
  ρ : ℝ → ℝ
  w : ℝ → ℝ
  system : ClosedHamiltonianJacobiSystem J P A B C a b
  interior_det : ∀ t ∈ Ioo a b, (J t).det ≠ 0
  clock_derivative : ∀ t ∈ Ioo l h, HasDerivAt s (v t) t
  clock_injective : InjOn s (Ioo l h)
  clock_image : s '' Ioo l h = Ioo a b
  speed_continuous : ContinuousOn v (Ioo l h)
  kernel_eq : ∀ t ∈ Ioo l h,
    K t = v t • ((J (s t))⁻¹ * C (s t) * (J (s t))⁻¹ᵀ)
  density_measurable : Measurable ρ
  weight_continuous : ContinuousOn w (Icc a b)
  density_nonneg : ∀ t ∈ Ioo a b, 0 ≤ ρ t
  density_bounded : ∀ t ∈ Ioo a b, ρ t ≤ R
  weight_nonneg : ∀ t ∈ Ioo a b, 0 ≤ w t
  normalizer_pos : 0 < θ
  normalization_nonneg : 0 ≤ κ
  conditional_density : μ.restrict (Ioo l h) =
    (volume.restrict (Ioo l h)).withDensity (fun t ↦
      ENNReal.ofReal ((ρ (s t) * w (s t) / θ) *
        (|v t| * |(J (s t)).det| * κ)))

/-- A window's moment is proved from its actual system and density; it is not a field
of the window record. Focal positions at either graph endpoint are allowed. -/
theorem PhysicalJacobiMomentWindow.integrableOn_primitive_rpow
    {K : ℝ → Matrix n n ℝ} {μ : Measure ℝ} [IsFiniteMeasure μ] {l h d r : ℝ}
    (W : PhysicalJacobiMomentWindow K μ l h)
    (hK : ContinuousOn K (Ioo l h)) (hd : d ∈ Ioo l h)
    (hr0 : 0 < r) (hr : r < 2) :
    IntegrableOn (fun t ↦ ‖∫ q in d..t, K q‖ ^ r) (Ioo l h) μ := by
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
  have hi := (W.system.conditional_moments W.interior_det (hmaps hd)
    W.density_measurable (continuousOn_const.mul W.weight_continuous)
    W.density_nonneg W.density_bounded
    (fun t ht ↦ mul_nonneg W.normalization_nonneg (W.weight_nonneg t ht))
    W.normalizer_pos hmap).2 r hr0 hr
  have hsm : AEMeasurable W.s (μ.restrict (Ioo l h)) :=
    (show ContinuousOn W.s (Ioo l h) from fun t ht ↦
      (W.clock_derivative t ht).continuousAt.continuousWithinAt).aemeasurable measurableSet_Ioo
  apply (hi.comp_aemeasurable hsm).congr
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
  have hseg := ordConnected_Ioo.uIcc_subset hd ht
  have heq := compliancePrimitive_eq_add_graphPrimitive hK hd hd ht
    hJdiff hC W.interior_det (fun q hq ↦ W.clock_derivative q (hseg hq))
    (W.speed_continuous.mono hseg) (hmaps.mono_left hseg)
    (fun q hq ↦ W.kernel_eq q (hseg hq))
  simp only [intervalIntegral.integral_same, zero_add] at heq
  rw [heq]
  rfl

/-- The original fixed-root primitive differs on this entire window by one finite
matrix constant. This transfers the proved moment without any root ordering. -/
theorem PhysicalJacobiMomentWindow.integrableOn_globalPrimitive_rpow
    {K : ℝ → Matrix n n ℝ} {μ : Measure ℝ} [IsFiniteMeasure μ]
    {l h a b c r : ℝ} (W : PhysicalJacobiMomentWindow K μ l h)
    (hK : ContinuousOn K (Ioo a b)) (hc : c ∈ Ioo a b)
    (hsub : Ioo l h ⊆ Ioo a b) (hr0 : 0 < r) (hr : r < 2) :
    IntegrableOn (fun t ↦ ‖∫ q in c..t, K q‖ ^ r) (Ioo l h) μ := by
  let d := (l + h) / 2
  have hd : d ∈ Ioo l h := ⟨by dsimp [d]; linarith [W.left_lt_right],
    by dsimp [d]; linarith [W.left_lt_right]⟩
  have hlocal := W.integrableOn_primitive_rpow (hK.mono hsub) hd hr0 hr
  have hm := (continuousOn_compliancePrimitive (hK.mono hsub) hd).aestronglyMeasurable
    (μ := μ) measurableSet_Ioo
  have hi := (integrable_norm_rpow_add_const_iff hm (∫ q in c..d, K q) hr0).mpr hlocal
  apply hi.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
  have hcd := (hK.mono (ordConnected_Ioo.uIcc_subset hc (hsub hd))).intervalIntegrable
    (μ := volume)
  have hdt := (hK.mono (ordConnected_Ioo.uIcc_subset (hsub hd) (hsub ht))).intervalIntegrable
    (μ := volume)
  rw [add_comm, intervalIntegral.integral_add_adjacent_intervals hcd hdt]

end OTSelector.Reconstruction
