import OTSelector.Reconstruction.JacobiClockMeasureTransfer
import OTSelector.Geometry.FocalConditionalPowerMomentsGlobal

/-!
# Physical Jacobi densities in the actual graph time

The physical Jacobian is the absolute graph-clock velocity times the graph-position
determinant and a fixed normalization determinant. The time change cancels only its
velocity factor. The full-interval focal estimate then applies to the same original
conditional measure after undoing its potential-clock shift.
-/

open Set MeasureTheory Matrix LinearMap
open scoped Topology Matrix.Norms.Operator ENNReal

set_option backward.isDefEq.respectTransparency false

namespace OTSelector.Reconstruction

open OTSelector.Geometry

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The fixed normalization factor remains in the graph density after the exact
absolute-velocity cancellation. Only interval-local measurability is required. -/
theorem map_physical_jacobi_density
    {I : Set ℝ} (hI : MeasurableSet I) {s v : ℝ → ℝ}
    (hs : ∀ t ∈ I, HasDerivWithinAt s (v t) I t) (hinj : InjOn s I)
    {a b θ κ : ℝ} (himage : s '' I = Ioo a b)
    {ρ w : ℝ → ℝ} {J : ℝ → Matrix n n ℝ}
    (hρ : Measurable ρ) (hw : ContinuousOn w (Ioo a b))
    (hJ : ContinuousOn J (Ioo a b)) :
    ((volume.restrict I).withDensity (fun t ↦
      ENNReal.ofReal ((ρ (s t) * w (s t) / θ) *
        (|v t| * |(J (s t)).det| * κ)))).map s =
      (volume.restrict (Ioo a b)).withDensity
        (fun x ↦ ENNReal.ofReal ((ρ x * (κ * w x) / θ) * |(J x).det|)) := by
  classical
  let q : ℝ → ℝ≥0∞ := (Ioo a b).indicator
    (fun x ↦ ENNReal.ofReal ((ρ x * (κ * w x) / θ) * |(J x).det|))
  have hdet : ContinuousOn (fun x ↦ (J x).det) (Ioo a b) :=
    continuous_id.matrix_det.comp_continuousOn hJ
  have hwJ : ContinuousOn (fun x ↦ (κ * w x) * |(J x).det|) (Ioo a b) :=
    (continuousOn_const.mul hw).mul hdet.abs
  have hq : Measurable q := by
    have hm : Measurable ((Ioo a b).indicator
        (fun x ↦ (κ * w x) * |(J x).det|)) :=
      by simpa only [piecewise_eq_indicator] using
        hwJ.measurable_piecewise continuous_zero.continuousOn measurableSet_Ioo
    convert ((hρ.mul hm).div_const θ).ennreal_ofReal using 1
    ext x
    by_cases hx : x ∈ Ioo a b
    · simp only [q, Pi.mul_apply, indicator_of_mem hx]
      congr 1
      ring
    · simp [q, hx]
  have hden : (volume.restrict I).withDensity (fun t ↦
      ENNReal.ofReal ((ρ (s t) * w (s t) / θ) * (|v t| * |(J (s t)).det| * κ))) =
      (volume.restrict I).withDensity (fun t ↦ ENNReal.ofReal |v t| * q (s t)) := by
    apply withDensity_congr_ae
    filter_upwards [ae_restrict_mem hI] with t ht
    have hst : s t ∈ Ioo a b := himage ▸ mem_image_of_mem s ht
    simp only [q, indicator_of_mem hst]
    rw [← ENNReal.ofReal_mul (abs_nonneg (v t))]
    congr 1
    ring
  rw [hden, map_withDensity_abs_deriv_mul_comp hI hs hinj hq, himage]
  apply withDensity_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
  exact indicator_of_mem hx _

/-- Full-interval compliance moments hold under the original scalar law. The
physical density retains the actual nonlinear graph clock, its Jacobian, the fixed
normalization determinant and the original potential-clock offset. -/
theorem integrable_originalClock_jacobiCompliance_rpow
    {J P A B C : ℝ → Matrix n n ℝ} {a b c θ r κ u₀ : ℝ}
    (hJ : ∀ t ∈ Ioo a b, HasDerivAt J (B t * J t + C t * P t) t)
    (hP : ∀ t ∈ Ioo a b, HasDerivAt P (-A t * J t - (B t)ᵀ * P t) t)
    (hA : ContinuousOn A (Icc a b)) (hB : ContinuousOn B (Icc a b))
    (hC : ContinuousOn C (Icc a b))
    (hAsym : ∀ t ∈ Ioo a b, (A t)ᵀ = A t)
    (hCsym : ∀ t ∈ Ioo a b, (C t)ᵀ = C t)
    (hd : ∀ t ∈ Ioo a b, (J t).det ≠ 0) (hc : c ∈ Ioo a b)
    (hinit : (J c)ᵀ * P c = (P c)ᵀ * J c)
    (hJa : HasDerivWithinAt J (B a * J a + C a * P a) (Ici a) a)
    (hJb : HasDerivWithinAt J (B b * J b + C b * P b) (Iic b) b)
    (hWa : (J a)ᵀ * P a = (P a)ᵀ * J a)
    (hWb : (J b)ᵀ * P b = (P b)ᵀ * J b)
    (hphasea : ∀ v, J a *ᵥ v = 0 → P a *ᵥ v = 0 → v = 0)
    (hphaseb : ∀ v, J b *ᵥ v = 0 → P b *ᵥ v = 0 → v = 0)
    (hCa : (C a).PosDef) (hCb : (C b).PosDef)
    {ρ w : ℝ → ℝ} {R : ℝ} (hρ : Measurable ρ) (hw : ContinuousOn w (Icc a b))
    (hρ0 : ∀ t ∈ Ioo a b, 0 ≤ ρ t) (hρR : ∀ t ∈ Ioo a b, ρ t ≤ R)
    (hw0 : ∀ t ∈ Ioo a b, 0 ≤ w t) (hθ : 0 < θ) (hκ : 0 ≤ κ)
    {I : Set ℝ} (hI : MeasurableSet I) {s v : ℝ → ℝ}
    (hs : ∀ t ∈ I, HasDerivWithinAt s (v t) I t) (hinj : InjOn s I)
    (himage : s '' I = Ioo a b)
    {μ : Measure ℝ} [IsFiniteMeasure μ]
    (hμ : μ.map (fun x ↦ x - u₀) = (volume.restrict I).withDensity (fun t ↦
      ENNReal.ofReal ((ρ (s t) * w (s t) / θ) *
        (|v t| * |(J (s t)).det| * κ))))
    (hr0 : 0 < r) (hr : r < 2) :
    Integrable (fun x ↦ ‖jacobiCompliancePrimitive J C c (s (x - u₀))‖ ^ r) μ := by
  let μt := μ.map (fun x ↦ x - u₀)
  have hmap : μt.map s = (volume.restrict (Ioo a b)).withDensity
      (fun x ↦ ENNReal.ofReal ((ρ x * (κ * w x) / θ) * |(J x).det|)) := by
    rw [show μt = _ from hμ]
    exact map_physical_jacobi_density hI hs hinj himage hρ
      (hw.mono Ioo_subset_Icc_self) (fun t ht ↦ (hJ t ht).continuousAt.continuousWithinAt)
  have hi : Integrable (fun t ↦ ‖jacobiCompliancePrimitive J C c t‖ ^ r) (μt.map s) :=
    integrable_jacobiCompliance_rpow_of_hamiltonian_endpoints
      hJ hP hA hB hC hAsym hCsym hd hc hinit hJa hJb hWa hWb hphasea hphaseb hCa hCb
      hρ (continuousOn_const.mul hw) hρ0 hρR (fun t ht ↦ mul_nonneg hκ (hw0 t ht))
      hθ hmap hr0 hr
  have hsm : AEMeasurable s μt := by
    rw [show μt = _ from hμ]
    exact ((show ContinuousOn s I from fun t ht ↦
      (hs t ht).differentiableWithinAt.continuousWithinAt).aemeasurable hI).mono_ac
        (withDensity_absolutelyContinuous _ _)
  exact (hi.comp_aemeasurable hsm).comp_measurable (measurable_id.sub_const u₀)

end OTSelector.Reconstruction
