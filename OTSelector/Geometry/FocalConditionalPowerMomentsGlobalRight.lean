import OTSelector.Geometry.FocalConditionalPowerMoments
import OTSelector.Geometry.JacobiComplianceReflection

/-!
# Right-end power moments of the original Jacobi conditional law

The actual reflected Hamiltonian system and the pushforward of the same conditional
measure supply the left-end moment theorem. Reflection then transfers its conclusion
back to the original time coordinate, including the sign of the actual primitive.
-/

open Set MeasureTheory Matrix LinearMap
open scoped Topology Matrix.Norms.Operator ENNReal

set_option backward.isDefEq.respectTransparency false

namespace OTSelector.Geometry

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- A regular right endpoint gives all local moments below its nullity plus one
for the original compliance primitive and original conditional measure. -/
theorem exists_integrableOn_jacobiCompliance_rpow_near_regular_right_endpoint
    {J P A B C : ℝ → Matrix n n ℝ} {a b c θ r : ℝ} {D : Matrix n n ℝ}
    (hJ : ∀ t ∈ Ioo a b, HasDerivAt J (B t * J t + C t * P t) t)
    (hP : ∀ t ∈ Ioo a b, HasDerivAt P (-A t * J t - (B t)ᵀ * P t) t)
    (hA : ContinuousOn A (Icc a b)) (hB : ContinuousOn B (Icc a b))
    (hC : ContinuousOn C (Icc a b))
    (hAsym : ∀ t ∈ Ioo a b, (A t)ᵀ = A t)
    (hCsym : ∀ t ∈ Ioo a b, (C t)ᵀ = C t)
    (hd : ∀ t ∈ Ioo a b, (J t).det ≠ 0) (hc : c ∈ Ioo a b)
    (hinit : (J c)ᵀ * P c = (P c)ᵀ * J c)
    (hJb : HasDerivWithinAt J D (Iic b) b)
    (hcross : ∀ v, J b *ᵥ v = 0 →
      D *ᵥ v ∈ LinearMap.range (J b).mulVecLin → v = 0)
    {ρ w : ℝ → ℝ} {R : ℝ} (hρ : Measurable ρ) (hw : ContinuousOn w (Icc a b))
    (hρ0 : ∀ t ∈ Ioo a b, 0 ≤ ρ t) (hρR : ∀ t ∈ Ioo a b, ρ t ≤ R)
    (hw0 : ∀ t ∈ Ioo a b, 0 ≤ w t) (hθ : 0 < θ)
    {μ : Measure ℝ}
    (hμ : μ = (volume.restrict (Ioo a b)).withDensity
      (fun t ↦ ENNReal.ofReal ((ρ t * w t / θ) * |(J t).det|)))
    (hr0 : 0 < r) (hr : r < (Module.finrank ℝ (ker (J b).mulVecLin) : ℝ) + 1) :
    ∃ ε : ℝ, 0 < ε ∧ ε < b - a ∧
      IntegrableOn (fun t ↦ ‖jacobiCompliancePrimitive J C c t‖ ^ r) (Ioo (b - ε) b) μ := by
  have hmap : MapsTo (fun t : ℝ ↦ b - t) (Icc 0 (b - a)) (Icc a b) := by
    intro t ht
    constructor <;> linarith [ht.1, ht.2]
  have hmapi : MapsTo (fun t : ℝ ↦ b - t) (Ioo 0 (b - a)) (Ioo a b) := by
    intro t ht
    constructor <;> linarith [ht.1, ht.2]
  have hcomp : ContinuousOn (fun t : ℝ ↦ b - t) (Icc 0 (b - a)) := by fun_prop
  have hArev := hA.comp hcomp hmap
  have hBrev := (hB.comp hcomp hmap).neg
  have hCrev := hC.comp hcomp hmap
  have hcrev : b - c ∈ Ioo 0 (b - a) := by
    constructor <;> linarith [hc.1, hc.2]
  have hinitrev : (J (b - (b - c)))ᵀ * (-P (b - (b - c))) =
      (-P (b - (b - c)))ᵀ * J (b - (b - c)) := by
    simpa only [sub_sub_cancel, Matrix.mul_neg, Matrix.transpose_neg, Matrix.neg_mul]
      using congrArg Neg.neg hinit
  have hcrossrev : ∀ v, J (b - 0) *ᵥ v = 0 →
      (-D) *ᵥ v ∈ LinearMap.range (J (b - 0)).mulVecLin → v = 0 := by
    simpa only [sub_zero] using matrix_crossing_kernel_condition_neg hcross
  have hμrev : μ.map (fun t ↦ b - t) =
      (volume.restrict (Ioo 0 (b - a))).withDensity (fun s ↦
        ENNReal.ofReal (((ρ (b - s)) * (w (b - s)) / θ) * |(J (b - s)).det|)) := by
    rw [hμ, map_reflect_interval_density]
  have hrrev : r < (Module.finrank ℝ (ker (J (b - 0)).mulVecLin) : ℝ) + 1 := by
    rw [sub_zero]
    exact hr
  obtain ⟨ε, hε, hεab, hmoment⟩ :=
    exists_integrableOn_jacobiCompliance_rpow_near_regular_endpoint
      (fun s hs ↦ (hamiltonian_system_reflect hJ hP hs).1)
      (fun s hs ↦ (hamiltonian_system_reflect hJ hP hs).2)
      hArev hBrev hCrev
      (fun s hs ↦ hAsym _ (hmapi hs)) (fun s hs ↦ hCsym _ (hmapi hs))
      (fun s hs ↦ hd _ (hmapi hs)) hcrev hinitrev
      (hasDerivWithinAt_right_inward_parameter hJb) hcrossrev
      (hρ.comp (measurable_const.sub measurable_id)) (hw.comp hcomp hmap)
      (fun s hs ↦ hρ0 _ (hmapi hs)) (fun s hs ↦ hρR _ (hmapi hs))
      (fun s hs ↦ hw0 _ (hmapi hs)) hθ hμrev hr0 hrrev
  refine ⟨ε, hε, hεab, ?_⟩
  apply (integrableOn_reflected_rpow_iff (jacobiCompliancePrimitive J C c) μ b ε r).1
  simpa only [jacobiCompliancePrimitive_reflect, norm_neg] using hmoment

end OTSelector.Geometry
