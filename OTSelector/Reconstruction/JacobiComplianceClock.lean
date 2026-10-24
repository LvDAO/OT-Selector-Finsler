import OTSelector.Reconstruction.JacobiClockMeasureTransfer
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-!
# The same compliance integral under a nonlinear clock

The actual Hamiltonian coefficients acquire the signed clock velocity under
reparameterization. Substitution in the matrix-valued interval integral identifies
the resulting compliance with the original graph-time primitive, including its base.
-/

open Set MeasureTheory Matrix
open scoped Topology Matrix.Norms.Operator Interval

set_option backward.isDefEq.respectTransparency false

namespace OTSelector.Reconstruction

open OTSelector.Geometry

variable {n : Type*} [Fintype n] [DecidableEq n]

omit [DecidableEq n] in
/-- Reparameterizing the actual Hamiltonian system scales all three coefficients
by the same signed clock velocity. Position and momentum are composed with the clock. -/
theorem hamiltonian_system_graphClock
    {J P A B C : ℝ → Matrix n n ℝ} {s : ℝ → ℝ} {v t : ℝ}
    (hJ : HasDerivAt J (B (s t) * J (s t) + C (s t) * P (s t)) (s t))
    (hP : HasDerivAt P (-A (s t) * J (s t) - (B (s t))ᵀ * P (s t)) (s t))
    (hs : HasDerivAt s v t) :
    HasDerivAt (fun r ↦ J (s r))
        ((v • B (s t)) * J (s t) + (v • C (s t)) * P (s t)) t ∧
      HasDerivAt (fun r ↦ P (s r))
        (-(v • A (s t)) * J (s t) - (v • B (s t))ᵀ * P (s t)) t := by
  constructor
  · simpa only [smul_add, Matrix.smul_mul] using! hJ.scomp t hs
  · simpa only [smul_sub, smul_neg, Matrix.smul_mul, Matrix.transpose_smul,
      Matrix.neg_mul] using! hP.scomp t hs

/-- The actual old-time primitive equals the graph-time primitive at the actual
clock values. The coefficient scales by the signed velocity, not its absolute value. -/
theorem jacobiCompliancePrimitive_graphClock
    {J C : ℝ → Matrix n n ℝ} {a b t₀ t : ℝ} {s v : ℝ → ℝ}
    (hJ : DifferentiableOn ℝ J (Ioo a b)) (hC : ContinuousOn C (Ioo a b))
    (hd : ∀ r ∈ Ioo a b, (J r).det ≠ 0)
    (hs : ∀ r ∈ uIcc t₀ t, HasDerivAt s (v r) r)
    (hv : ContinuousOn v (uIcc t₀ t)) (himage : MapsTo s (uIcc t₀ t) (Ioo a b)) :
    jacobiCompliancePrimitive (fun r ↦ J (s r)) (fun r ↦ v r • C (s r)) t₀ t =
      jacobiCompliancePrimitive J C (s t₀) (s t) := by
  unfold jacobiCompliancePrimitive
  simp only [Matrix.mul_smul, Matrix.smul_mul]
  simpa only [Function.comp_def] using!
    intervalIntegral.integral_deriv_smul_comp' hs hv
      ((continuousOn_jacobiComplianceIntegrand hJ hC hd).mono
        (image_subset_iff.mpr himage))

/-- Moment integrability is unchanged when both the compliance primitive and
the original conditional clock are expressed in the actual old family time. -/
theorem integrable_originalTime_compliance_iff
    {J C : ℝ → Matrix n n ℝ} {a b l h t₀ u₀ r : ℝ} {s v : ℝ → ℝ}
    (hJ : DifferentiableOn ℝ J (Ioo a b)) (hC : ContinuousOn C (Ioo a b))
    (hd : ∀ q ∈ Ioo a b, (J q).det ≠ 0)
    (hs : ∀ q ∈ Ioo l h, HasDerivAt s (v q) q)
    (hv : ContinuousOn v (Ioo l h)) (himage : MapsTo s (Ioo l h) (Ioo a b))
    (ht₀ : t₀ ∈ Ioo l h) {μ : Measure ℝ}
    (hμ : ∀ᵐ x ∂μ, x - u₀ ∈ Ioo l h) :
    Integrable (fun x ↦ ‖jacobiCompliancePrimitive (fun q ↦ J (s q))
        (fun q ↦ v q • C (s q)) t₀ (x - u₀)‖ ^ r) μ ↔
      Integrable (fun x ↦ ‖jacobiCompliancePrimitive J C (s t₀) (s (x - u₀))‖ ^ r) μ := by
  apply integrable_congr
  filter_upwards [hμ] with x hx
  have hsegment : uIcc t₀ (x - u₀) ⊆ Ioo l h := ordConnected_Ioo.uIcc_subset ht₀ hx
  rw [jacobiCompliancePrimitive_graphClock hJ hC hd
    (fun q hq ↦ hs q (hsegment hq)) (hv.mono hsegment) (himage.mono_left hsegment)]

end OTSelector.Reconstruction
