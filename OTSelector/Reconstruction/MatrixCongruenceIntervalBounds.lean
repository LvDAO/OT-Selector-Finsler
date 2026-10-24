import OTSelector.Reconstruction.OriginalFocalNormalizedPhaseBounds
import Mathlib.Analysis.Normed.Operator.Mul

/-!
# Integrating the same normalized actual mobility

A fixed congruence commutes with the original matrix integral. A bound on the actual
scaled normalized kernel therefore bounds its genuine compliance increment on every
subinterval, with either orientation, and makes relative short increments small.
-/

open Set Matrix MeasureTheory
open scoped Topology Matrix.Norms.Operator
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The same fixed phase congruence commutes with the unchanged original interval integral. -/
theorem intervalIntegral_congruence (T : Matrix ι ι ℝ) {W : ℝ→Matrix ι ι ℝ} {a b : ℝ}
    (hW : IntervalIntegrable W volume a b) :
    (∫s in a..b,T*W s*Tᵀ)=T*(∫s in a..b,W s)*Tᵀ := by
  simpa only [ContinuousLinearMap.mulLeftRight_apply] using
    (ContinuousLinearMap.mulLeftRight ℝ (Matrix ι ι ℝ) T Tᵀ).intervalIntegral_comp_comm hW

/-- Integrating the normalized actual kernel preserves its scaled norm bound exactly. -/
theorem norm_congruence_intervalIntegral_le_scaled
    (T : Matrix ι ι ℝ) {W : ℝ→Matrix ι ι ℝ} {a b t B : ℝ} (ht : 0<t)
    (hW : IntervalIntegrable W volume a b)
    (hbound : ∀s∈uIoc a b, ‖t•(T*W s*Tᵀ)‖≤B) :
    ‖T*(∫s in a..b,W s)*Tᵀ‖≤B*|b-a|/t := by
  have hh := intervalIntegral.norm_integral_le_of_norm_le_const hbound
  rw [intervalIntegral.integral_smul,intervalIntegral_congruence T hW,
    norm_smul,Real.norm_eq_abs,abs_of_pos ht] at hh
  apply (le_div_iff₀ ht).mpr
  nlinarith

/-- Every true relative short compliance increment is small in the same fixed frame. -/
theorem norm_congruence_intervalIntegral_le_relative
    (T : Matrix ι ι ℝ) {W : ℝ→Matrix ι ι ℝ} {a b t B σ : ℝ} (ht : 0<t) (hB : 0≤B)
    (hW : IntervalIntegrable W volume a b)
    (hbound : ∀s∈uIoc a b, ‖t•(T*W s*Tᵀ)‖≤B) (hspan : |b-a|≤σ*t) :
    ‖T*(∫s in a..b,W s)*Tᵀ‖≤B*σ := by
  calc
    _ ≤ B*|b-a|/t := norm_congruence_intervalIntegral_le_scaled T ht hW hbound
    _ ≤ B*(σ*t)/t := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hspan hB) ht.le
    _ = _ := by field_simp

end OTSelector.Reconstruction
