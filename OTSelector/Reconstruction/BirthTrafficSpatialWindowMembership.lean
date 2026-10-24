import OTSelector.Reconstruction.BirthTrafficSourceWindowVolume

/-! Membership in the actual birth traffic source window is exactly the
scaled canonical normalized endpoint bound. -/
open Set Matrix MeasureTheory
open scoped Matrix.Norms.Operator
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The original physical point is in the very same traffic window used by
its physical Haar-volume bound; no condition number is introduced. -/
theorem mem_birthTrafficSpatialWindow_of_normalized_norm
    {G : Matrix ι ι ℝ} (hG : G.PosSemidef) {t s R : ℝ}
    (ht : 0 < t) (hs : 0 < s) (x : ι → ℝ)
    (hx : ‖positiveMatrixNormalizer (birthResidueScale G t s) *ᵥ x‖ ≤
      birthTrafficCoarseScale (Fintype.card ι) t s * R) :
    x ∈ birthTrafficSpatialWindow G t s R := by
  let T := positiveMatrixNormalizer (birthResidueScale G t s)
  let δ := birthTrafficCoarseScale (Fintype.card ι) t s
  have hδ : 0 < δ := birthTrafficCoarseScale_pos _ ht hs
  let _ := Matrix.invertibleOfIsUnitDet T
    (positiveMatrixNormalizer_spec (birthResidueScale_posDef (t := t) hG hs)).1
  refine ⟨δ⁻¹ • (T *ᵥ x), ?_, ?_⟩
  · rw [Metric.mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr hδ)]
    have hh := mul_le_mul_of_nonneg_left hx (inv_nonneg.mpr hδ.le)
    change δ⁻¹ * ‖T *ᵥ x‖ ≤ R
    calc
      _ ≤ δ⁻¹ * (δ * R) := hh
      _ = R := by field_simp
  · change (δ • T⁻¹) *ᵥ (δ⁻¹ • (T *ᵥ x)) = x
    rw [Matrix.smul_mulVec, Matrix.mulVec_smul, smul_smul, mul_inv_cancel₀ hδ.ne', one_smul,
      Matrix.mulVec_mulVec, Matrix.inv_mul_of_invertible, Matrix.one_mulVec]

/-- A positive coarse scale at least one absorbs the actual fixed node error,
so all bounded-phase physical windows share one scale-independent radius. -/
theorem bounded_phase_endpoint_radius_le_coarseScale
    {δ A H L b ρ C : ℝ} (hδ : 1 ≤ δ) (hb : 0 ≤ b)
    (hρ : 0 ≤ ρ) (hC : 0 ≤ C) :
    A * δ + (ρ + C) * (2 * (H * δ) + 2 * (L * (A * δ) + b)) ≤
      δ * (A + (ρ + C) * (2 * H + 2 * (L * A + b))) := by
  nlinarith [mul_nonneg (add_nonneg hρ hC) (mul_nonneg hb (sub_nonneg.mpr hδ))]

end OTSelector.Reconstruction
