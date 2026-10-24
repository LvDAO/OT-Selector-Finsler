import OTSelector.Reconstruction.BirthCanonicalMomentumLower
import OTSelector.Reconstruction.BirthPoleDyadicBounds

/-! Canonical scalar birth frames in the regular clock region. The scale is
exactly s I; all matrix bounds and the physical sqrt(s) traffic gain follow
without a selected residue, pole model, or extra geometric hypothesis. -/
open Matrix
open scoped Matrix.Norms.Operator
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 900000
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A true original leg comparable with s I has the same fixed bounds after
canonical normalization, without a condition-number loss. -/
theorem scalar_birth_normalized_leg_bounds {A : Matrix ι ι ℝ} {s c C : ℝ}
    (hs : 0 < s) (hlower : (A - c • (s • 1)).PosSemidef)
    (hupper : (C • (s • 1) - A).PosSemidef) :
    let T := positiveMatrixNormalizer (s • (1 : Matrix ι ι ℝ))
    (T * A * Tᵀ - c • 1).PosSemidef ∧
      (C • 1 - T * A * Tᵀ).PosSemidef := by
  have hscale : (s • (1 : Matrix ι ι ℝ)).PosDef := Matrix.PosDef.one.smul hs
  refine ⟨posSemidef_positiveMatrixNormalizer_congruence_lower hscale hlower, ?_⟩
  have h := hupper.mul_mul_conjTranspose_same (positiveMatrixNormalizer (s • (1 : Matrix ι ι ℝ)))
  rw [Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.mul_sub,
    Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul,
    (positiveMatrixNormalizer_spec hscale).2] at h
  exact h

/-- Uniform true regular mobility bounds become scale-independent bounds in
its canonical scalar birth frame. -/
theorem scalar_birth_normalized_mobility_bounds {W : Matrix ι ι ℝ} {s c C : ℝ}
    (hs : 0 < s) (hlower : (W - c • 1).PosSemidef)
    (hupper : (C • 1 - W).PosSemidef) :
    let T := positiveMatrixNormalizer (s • (1 : Matrix ι ι ℝ))
    (s • (T * W * Tᵀ) - c • 1).PosSemidef ∧
      (C • 1 - s • (T * W * Tᵀ)).PosSemidef := by
  have hl : (s • W - c • (s • (1 : Matrix ι ι ℝ))).PosSemidef := by
    convert hlower.smul hs.le using 1
    module
  have hu : (C • (s • (1 : Matrix ι ι ℝ)) - s • W).PosSemidef := by
    convert hupper.smul hs.le using 1
    module
  simpa only [Matrix.mul_smul, Matrix.smul_mul] using scalar_birth_normalized_leg_bounds hs hl hu

/-- The canonical scalar frame controls the actual physical velocity by its
own normalized momentum with the precise inverse-sqrt(s) factor. -/
theorem regular_birth_velocity_le_canonicalMomentum {W : Matrix ι ι ℝ} {s M : ℝ}
    (hs : 0 < s) (hM : 0 ≤ M) (hW : ‖W‖ ≤ M) (p : ι → ℝ) :
    ‖W *ᵥ p‖ ≤ (M * Real.sqrt (Fintype.card ι : ℝ) / Real.sqrt s) *
      ‖((positiveMatrixNormalizer (s • (1 : Matrix ι ι ℝ)))ᵀ)⁻¹ *ᵥ p‖ := by
  have hroot := (birthNormalizer_original_momentum_sqrt_bounds
    (G := (0 : Matrix ι ι ℝ)) Matrix.PosSemidef.zero (t := 1) (by norm_num) hs p).1
  simp only [birthResidueScale, smul_zero, add_zero] at hroot
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ (Real.sqrt_pos.mpr hs)).mpr
  calc
    _ ≤ (M * ‖p‖) * Real.sqrt s := mul_le_mul_of_nonneg_right
      ((Matrix.linfty_opNorm_mulVec _ _).trans
        (mul_le_mul_of_nonneg_right hW (norm_nonneg p))) (Real.sqrt_nonneg _)
    _ = M * (Real.sqrt s * ‖p‖) := by ring
    _ ≤ M * (Real.sqrt (Fintype.card ι : ℝ) *
        ‖((positiveMatrixNormalizer (s • (1 : Matrix ι ι ℝ)))ᵀ)⁻¹ *ᵥ p‖) :=
      mul_le_mul_of_nonneg_left hroot hM
    _ = _ := by ring

/-- A physical window of size at most A s gives the true sqrt(s) gain before
any probabilistic count or selection estimate is applied. -/
theorem regular_birth_window_velocity_le_canonicalMomentum
    {W : Matrix ι ι ℝ} {s M A ell : ℝ} (hs : 0 < s) (hM : 0 ≤ M)
    (hA : 0 ≤ A) (hells : ell ≤ A * s) (hW : ‖W‖ ≤ M)
    (p : ι → ℝ) :
    ell * ‖W *ᵥ p‖ ≤ (A * M * Real.sqrt (Fintype.card ι : ℝ) * Real.sqrt s) *
      ‖((positiveMatrixNormalizer (s • (1 : Matrix ι ι ℝ)))ᵀ)⁻¹ *ᵥ p‖ := by
  have hv := regular_birth_velocity_le_canonicalMomentum hs hM hW p
  calc
    _ ≤ (A * s) * ((M * Real.sqrt (Fintype.card ι : ℝ) / Real.sqrt s) *
        ‖((positiveMatrixNormalizer (s • (1 : Matrix ι ι ℝ)))ᵀ)⁻¹ *ᵥ p‖) := by
      exact mul_le_mul hells hv (norm_nonneg _) (by positivity)
    _ = _ := by
      have hsqrt : Real.sqrt s ≠ 0 := (Real.sqrt_pos.mpr hs).ne'
      have hsquare := Real.sq_sqrt hs.le
      field_simp
      rw [hsquare]
      ring

end OTSelector.Reconstruction
