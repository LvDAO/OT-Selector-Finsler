import OTSelector.Reconstruction.BirthCanonicalMomentumLower

/-! # Physical double-pole speed in the same canonical birth momentum -/
open Matrix
open scoped Matrix.Norms.Operator
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The actual physical pole velocity is bounded by C/(t√s) times the canonical
birth momentum; the matrix remainder is allowed to be noncommuting. -/
theorem birthPole_velocity_le_canonicalMomentum
    {G Rem : Matrix ι ι ℝ} (hG : G.PosSemidef) {t s r L M : ℝ}
    (ht : 0 < t) (ht1 : t ≤ 1) (hs : 0 < s) (hr : t / 2 ≤ r)
    (hL : 0 ≤ L) (hM : 0 ≤ M)
    (hGnorm : ∀ p : ι → ℝ, ‖G *ᵥ p‖ ≤ L * Real.sqrt (p ⬝ᵥ (G *ᵥ p)))
    (hRem : ‖Rem‖ ≤ M) (p : ι → ℝ) :
    ‖(((r ^ 2)⁻¹ • G + Rem) *ᵥ p)‖ ≤
      ((4 * L + M) * Real.sqrt (Fintype.card ι : ℝ) / (t * Real.sqrt s)) *
        ‖((positiveMatrixNormalizer (birthResidueScale G t s))ᵀ)⁻¹ *ᵥ p‖ := by
  let p' := ((positiveMatrixNormalizer (birthResidueScale G t s))ᵀ)⁻¹ *ᵥ p
  have hroot := birthNormalizer_original_momentum_sqrt_bounds hG ht hs p
  have hr0 : 0 < r := lt_of_lt_of_le (half_pos ht) hr
  have hratio : t ^ 2 * (r ^ 2)⁻¹ ≤ 4 := by
    have h : t ^ 2 / r ^ 2 ≤ 4 := (div_le_iff₀ (sq_pos_of_pos hr0)).mpr (by nlinarith)
    simpa only [div_eq_mul_inv] using h
  have hW : ‖(((r ^ 2)⁻¹ • G + Rem) *ᵥ p)‖ ≤
      (r ^ 2)⁻¹ * L * Real.sqrt (p ⬝ᵥ (G *ᵥ p)) + M * ‖p‖ := by
    calc
      _ ≤ ‖(r ^ 2)⁻¹ • (G *ᵥ p)‖ + ‖Rem *ᵥ p‖ := by
        rw [Matrix.add_mulVec, Matrix.smul_mulVec]
        exact norm_add_le _ _
      _ = (r ^ 2)⁻¹ * ‖G *ᵥ p‖ + ‖Rem *ᵥ p‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (sq_nonneg r))]
      _ ≤ (r ^ 2)⁻¹ * (L * Real.sqrt (p ⬝ᵥ (G *ᵥ p))) + M * ‖p‖ := by
        apply add_le_add
        · exact mul_le_mul_of_nonneg_left (hGnorm p) (inv_nonneg.mpr (sq_nonneg r))
        · exact (Matrix.linfty_opNorm_mulVec _ _).trans
            (mul_le_mul_of_nonneg_right hRem (norm_nonneg p))
      _ = _ := by ring
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ (mul_pos ht (Real.sqrt_pos.mpr hs))).mpr
  calc
    _ ≤ ((r ^ 2)⁻¹ * L * Real.sqrt (p ⬝ᵥ (G *ᵥ p)) + M * ‖p‖) *
        (t * Real.sqrt s) := mul_le_mul_of_nonneg_right hW (by positivity)
    _ = (t * (r ^ 2)⁻¹ * L) * (Real.sqrt s * Real.sqrt (p ⬝ᵥ (G *ᵥ p))) +
        (t * M) * (Real.sqrt s * ‖p‖) := by ring
    _ ≤ (t * (r ^ 2)⁻¹ * L) * (t * Real.sqrt (Fintype.card ι : ℝ) * ‖p'‖) +
        (t * M) * (Real.sqrt (Fintype.card ι : ℝ) * ‖p'‖) :=
      add_le_add (mul_le_mul_of_nonneg_left hroot.2 (by positivity))
        (mul_le_mul_of_nonneg_left hroot.1 (by positivity))
    _ = (t ^ 2 * (r ^ 2)⁻¹ * L + t * M) *
        (Real.sqrt (Fintype.card ι : ℝ) * ‖p'‖) := by ring
    _ ≤ (4 * L + M) * (Real.sqrt (Fintype.card ι : ℝ) * ‖p'‖) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact add_le_add (mul_le_mul_of_nonneg_right hratio hL)
        (by simpa only [one_mul] using mul_le_mul_of_nonneg_right ht1 hM)
    _ = _ := by ring

end OTSelector.Reconstruction
