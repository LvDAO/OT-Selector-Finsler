import OTSelector.Reconstruction.BirthResidueNormalizedMomentum
import OTSelector.Reconstruction.FocalNormalizerJacobian

/-! The actual birth normalization has its original Haar Jacobian at the same
residue rank. It is a scalar multiple of the previously proved focal scale. -/
open Matrix
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] in
/-- The same actual birth scale is a scalar multiple of the original focal scale. -/
theorem birthResidueScale_eq_smul_focal (G : Matrix ι ι ℝ) {t : ℝ} (ht : t ≠ 0) (s : ℝ) :
    birthResidueScale G t s = (s / t) • focalResidueScale G t := by
  have h₁ : (s / t) * t = s := div_mul_cancel₀ s ht
  have h₂ : (s / t) * t⁻¹ = s / t ^ 2 := by field_simp
  simp only [birthResidueScale, focalResidueScale, smul_add, smul_smul, h₁, h₂]

/-- The actual birth-scale determinant keeps the physical scalar dilation power. -/
theorem birthResidueScale_det_eq (G : Matrix ι ι ℝ) {t : ℝ} (ht : t ≠ 0) (s : ℝ) :
    (birthResidueScale G t s).det = (s / t) ^ Fintype.card ι * (focalResidueScale G t).det := by
  rw [birthResidueScale_eq_smul_focal G ht s, Matrix.det_smul]

/-- The same source/target birth scale has determinant comparable to
`s^q / t^(2 rank G)`, with constants internally produced from its physical residue. -/
theorem exists_birthResidueScale_det_rank_bounds {G : Matrix ι ι ℝ} (hG : G.PosSemidef) :
    ∃ c : ℝ, 0 < c ∧ ∃ C : ℝ, 0 < C ∧ ∀ t s : ℝ, 0 < t → t ≤ 1 → 0 < s →
      c * (s ^ Fintype.card ι / t ^ (2 * G.rank)) ≤ (birthResidueScale G t s).det ∧
      (birthResidueScale G t s).det ≤ C * (s ^ Fintype.card ι / t ^ (2 * G.rank)) := by
  obtain ⟨c, hc, C, hC, hbound⟩ := exists_focalResidueScale_det_rank_bounds hG
  refine ⟨c, hc, C, hC, fun t s ht ht1 hs ↦ ?_⟩
  obtain ⟨hl, hu⟩ := hbound t ht ht1
  rw [birthResidueScale_det_eq G ht.ne' s]
  have hscale (a : ℝ) : (s / t) ^ Fintype.card ι *
      (a * (t ^ Fintype.card ι / t ^ (2 * G.rank))) =
      a * (s ^ Fintype.card ι / t ^ (2 * G.rank)) := by
    rw [div_pow]
    field_simp
  constructor
  · simpa only [hscale] using mul_le_mul_of_nonneg_left hl (pow_nonneg (div_nonneg hs.le ht.le) (Fintype.card ι))
  · simpa only [hscale] using mul_le_mul_of_nonneg_left hu (pow_nonneg (div_nonneg hs.le ht.le) (Fintype.card ι))

/-- The actual canonical birth frame's inverse Haar Jacobian is comparable to
`sqrt(s^q/t^(2rankG))`, including singular and zero-rank residues. -/
theorem exists_birthNormalizer_inverse_jacobian_rank_bounds {G : Matrix ι ι ℝ} (hG : G.PosSemidef) :
    ∃ c : ℝ, 0 < c ∧ ∃ C : ℝ, 0 < C ∧ ∀ t s : ℝ, 0 < t → t ≤ 1 → 0 < s →
      Real.sqrt c * Real.sqrt (s ^ Fintype.card ι / t ^ (2 * G.rank)) ≤
          |((positiveMatrixNormalizer (birthResidueScale G t s))⁻¹).det| ∧
      |((positiveMatrixNormalizer (birthResidueScale G t s))⁻¹).det| ≤
        Real.sqrt C * Real.sqrt (s ^ Fintype.card ι / t ^ (2 * G.rank)) := by
  obtain ⟨c, hc, C, hC, hbound⟩ := exists_birthResidueScale_det_rank_bounds hG
  refine ⟨c, hc, C, hC, fun t s ht ht1 hs ↦ ?_⟩
  rw [positiveMatrixNormalizer_abs_inverse_det (birthResidueScale_posDef (t := t) hG hs)]
  obtain ⟨hl, hu⟩ := hbound t s ht ht1 hs
  constructor
  · simpa only [Real.sqrt_mul hc.le] using Real.sqrt_le_sqrt hl
  · simpa only [Real.sqrt_mul hC.le] using Real.sqrt_le_sqrt hu

end OTSelector.Reconstruction
