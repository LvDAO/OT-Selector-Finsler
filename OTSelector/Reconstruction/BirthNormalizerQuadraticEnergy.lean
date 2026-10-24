import OTSelector.Reconstruction.BirthResidueNormalizedMomentum

/-! The canonical birth-frame quadratic momentum is bounded by the same
original focal and full-momentum energies, retaining each band's energy budget. -/
open Set Function Matrix
open scoped BigOperators Matrix.Norms.Operator
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The actual canonical inverse-transpose birth momentum square is bounded
by its own original full energy and same-residue endpoint energy. -/
theorem birthNormalizer_momentum_sq_le_source_energy
    {G : Matrix ι ι ℝ} (hG : G.PosSemidef) {t s a : ℝ}
    (ht : 0 < t) (hs : 0 < s) (ha : 0 < a) (hat : a ≤ 2 * t) (p : ι → ℝ) :
    ‖((positiveMatrixNormalizer (birthResidueScale G t s))ᵀ)⁻¹ *ᵥ p‖ ^ 2 ≤
      (s * (Fintype.card ι : ℝ)) * ‖p‖ ^ 2 +
        (2 * s / t) * ((p ⬝ᵥ (G *ᵥ p)) / a) := by
  let e : ℝ := (p ⬝ᵥ (G *ᵥ p)) / a
  have hq : 0 ≤ p ⬝ᵥ (G *ᵥ p) := by simpa only [star_trivial] using hG.dotProduct_mulVec_nonneg p
  have he : 0 ≤ e := div_nonneg hq ha.le
  have hqeq : p ⬝ᵥ (G *ᵥ p) = a * e := by dsimp [e]; field_simp
  have hqle : p ⬝ᵥ (G *ᵥ p) ≤ 2 * t * e := by rw [hqeq]; gcongr
  have hb := positiveMatrixNormalizer_momentum_norm_sq_le (birthResidueScale_posDef (t := t) hG hs) p
  have hd : p ⬝ᵥ p = ∑ i, p i ^ 2 := by simp only [dotProduct, pow_two]
  simp only [birthResidueScale, Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
    dotProduct_add, dotProduct_smul, smul_eq_mul, hd] at hb
  calc
    _ ≤ s * (∑ i, p i ^ 2) + (s / t ^ 2) * (p ⬝ᵥ (G *ᵥ p)) := hb
    _ ≤ s * ((Fintype.card ι : ℝ) * ‖p‖ ^ 2) + (s / t ^ 2) * (2 * t * e) := by
      gcongr
      exact sum_sq_le_card_mul_pi_norm_sq p
    _ = _ := by change _ = (s * (Fintype.card ι : ℝ)) * ‖p‖ ^ 2 + (2 * s / t) * e; field_simp

end OTSelector.Reconstruction
