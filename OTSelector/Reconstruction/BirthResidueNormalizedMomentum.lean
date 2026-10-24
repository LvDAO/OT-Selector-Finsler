import OTSelector.Reconstruction.FocalResidueScaleNormalization
import OTSelector.LinearAlgebra.Matrix.ComplianceCongruenceCovariance
import OTSelector.Reconstruction.FinslerConcreteUpperModel
import OTSelector.Reconstruction.RegularClockLegLowerBound

/-! The canonical actual birth-scale normalizer controls its own transformed
momentum by the same residue energy. No independently chosen frame bound enters. -/
open Set Function Matrix
open scoped BigOperators Matrix.Norms.Operator
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The same canonical positive normalizer transforms momentum by its inverse
transpose, whose coordinate norm is controlled by its exact original scale energy. -/
theorem positiveMatrixNormalizer_momentum_norm_sq_le
    {A : Matrix ι ι ℝ} (hA : A.PosDef) (p : ι → ℝ) :
    ‖((positiveMatrixNormalizer A)ᵀ)⁻¹ *ᵥ p‖ ^ 2 ≤ p ⬝ᵥ (A *ᵥ p) := by
  let T := positiveMatrixNormalizer A
  obtain ⟨hu, hs⟩ := positiveMatrixNormalizer_spec hA
  let _ := Matrix.invertibleOfIsUnitDet T hu
  have h := matrixQuadratic_congruence_momentum T A p
  change matrixQuadratic (T * A * Tᵀ) ((Tᵀ)⁻¹ *ᵥ p) = matrixQuadratic A p at h
  rw [hs] at h
  have heq : (∑ i, (((Tᵀ)⁻¹ *ᵥ p) i) ^ 2) = p ⬝ᵥ (A *ᵥ p) := by
    simp only [matrixQuadratic, Matrix.one_mulVec, dotProduct, pow_two] at h ⊢
    linarith
  exact (pi_norm_sq_le_sum_sq ((Tᵀ)⁻¹ *ᵥ p)).trans_eq heq

/-- The actual birth normalization scale of the fixed original positive residue. -/
def birthResidueScale (G : Matrix ι ι ℝ) (t s : ℝ) : Matrix ι ι ℝ :=
  s • 1 + (s / t ^ 2) • G

omit [Fintype ι] in
/-- The same birth scale is positive for every positive physical time-window size. -/
theorem birthResidueScale_posDef {G : Matrix ι ι ℝ} (hG : G.PosSemidef)
    {t s : ℝ} (hs : 0 < s) : (birthResidueScale G t s).PosDef := by
  have h := (Matrix.PosDef.one.smul hs).add_posSemidef
    (hG.smul (div_nonneg hs.le (sq_nonneg t)))
  exact h

/-- The same canonical actual birth normalizer gives the precise source-energy
and full-momentum control at a source or target clock distance at most `2t`. -/
theorem birthResidueNormalizer_momentum_norm_le
    {G : Matrix ι ι ℝ} (hG : G.PosSemidef) {t s a : ℝ}
    (ht : 0 < t) (hs : 0 < s) (ha : 0 < a) (hat : a ≤ 2 * t) (p : ι → ℝ) :
    ‖((positiveMatrixNormalizer (birthResidueScale G t s))ᵀ)⁻¹ *ᵥ p‖ ≤
      Real.sqrt s * (Real.sqrt (Fintype.card ι : ℝ) * ‖p‖ +
        Real.sqrt (2 / t) * Real.sqrt ((p ⬝ᵥ (G *ᵥ p)) / a)) := by
  let e : ℝ := (p ⬝ᵥ (G *ᵥ p)) / a
  have hq : 0 ≤ p ⬝ᵥ (G *ᵥ p) := by simpa only [star_trivial] using hG.dotProduct_mulVec_nonneg p
  have he : 0 ≤ e := div_nonneg hq ha.le
  have hqeq : p ⬝ᵥ (G *ᵥ p) = a * e := by dsimp [e]; field_simp
  have hqle : p ⬝ᵥ (G *ᵥ p) ≤ 2 * t * e := by rw [hqeq]; gcongr
  have hbase := positiveMatrixNormalizer_momentum_norm_sq_le (birthResidueScale_posDef (t := t) hG hs) p
  have hdot : p ⬝ᵥ p = ∑ i, p i ^ 2 := by simp only [dotProduct, pow_two]
  simp only [birthResidueScale, Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
    dotProduct_add, dotProduct_smul, smul_eq_mul, hdot] at hbase
  have hpower : (s / t ^ 2) * (2 * t * e) = s * ((2 / t) * e) := by field_simp
  have hsq : ‖((positiveMatrixNormalizer (birthResidueScale G t s))ᵀ)⁻¹ *ᵥ p‖ ^ 2 ≤
      s * ((Fintype.card ι : ℝ) * ‖p‖ ^ 2 + (2 / t) * e) := by
    calc
      _ ≤ s * (∑ i, p i ^ 2) + (s / t ^ 2) * (p ⬝ᵥ (G *ᵥ p)) := hbase
      _ ≤ s * ((Fintype.card ι : ℝ) * ‖p‖ ^ 2) + (s / t ^ 2) * (2 * t * e) := by
        gcongr
        exact sum_sq_le_card_mul_pi_norm_sq p
      _ = _ := by rw [hpower]; ring
  have hn := Real.le_sqrt (norm_nonneg (((positiveMatrixNormalizer (birthResidueScale G t s))ᵀ)⁻¹ *ᵥ p))
    (show 0 ≤ s * ((Fintype.card ι : ℝ) * ‖p‖ ^ 2 + (2 / t) * e) by positivity)
  have hnorm := hn.mpr hsq
  rw [Real.sqrt_mul hs.le] at hnorm
  calc
    _ ≤ _ := hnorm
    _ ≤ Real.sqrt s * (Real.sqrt ((Fintype.card ι : ℝ) * ‖p‖ ^ 2) +
        Real.sqrt ((2 / t) * e)) := by
      apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg _)
      apply (Real.sqrt_le_left (add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))).mpr
      nlinarith [Real.sq_sqrt (show 0 ≤ (Fintype.card ι : ℝ) * ‖p‖ ^ 2 by positivity),
        Real.sq_sqrt (show 0 ≤ (2 / t) * e by positivity),
        mul_nonneg (Real.sqrt_nonneg ((Fintype.card ι : ℝ) * ‖p‖ ^ 2))
          (Real.sqrt_nonneg ((2 / t) * e))]
    _ = _ := by
      rw [Real.sqrt_mul (Nat.cast_nonneg _), Real.sqrt_sq_eq_abs,
        abs_of_nonneg (norm_nonneg _), Real.sqrt_mul (by positivity)]

end OTSelector.Reconstruction
