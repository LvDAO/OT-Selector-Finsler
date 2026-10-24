import OTSelector.Reconstruction.BirthPoleDyadicBounds
import OTSelector.LinearAlgebra.Matrix.PositiveResidueVelocity

/-!
# The actual birth-normalized momentum controls the original pole directions

These inequalities use the exact energy identity for the canonical normalizer.
They do not infer a lower bound from the previously proved upper momentum estimate.
-/
open Matrix
open scoped BigOperators Matrix.Norms.Operator
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The same inverse-transpose normalized momentum has exactly the original scale energy. -/
theorem positiveMatrixNormalizer_energy_eq_sum_sq
    {A : Matrix ι ι ℝ} (hA : A.PosDef) (p : ι → ℝ) :
    p ⬝ᵥ (A *ᵥ p) = ∑ i, ((((positiveMatrixNormalizer A)ᵀ)⁻¹ *ᵥ p) i) ^ 2 := by
  let T := positiveMatrixNormalizer A
  obtain ⟨hu, hs⟩ := positiveMatrixNormalizer_spec hA
  let _ := Matrix.invertibleOfIsUnitDet T hu
  have h := matrixQuadratic_congruence_momentum T A p
  change matrixQuadratic (T * A * Tᵀ) ((Tᵀ)⁻¹ *ᵥ p) = matrixQuadratic A p at h
  rw [hs] at h
  simp only [matrixQuadratic, Matrix.one_mulVec, dotProduct, pow_two] at h ⊢
  dsimp [T] at h
  linarith

/-- The actual canonical birth momentum controls both full original momentum and
its same-residue focal energy, with their correct short-time powers. -/
theorem birthNormalizer_original_momentum_sqrt_bounds
    {G : Matrix ι ι ℝ} (hG : G.PosSemidef) {t s : ℝ}
    (ht : 0 < t) (hs : 0 < s) (p : ι → ℝ) :
    let p' := ((positiveMatrixNormalizer (birthResidueScale G t s))ᵀ)⁻¹ *ᵥ p
    Real.sqrt s * ‖p‖ ≤ Real.sqrt (Fintype.card ι : ℝ) * ‖p'‖ ∧
      Real.sqrt s * Real.sqrt (p ⬝ᵥ (G *ᵥ p)) ≤
        t * Real.sqrt (Fintype.card ι : ℝ) * ‖p'‖ := by
  let p' := ((positiveMatrixNormalizer (birthResidueScale G t s))ᵀ)⁻¹ *ᵥ p
  have hq : 0 ≤ p ⬝ᵥ (G *ᵥ p) := by simpa only [star_trivial] using hG.dotProduct_mulVec_nonneg p
  have hE := positiveMatrixNormalizer_energy_eq_sum_sq (birthResidueScale_posDef (t := t) hG hs) p
  have hdot : p ⬝ᵥ p = ∑ i, p i ^ 2 := by simp only [dotProduct, pow_two]
  simp only [birthResidueScale, Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
    dotProduct_add, dotProduct_smul, smul_eq_mul, hdot] at hE
  change s * (∑ i, p i ^ 2) + (s / t ^ 2) * (p ⬝ᵥ (G *ᵥ p)) = ∑ i, p' i ^ 2 at hE
  have hsum : ∑ i, p' i ^ 2 ≤ (Fintype.card ι : ℝ) * ‖p'‖ ^ 2 :=
    sum_sq_le_card_mul_pi_norm_sq p'
  have hfull : s * ‖p‖ ^ 2 ≤ (Fintype.card ι : ℝ) * ‖p'‖ ^ 2 := by
    have hnorm := mul_le_mul_of_nonneg_left (pi_norm_sq_le_sum_sq p) hs.le
    have hpos : 0 ≤ (s / t ^ 2) * (p ⬝ᵥ (G *ᵥ p)) := by positivity
    linarith
  have hpole : s * (p ⬝ᵥ (G *ᵥ p)) ≤ t ^ 2 * ((Fintype.card ι : ℝ) * ‖p'‖ ^ 2) := by
    have hsum0 : 0 ≤ s * ∑ i, p i ^ 2 := by positivity
    have hle : (s / t ^ 2) * (p ⬝ᵥ (G *ᵥ p)) ≤
        (Fintype.card ι : ℝ) * ‖p'‖ ^ 2 := by linarith
    have h := mul_le_mul_of_nonneg_left hle (sq_nonneg t)
    have heq : t ^ 2 * ((s / t ^ 2) * (p ⬝ᵥ (G *ᵥ p))) = s * (p ⬝ᵥ (G *ᵥ p)) := by
      field_simp
    rwa [heq] at h
  constructor
  · apply (sq_le_sq₀ (by positivity) (by positivity)).mp
    calc
      _ = s * ‖p‖ ^ 2 := by rw [mul_pow, Real.sq_sqrt hs.le]
      _ ≤ _ := hfull
      _ = _ := by rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
  · apply (sq_le_sq₀ (by positivity) (by positivity)).mp
    calc
      _ = s * (p ⬝ᵥ (G *ᵥ p)) := by
        rw [mul_pow, Real.sq_sqrt hs.le, Real.sq_sqrt hq]
      _ ≤ _ := hpole
      _ = _ := by simp only [mul_pow, Real.sq_sqrt (Nat.cast_nonneg _)]; ring

end OTSelector.Reconstruction
