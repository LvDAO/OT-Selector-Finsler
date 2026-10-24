import Mathlib.Algebra.Order.Star.Real
import OTSelector.LinearAlgebra.Matrix.CompactPositiveQuadratic
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Reconstruction.CompliancePhaseCovariance.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Reconstruction.CompliancePhaseCovariance`; the selected original proof blocks follow. -/
section

/-!
# Reconstruction.CompliancePhaseCovariance

**Conditions:** Finite real matrices and an invertible spatial frame T; the original legal two-cycle comparison is retained exactly.

**Objects:** Compliance congruence, inverse-transpose momentum and unchanged physical quadratic/path-offset expressions.

**Proof detail:** Expand matrix products and transpose/inverse identities; T cancels against T⁻¹ in costs and offsets, then substitute the exact transformed identities into the original cycle inequality.

**Sources:** [Stephen Boyd; Lieven Vandenberghe, Convex Optimization (2004)](https://web.stanford.edu/~boyd/cvxbook/bv_cvxbook.pdf#page=662), Appendix A.5.1, pp. 645–646 (range/nullspace/rank); A.5.2, p. 647 (positive square root); A.5.4, pp. 648–649 (SVD and the nonzero spectra of A^T A and A A^T); [Stephen Boyd; Lieven Vandenberghe, Convex Optimization](https://web.stanford.edu/~boyd/cvxbook/bv_cvxbook.pdf#page=108), Section 3.3.2, Fenchel’s inequality and quadratic example, p. 94.

Source relation (corollary): The cited sections provide the stated mathematical foundations; the exact finite construction and quantitative bound in this module are local consequences, not a claim that the book states the Lean theorem verbatim.
-/

/-!
# Exact covariance of original compliance phase coordinates

An invertible linear change of physical position transforms each original compliance by
congruence and its momentum by the inverse transpose. Actual quadratic costs and complete
path offsets agree exactly, including noncommuting anisotropic changes of basis.
-/

open Set Function Matrix
open scoped Matrix.Norms.Operator

noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
set_option linter.unusedSectionVars false

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Quadratic energy transforms by the same original compliance congruence. -/
theorem matrixQuadratic_congruence (T A : Matrix ι ι ℝ) (v : ι → ℝ) :
    matrixQuadratic (T * A * Tᵀ) v = matrixQuadratic A (Tᵀ *ᵥ v) := by
  have hs := Matrix.dotProduct_transpose_mulVec Tᵀ v (A *ᵥ (Tᵀ *ᵥ v))
  rw [Matrix.transpose_transpose, dotProduct_comm (A *ᵥ (Tᵀ *ᵥ v))] at hs
  simp only [matrixQuadratic, ← Matrix.mulVec_mulVec]
  rw [hs]

/-- The physical inverse-compliance cost is unchanged under an invertible change of position. -/
theorem matrixQuadratic_inverse_congruence (T A : Matrix ι ι ℝ) [Invertible T]
    (v : ι → ℝ) :
    matrixQuadratic (T * A * Tᵀ)⁻¹ (T *ᵥ v) = matrixQuadratic A⁻¹ v := by
  have heq : (T * A * Tᵀ)⁻¹ = T⁻¹ᵀ * A⁻¹ * (T⁻¹ᵀ)ᵀ := by
    simp only [Matrix.mul_inv_rev, Matrix.transpose_nonsing_inv, Matrix.transpose_transpose,
      Matrix.mul_assoc]
  rw [heq, matrixQuadratic_congruence, Matrix.transpose_transpose, Matrix.mulVec_mulVec,
    Matrix.inv_mul_of_invertible, Matrix.one_mulVec]

/-- The actual momentum transforms by the inverse transpose of the same spatial change. -/
theorem inverse_congruence_momentum (T A : Matrix ι ι ℝ) [Invertible T] (v : ι → ℝ) :
    (T * A * Tᵀ)⁻¹ *ᵥ (T *ᵥ v) = (Tᵀ)⁻¹ *ᵥ (A⁻¹ *ᵥ v) := by
  rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev]
  simp only [← Matrix.mulVec_mulVec]
  rw [Matrix.mulVec_mulVec v T⁻¹ T, Matrix.inv_mul_of_invertible, Matrix.one_mulVec]

/-- An actual compliance path offset is covariant under that same coordinate change. -/
theorem compliance_congruence_path_offset (T A : Matrix ι ι ℝ) [Invertible T] (p : ι → ℝ) :
    (T * A * Tᵀ) *ᵥ ((Tᵀ)⁻¹ *ᵥ p) = T *ᵥ (A *ᵥ p) := by
  have hT : IsUnit Tᵀ.det := Matrix.isUnit_det_transpose T (Matrix.isUnit_det_of_invertible T)
  let _ := Matrix.invertibleOfIsUnitDet Tᵀ hT
  simp only [← Matrix.mulVec_mulVec]
  rw [Matrix.mulVec_mulVec p Tᵀ (Tᵀ)⁻¹, Matrix.mul_inv_of_invertible, Matrix.one_mulVec]

/-- The original positive-compliance energy is unchanged when momentum is transformed
contragrediently by the same invertible spatial change. -/
theorem matrixQuadratic_congruence_momentum (T A : Matrix ι ι ℝ) [Invertible T]
    (p : ι → ℝ) :
    matrixQuadratic (T * A * Tᵀ) ((Tᵀ)⁻¹ *ᵥ p) = matrixQuadratic A p := by
  have hT : IsUnit Tᵀ.det := Matrix.isUnit_det_transpose T (Matrix.isUnit_det_of_invertible T)
  let _ := Matrix.invertibleOfIsUnitDet Tᵀ hT
  rw [matrixQuadratic_congruence, Matrix.mulVec_mulVec, Matrix.mul_inv_of_invertible,
    Matrix.one_mulVec]

/-- A complete four-leg cycle comparison is covariant under any invertible spatial change;
the same original defect is retained. This verifies the anisotropic phase normalization
before any coarse scalar rescaling. -/
theorem legalTwoCycle_compliance_congruence
    (T A₁ B₁ A₂ B₂ : Matrix ι ι ℝ) [Invertible T]
    (p₁ p₂ δ : ι → ℝ) (D₀ : ℝ)
    (hcycle : matrixQuadratic (A₁ + B₁) p₁ + matrixQuadratic (A₂ + B₂) p₂ ≤
      matrixQuadratic (A₁ + B₂)⁻¹ (δ + A₁ *ᵥ p₁ + B₂ *ᵥ p₂) +
        matrixQuadratic (A₂ + B₁)⁻¹ (-δ + A₂ *ᵥ p₂ + B₁ *ᵥ p₁) + D₀) :
    let A₁' := T * A₁ * Tᵀ
    let B₁' := T * B₁ * Tᵀ
    let A₂' := T * A₂ * Tᵀ
    let B₂' := T * B₂ * Tᵀ
    let p₁' := (Tᵀ)⁻¹ *ᵥ p₁
    let p₂' := (Tᵀ)⁻¹ *ᵥ p₂
    let δ' := T *ᵥ δ
    matrixQuadratic (A₁' + B₁') p₁' + matrixQuadratic (A₂' + B₂') p₂' ≤
      matrixQuadratic (A₁' + B₂')⁻¹ (δ' + A₁' *ᵥ p₁' + B₂' *ᵥ p₂') +
        matrixQuadratic (A₂' + B₁')⁻¹ (-δ' + A₂' *ᵥ p₂' + B₁' *ᵥ p₁') + D₀ := by
  have hsum (A B : Matrix ι ι ℝ) :
      T * A * Tᵀ + T * B * Tᵀ = T * (A + B) * Tᵀ := by
    simp only [Matrix.mul_add, Matrix.add_mul]
  have hcross (A B : Matrix ι ι ℝ) (p q z : ι → ℝ) :
      matrixQuadratic (T * A * Tᵀ + T * B * Tᵀ)⁻¹
        (T *ᵥ z + (T * A * Tᵀ) *ᵥ ((Tᵀ)⁻¹ *ᵥ p) +
          (T * B * Tᵀ) *ᵥ ((Tᵀ)⁻¹ *ᵥ q)) =
        matrixQuadratic (A + B)⁻¹ (z + A *ᵥ p + B *ᵥ q) := by
    rw [hsum, compliance_congruence_path_offset, compliance_congruence_path_offset,
      ← Matrix.mulVec_add, ← Matrix.mulVec_add, matrixQuadratic_inverse_congruence]
  dsimp only
  rw [hcross A₁ B₂ p₁ p₂ δ]
  have hsecond := hcross A₂ B₁ p₂ p₁ (-δ)
  rw [Matrix.mulVec_neg] at hsecond
  rw [hsecond, hsum A₁ B₁, hsum A₂ B₂,
    matrixQuadratic_congruence_momentum, matrixQuadratic_congruence_momentum]
  exact hcycle

end OTSelector.Reconstruction

end
end
