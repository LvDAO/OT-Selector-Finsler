import OTSelector.Reconstruction.PositiveResidueDeterminant
import Mathlib.Analysis.Real.Sqrt

/-!
# Actual focal normalization Jacobian and volume scaling

The same internally constructed normalizer used for the original full legs has inverse
Jacobian equal to the square root of its own scale determinant. Its volume exponent
therefore follows from the actual residue rank, without invertibility of the residue.
-/

open Matrix

noncomputable section
namespace OTSelector.Reconstruction

set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The inverse Jacobian squared is exactly the determinant of the scale normalized by
this same canonical positive normalizer. -/
theorem positiveMatrixNormalizer_inverse_det_sq {A : Matrix ι ι ℝ} (hA : A.PosDef) :
    ((positiveMatrixNormalizer A)⁻¹).det ^ 2 = A.det := by
  obtain ⟨hu, hn⟩ := positiveMatrixNormalizer_spec hA
  have hd := congrArg Matrix.det hn
  simp only [Matrix.det_mul, Matrix.det_transpose, Matrix.det_one] at hd
  have hi := (positiveMatrixNormalizer A).det_nonsing_inv_mul_det hu
  calc
    ((positiveMatrixNormalizer A)⁻¹).det ^ 2 =
        ((positiveMatrixNormalizer A)⁻¹).det ^ 2 *
          ((positiveMatrixNormalizer A).det * A.det * (positiveMatrixNormalizer A).det) := by
      rw [hd, mul_one]
    _ = (((positiveMatrixNormalizer A)⁻¹).det * (positiveMatrixNormalizer A).det) ^ 2 *
        A.det := by ring
    _ = A.det := by rw [hi]; simp

/-- The inverse Jacobian of the canonical positive normalizer is the nonnegative square
root of the scale determinant, including the empty-dimensional case. -/
theorem positiveMatrixNormalizer_abs_inverse_det {A : Matrix ι ι ℝ} (hA : A.PosDef) :
    |((positiveMatrixNormalizer A)⁻¹).det| = Real.sqrt A.det := by
  rw [← Real.sqrt_sq_eq_abs, positiveMatrixNormalizer_inverse_det_sq hA]

/-- The genuine focal frame has its actual scale determinant as its squared inverse
Jacobian; no separate Jacobian or nondegeneracy premise is supplied. -/
theorem focalNormalizer_inverse_det_sq {G : Matrix ι ι ℝ} (hG : G.PosSemidef)
    {t : ℝ} (ht : 0 < t) :
    ((positiveMatrixNormalizer (focalResidueScale G t))⁻¹).det ^ 2 =
      (focalResidueScale G t).det :=
  positiveMatrixNormalizer_inverse_det_sq (focalResidueScale_posDef hG ht)

/-- Exact volume change of the same actual focal normalization frame. -/
theorem focalNormalizer_abs_inverse_det {G : Matrix ι ι ℝ} (hG : G.PosSemidef)
    {t : ℝ} (ht : 0 < t) :
    |((positiveMatrixNormalizer (focalResidueScale G t))⁻¹).det| =
      Real.sqrt (focalResidueScale G t).det :=
  positiveMatrixNormalizer_abs_inverse_det (focalResidueScale_posDef hG ht)

/-- Determinant comparison transfers to the actual inverse Jacobian in the same focal
frame, with the exact square roots of the original comparison constants. -/
theorem focalNormalizer_inverse_jacobian_bounds_of_det_bounds
    {G : Matrix ι ι ℝ} (hG : G.PosSemidef) {t : ℝ} (ht : 0 < t)
    {c C r : ℝ} (hc : 0 ≤ c) (hC : 0 ≤ C)
    (hlo : c * r ≤ (focalResidueScale G t).det)
    (hhi : (focalResidueScale G t).det ≤ C * r) :
    Real.sqrt c * Real.sqrt r ≤
        |((positiveMatrixNormalizer (focalResidueScale G t))⁻¹).det| ∧
      |((positiveMatrixNormalizer (focalResidueScale G t))⁻¹).det| ≤
        Real.sqrt C * Real.sqrt r := by
  rw [focalNormalizer_abs_inverse_det hG ht]
  constructor
  · simpa only [Real.sqrt_mul hc] using Real.sqrt_le_sqrt hlo
  · simpa only [Real.sqrt_mul hC] using Real.sqrt_le_sqrt hhi

/-- Uniform two-sided actual frame volume bounds at the residue rank exponent. The same
positive constants control both the squared volume and its nonnegative square root. -/
theorem exists_focalNormalizer_inverse_jacobian_rank_bounds {G : Matrix ι ι ℝ}
    (hG : G.PosSemidef) :
    ∃ c : ℝ, 0 < c ∧ ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 0 < t → t ≤ 1 →
      (c * (t ^ Fintype.card ι / t ^ (2 * G.rank)) ≤
          ((positiveMatrixNormalizer (focalResidueScale G t))⁻¹).det ^ 2 ∧
        ((positiveMatrixNormalizer (focalResidueScale G t))⁻¹).det ^ 2 ≤
          C * (t ^ Fintype.card ι / t ^ (2 * G.rank))) ∧
      (Real.sqrt c * Real.sqrt (t ^ Fintype.card ι / t ^ (2 * G.rank)) ≤
          |((positiveMatrixNormalizer (focalResidueScale G t))⁻¹).det| ∧
        |((positiveMatrixNormalizer (focalResidueScale G t))⁻¹).det| ≤
          Real.sqrt C * Real.sqrt (t ^ Fintype.card ι / t ^ (2 * G.rank))) := by
  obtain ⟨c, hc, C, hC, hb⟩ := exists_focalResidueScale_det_rank_bounds hG
  refine ⟨c, hc, C, hC, ?_⟩
  intro t ht ht1
  obtain ⟨hl, hu⟩ := hb t ht ht1
  constructor
  · simpa only [focalNormalizer_inverse_det_sq hG ht] using And.intro hl hu
  · exact focalNormalizer_inverse_jacobian_bounds_of_det_bounds hG ht hc.le hC.le hl hu

end OTSelector.Reconstruction
