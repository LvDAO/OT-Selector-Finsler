import Mathlib.Analysis.Matrix.Order
import Mathlib.LinearAlgebra.Matrix.Rank

/-!
## Lemma skeleton

* **Conditions:** A finite real rectangular matrix R and a positive definite finite real square weight C; R may be singular and either index type may be empty.
* **Objects:** Equality of ranks of R C R^T and R.
* **Proof detail:** Write C as S S^T using its invertible positive square root. Apply rank(A A^T)=rank(A) to A=R S, then invariance under multiplication by invertible S.

## Mathematical sources

* Stephen Boyd; Lieven Vandenberghe, *Convex Optimization (2004)*, Appendix A.5.1, pp. 645–646 (range/nullspace/rank); A.5.2, p. 647 (positive square root); A.5.4, pp. 648–649 (SVD and the nonzero spectra of A^T A and A A^T).
  https://web.stanford.edu/~boyd/cvxbook/bv_cvxbook.pdf#page=662

**Relationship to the sources:** Weighted Gram-rank corollary of positive square roots and the SVD Gram spectrum.
-/

/-! The rank of a positive weighted Gram matrix equals the original map rank. -/
open Matrix
open scoped MatrixOrder
noncomputable section
namespace OTSelector.Probability

/-- A positive definite weight loses no rank, including for a rectangular or
singular original map. This identifies actual focal residue ranks. -/
theorem rank_positive_congruence {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n] (R : Matrix m n ℝ)
    {C : Matrix n n ℝ} (hC : C.PosDef) : (R * C * Rᵀ).rank = R.rank := by
  let S := CFC.sqrt C
  have hS : S.PosSemidef := (CFC.sqrt_nonneg C).posSemidef
  have hSS : S * S = C := by simpa only [pow_two] using CFC.sq_sqrt C
  have hSt : Sᵀ = S := by
    simpa only [conjTranspose_eq_transpose_of_trivial] using hS.isHermitian.eq
  have hdet : det S ≠ 0 := by
    intro hzero
    have h : det C = 0 := by rw [← hSS, det_mul, hzero, zero_mul]
    exact hC.det_pos.ne' h
  calc
    _ = ((R * S) * (R * S)ᵀ).rank := by
      congr 1
      rw [transpose_mul, hSt, ← hSS]
      simp only [Matrix.mul_assoc]
    _ = (R * S).rank := rank_self_mul_transpose _
    _ = R.rank := rank_mul_eq_left_of_det_ne_zero S R hdet

end OTSelector.Probability
