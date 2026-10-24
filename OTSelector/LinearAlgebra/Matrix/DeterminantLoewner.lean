import Mathlib.Analysis.Matrix.Order
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Module
import Mathlib.Tactic.NoncommRing

/-!
## Lemma skeleton

* **Conditions:** Finite real square matrices; a positive semidefinite increment, with a positive definite lower matrix for the monotonicity conclusion.
* **Objects:** det(I+U) >= 1 and det(A) <= det(B) when B-A is positive semidefinite.
* **Proof detail:** Diagonalize the semidefinite matrix for the first inequality. For the second, use the positive square root of A, conjugate the increment by its inverse, and factor the determinant.

## Mathematical sources

* Stephen Boyd; Lieven Vandenberghe, *Convex Optimization (2004)*, Section 2.2.5, p. 34; Section 2.4.1, Example 2.15, p. 43; Appendix A.5.2, pp. 646–647 (spectral decomposition, determinant, definiteness, symmetric square root).
  https://web.stanford.edu/~boyd/cvxbook/bv_cvxbook.pdf#page=660

**Relationship to the sources:** Elementary spectral and square-root-congruence consequences of the cited matrix facts, rather than a separately quoted determinant-monotonicity theorem.
-/

/-! Determinant monotonicity from positive square roots, without ordered eigenvalues. -/
open Matrix
open scoped MatrixOrder
noncomputable section
namespace OTSelector.Probability
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Adding a positive semidefinite matrix to the identity increases its determinant. -/
theorem one_le_det_one_add_of_posSemidef {U : Matrix ι ι ℝ} (hU : U.PosSemidef) :
    1 ≤ det (1 + U) := by
  let V := hU.1.eigenvectorUnitary
  let D := diagonal (fun i ↦ hU.1.eigenvalues i)
  have hUeq : U = (V : Matrix ι ι ℝ) * D * star (V : Matrix ι ι ℝ) := by
    simpa only [V, D, Function.comp_def, RCLike.ofReal_real_eq_id, id_eq,
      Unitary.conjStarAlgAut_apply] using hU.1.spectral_theorem
  have hV : star (V : Matrix ι ι ℝ) * (V : Matrix ι ι ℝ) = 1 :=
    Unitary.coe_star_mul_self V
  rw [hUeq, Matrix.mul_assoc, det_one_add_mul_comm]
  rw [Matrix.mul_assoc, hV, Matrix.mul_one]
  have hdiag : (1 : Matrix ι ι ℝ) + D = diagonal (fun i ↦ 1 + hU.1.eigenvalues i) := by
    rw [← diagonal_one, ← diagonal_add]
  rw [hdiag, det_diagonal]
  exact Finset.one_le_prod (fun i _ ↦ by linarith [hU.eigenvalues_nonneg i])

/-- Determinants are monotone for a positive definite lower matrix in Loewner order. -/
theorem det_mono_of_posDef_of_posSemidef_sub {A B : Matrix ι ι ℝ}
    (hA : A.PosDef) (hBA : (B - A).PosSemidef) : det A ≤ det B := by
  let S := CFC.sqrt A
  have hS : S.PosSemidef := (CFC.sqrt_nonneg A).posSemidef
  have hSsq : S * S = A := by simpa only [pow_two] using CFC.sq_sqrt A
  have hSdet : det S ≠ 0 := by
    change det (CFC.sqrt A) ≠ 0
    rw [hA.posSemidef.det_sqrt, RCLike.sqrt_of_nonneg hA.det_pos.le]
    simpa only [RCLike.ofReal_real_eq_id, id_eq, RCLike.re_to_real] using
      (Real.sqrt_pos.mpr hA.det_pos).ne'
  let _ : Invertible S := (hS.posDef_iff_det_ne_zero.mpr hSdet).isUnit.invertible
  let C := S⁻¹ * (B - A) * S⁻¹
  have hC : C.PosSemidef := by
    simpa only [hS.inv.isHermitian.eq] using hBA.mul_mul_conjTranspose_same S⁻¹
  have hBfact : B = S * (1 + C) * S := by
    symm
    calc
      _ = S * S + (S * S⁻¹) * (B - A) * (S⁻¹ * S) := by dsimp [C]; noncomm_ring
      _ = A + (B - A) := by
        rw [hSsq, Matrix.mul_inv_of_invertible, Matrix.inv_mul_of_invertible]
        simp only [one_mul, mul_one]
      _ = B := by abel
  have hdet : det B = det A * det (1 + C) := by
    calc
      _ = det S * det (1 + C) * det S := by rw [hBfact, det_mul, det_mul]
      _ = (det S * det S) * det (1 + C) := by ring
      _ = _ := by rw [← det_mul, hSsq]
  rw [hdet]
  exact le_mul_of_one_le_right hA.det_pos.le (one_le_det_one_add_of_posSemidef hC)

end OTSelector.Probability
