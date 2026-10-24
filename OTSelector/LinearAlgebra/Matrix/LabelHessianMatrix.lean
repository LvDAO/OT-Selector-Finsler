import OTSelector.Analysis.Convex.HomogeneousEnergy
import OTSelector.Analysis.ODE.Hamiltonian.MatrixCoordinates
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Geometry.LabelHessianMatrix.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Geometry.LabelHessianMatrix`; the selected original proof blocks follow. -/
section

/-!
Conditions: A bilinear endpoint form, actual label linear map and nonzero clock scale; positivity/inverse assumptions as stated.

Objects: Label Hessian congruence and inverse-form matrix formulas retaining label and clock factors.

Proof detail: Expand the pullback on basis vectors, obtain J transpose H J and substitute the inverse operator identities with the explicit scalar factor.

Sources: Jiří Lebl, Section 8.1.3, Propositions 8.1.17–8.1.18, p. 15 (https://www.jirka.org/ra/realanal2.pdf#page=15); Stephen Boyd, Section 2.2.5, p. 34; Section 2.4.1, Example 2.15, p. 43; Appendix A.5.2, pp. 646–647 (https://web.stanford.edu/~boyd/cvxbook/bv_cvxbook.pdf#page=48).
Relation: Elementary congruence and inverse-form adapter; no isometric label normalization is assumed.
-/

/-!
# Fixed-label matrices of positive length Hessians

Pulling a genuine bilinear Hessian back by a label derivative gives its usual matrix
congruence. Inverting it retains both the label matrix and any positive clock factor.
-/

open Matrix Module
open scoped Matrix.Norms.Operator

noncomputable section
namespace OTSelector.Geometry

variable {W V ι : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ W] [FiniteDimensional ℝ V] [Fintype ι] [DecidableEq ι]

omit [FiniteDimensional ℝ W] [FiniteDimensional ℝ V] [DecidableEq ι] in
/-- Actual bilinear pullback has the matrix congruence in the two fixed bases. -/
theorem hamiltonianMatrixA_bilinearComp (bW : Basis ι ℝ W) (bV : Basis ι ℝ V)
    (H : V →L[ℝ] V →L[ℝ] ℝ) (R : W →L[ℝ] V) :
    let J := vectorFamilyMatrix bV (fun j ↦ R (bW j))
    hamiltonianMatrixA bW (H.bilinearComp R R) = Jᵀ * hamiltonianMatrixA bV H * J := by
  ext i j
  change H (R (bW j)) (R (bW i)) = _
  conv_lhs => rw [← bV.sum_repr (R (bW j)), ← bV.sum_repr (R (bW i))]
  simp only [map_sum, _root_.sum_apply, _root_.map_smul, _root_.smul_apply,
    smul_eq_mul, Matrix.mul_apply, Matrix.transpose_apply, vectorFamilyMatrix,
    hamiltonianMatrixA, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k hk
  apply Finset.sum_congr rfl
  intro l hl
  ring

omit [FiniteDimensional ℝ W] in
/-- The true positive Hessian inverse has the dual-to-vector matrix used by the
actual Hamiltonian system. -/
theorem hamiltonianMatrixA_mul_inverse (b : Basis ι ℝ V)
    (H : V →L[ℝ] V →L[ℝ] ℝ) (hH : ∀ v : V, v ≠ 0 → 0 < H v v) :
    hamiltonianMatrixA b H * hamiltonianMatrixC b H.inverse = 1 := by
  let e := positive_dualMap_equiv H hH
  have he : H.inverse = e.symm.toContinuousLinearMap := ContinuousLinearMap.inverse_equiv e
  ext i j
  have hs := congrArg (fun v : V ↦ H v (b i))
    (b.sum_repr (e.symm (basisCovector b j)))
  have hi : H (e.symm (basisCovector b j)) = basisCovector b j := e.apply_symm_apply _
  simpa only [Matrix.mul_apply, hamiltonianMatrixA, hamiltonianMatrixC, he,
    ContinuousLinearEquiv.coe_coe, map_sum, _root_.map_smul, _root_.sum_apply,
    _root_.smul_apply, smul_eq_mul, mul_comm, hi, basisCovector_apply,
    b.repr_self, Finsupp.single_apply, Matrix.one_apply, eq_comm] using hs

omit [FiniteDimensional ℝ W] in
/-- Matrix inversion agrees with the genuine positive Hessian inverse. -/
theorem hamiltonianMatrixA_inverse (b : Basis ι ℝ V)
    (H : V →L[ℝ] V →L[ℝ] ℝ) (hH : ∀ v : V, v ≠ 0 → 0 < H v v) :
    (hamiltonianMatrixA b H)⁻¹ = hamiltonianMatrixC b H.inverse :=
  Matrix.inv_eq_right_inv (hamiltonianMatrixA_mul_inverse b H hH)

omit [FiniteDimensional ℝ W] in
/-- Inverting a positively rescaled actual label Hessian retains the exact clock
factor and the same label basis matrix. -/
theorem inverse_labelHessian_of_graph_congruence
    (bW : Basis ι ℝ W) (bV : Basis ι ℝ V)
    (H : V →L[ℝ] V →L[ℝ] ℝ) (R : W →L[ℝ] V)
    (hH : ∀ v : V, v ≠ 0 → 0 < H v v)
    {K : Matrix ι ι ℝ} {c : ℝ} (hc : c ≠ 0)
    (hK : hamiltonianMatrixA bW (H.bilinearComp R R) = c • K)
    (hJ : (vectorFamilyMatrix bV (fun j ↦ R (bW j))).det ≠ 0) :
    let J := vectorFamilyMatrix bV (fun j ↦ R (bW j))
    K⁻¹ = c • (J⁻¹ * hamiltonianMatrixC bV H.inverse * J⁻¹ᵀ) := by
  let J := vectorFamilyMatrix bV (fun j ↦ R (bW j))
  have hcong : Jᵀ * hamiltonianMatrixA bV H * J = c • K := by
    rw [← hamiltonianMatrixA_bilinearComp bW bV H R]
    exact hK
  have hK' : K = c⁻¹ • (Jᵀ * hamiltonianMatrixA bV H * J) := by
    rw [hcong, smul_smul, inv_mul_cancel₀ hc, one_smul]
  rw [hK']
  apply Matrix.inv_eq_right_inv
  rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, inv_mul_cancel₀ hc, one_smul]
  change (Jᵀ * hamiltonianMatrixA bV H * J) *
    (J⁻¹ * hamiltonianMatrixC bV H.inverse * J⁻¹ᵀ) = 1
  simp only [Matrix.mul_assoc,
    Matrix.mul_nonsing_inv_cancel_left J _ (isUnit_iff_ne_zero.mpr hJ)]
  rw [← Matrix.mul_assoc (hamiltonianMatrixA bV H),
    hamiltonianMatrixA_mul_inverse bV H hH, Matrix.one_mul]
  rw [← Matrix.transpose_mul, Matrix.nonsing_inv_mul J (isUnit_iff_ne_zero.mpr hJ),
    Matrix.transpose_one]

end OTSelector.Geometry

end
end
