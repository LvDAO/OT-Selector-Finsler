import OTSelector.Analysis.ODE.Hamiltonian.MatrixCoordinates
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Geometry.HamiltonianRectangularCoordinates.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Geometry.HamiltonianRectangularCoordinates`; the selected original proof blocks follow. -/
section

/-!
Conditions: Independent ambient basis dimension and variation-column index, with the stated actual Hamiltonian derivatives.

Objects: Rectangular variation matrices and their square column-pairing identities.

Proof detail: Apply dual-coordinate evaluation columnwise and form the rectangular matrix products representing the canonical pairing.

Sources: Jiří Lebl, Section 8.1.3, Propositions 8.1.17–8.1.18, p. 15 (https://www.jirka.org/ra/realanal2.pdf#page=15); Gerald Teschl, Section 2.4, pp. 45–47, equations (2.46)–(2.50), Theorem 2.10 (https://www.mat.univie.ac.at/~gerald/ftp/book-ode/ode.pdf#page=56); Ana Cannas da Silva, Homework 1, Symplectic Linear Algebra, p. 8; Section 2.2, pp. 9–10 (https://people.math.ethz.ch/~acannas/Papers/lsg.pdf#page=16).
Relation: Rectangular coordinate adapter. It does not assert a reduced square Hamiltonian ODE without additional hypotheses.
-/

/-!
# Rectangular coordinates of Hamiltonian variation families

The ambient basis and the finite column index are independent. Vector and covector
columns form d-by-q matrices, while their canonical pairing forms a q-by-q matrix.
The coefficient matrices remain the actual ambient d-by-d Hamiltonian blocks from
`HamiltonianMatrixCoordinates`. No reduced q-dimensional dynamics are asserted.
-/

open Set Matrix Module
open scoped Matrix.Norms.Operator

namespace OTSelector.Geometry

variable {E ι κ : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [Fintype ι]

/-- Rectangular coordinates of vector columns in an arbitrary ambient basis. -/
noncomputable def vectorFamilyRectMatrix (b : Basis ι ℝ E) (J : κ → E) : Matrix ι κ ℝ :=
  fun i j ↦ b.repr (J j) i

/-- Rectangular coordinates of covector columns in the dual ambient basis. -/
noncomputable def covectorFamilyRectMatrix (b : Basis ι ℝ E)
    (P : κ → E →L[ℝ] ℝ) : Matrix ι κ ℝ := fun i j ↦ P j (b i)

omit [FiniteDimensional ℝ E] in
private theorem basis_pairing_sum (b : Basis ι ℝ E) (p : E →L[ℝ] ℝ) (v : E) :
    ∑ i, b.repr v i * p (b i) = p v := by
  simpa only [map_sum, map_smul, smul_eq_mul] using congrArg p (b.sum_repr v)

private theorem sum_basisCovector (b : Basis ι ℝ E) (p : E →L[ℝ] ℝ) :
    ∑ i, p (b i) • basisCovector b i = p := by
  ext v
  simpa only [_root_.sum_apply, _root_.smul_apply,
    basisCovector_apply, smul_eq_mul,
    mul_comm] using basis_pairing_sum b p v

private theorem matrixB_mul_vector (b : Basis ι ℝ E) (B : E →L[ℝ] E) (J : κ → E) :
    hamiltonianMatrixB b B * vectorFamilyRectMatrix b J =
      vectorFamilyRectMatrix b (fun j ↦ B (J j)) := by
  ext i j
  simpa only [Matrix.mul_apply, hamiltonianMatrixB, vectorFamilyRectMatrix,
    basisCovector_apply,
    ContinuousLinearMap.comp_apply, mul_comm] using
    basis_pairing_sum b ((basisCovector b i).comp B) (J j)

private theorem matrixC_mul_covector (b : Basis ι ℝ E)
    (C : (E →L[ℝ] ℝ) →L[ℝ] E) (P : κ → E →L[ℝ] ℝ) :
    hamiltonianMatrixC b C * covectorFamilyRectMatrix b P =
      vectorFamilyRectMatrix b (fun j ↦ C (P j)) := by
  ext i j
  have h := congrArg ((basisCovector b i).comp C) (sum_basisCovector b (P j))
  simpa only [Matrix.mul_apply, hamiltonianMatrixC, covectorFamilyRectMatrix, vectorFamilyRectMatrix,
    map_sum, map_smul, ContinuousLinearMap.comp_apply, basisCovector_apply, smul_eq_mul, mul_comm] using h

omit [FiniteDimensional ℝ E] in
private theorem matrixA_mul_vector (b : Basis ι ℝ E)
    (A : E →L[ℝ] (E →L[ℝ] ℝ)) (J : κ → E) :
    hamiltonianMatrixA b A * vectorFamilyRectMatrix b J =
      covectorFamilyRectMatrix b (fun j ↦ A (J j)) := by
  ext i j
  have h := congrArg (fun v ↦ A v (b i)) (b.sum_repr (J j))
  simpa only [Matrix.mul_apply, hamiltonianMatrixA, vectorFamilyRectMatrix, covectorFamilyRectMatrix,
    map_sum, map_smul, _root_.sum_apply, _root_.smul_apply,
    smul_eq_mul, mul_comm] using h

omit [FiniteDimensional ℝ E] in
private theorem matrixB_transpose_mul_covector (b : Basis ι ℝ E)
    (B : E →L[ℝ] E) (P : κ → E →L[ℝ] ℝ) :
    (hamiltonianMatrixB b B)ᵀ * covectorFamilyRectMatrix b P =
      covectorFamilyRectMatrix b (fun j ↦ (P j).comp B) := by
  ext i j
  exact basis_pairing_sum b (P j) (B (b i))

variable [Fintype κ]

/-- Within derivatives of the actual vector and covector columns imply the two matrix
Hamiltonian equations. This applies to arbitrary time sets, including closed intervals. -/
theorem hasDerivWithinAt_hamiltonian_rectangular_matrices (b : Basis ι ℝ E)
    {J : κ → ℝ → E} {P : κ → ℝ → E →L[ℝ] ℝ}
    {A : E →L[ℝ] (E →L[ℝ] ℝ)} {B : E →L[ℝ] E} {C : (E →L[ℝ] ℝ) →L[ℝ] E}
    {I : Set ℝ} {t : ℝ}
    (hJ : ∀ j, HasDerivWithinAt (J j) (B (J j t) + C (P j t)) I t)
    (hP : ∀ j, HasDerivWithinAt (P j) (-A (J j t) - (P j t).comp B) I t) :
    HasDerivWithinAt (fun s ↦ vectorFamilyRectMatrix b (fun j ↦ J j s))
      (hamiltonianMatrixB b B * vectorFamilyRectMatrix b (fun j ↦ J j t) +
        hamiltonianMatrixC b C * covectorFamilyRectMatrix b (fun j ↦ P j t)) I t ∧
    HasDerivWithinAt (fun s ↦ covectorFamilyRectMatrix b (fun j ↦ P j s))
      (-hamiltonianMatrixA b A * vectorFamilyRectMatrix b (fun j ↦ J j t) -
        (hamiltonianMatrixB b B)ᵀ * covectorFamilyRectMatrix b (fun j ↦ P j t)) I t := by
  rw [matrixB_mul_vector, matrixC_mul_covector, Matrix.neg_mul,
    matrixA_mul_vector, matrixB_transpose_mul_covector]
  constructor
  · apply hasDerivWithinAt_pi.mpr
    intro i
    apply hasDerivWithinAt_pi.mpr
    intro j
    simpa only [vectorFamilyRectMatrix, Matrix.add_apply, basisCovector_apply,
      Function.comp_def, map_add, Finsupp.add_apply] using
      (basisCovector b i).hasFDerivAt.comp_hasDerivWithinAt t (hJ j)
  · apply hasDerivWithinAt_pi.mpr
    intro i
    apply hasDerivWithinAt_pi.mpr
    intro j
    simpa only [covectorFamilyRectMatrix, Matrix.sub_apply, Matrix.neg_apply,
      _root_.sub_apply, _root_.neg_apply,
      ContinuousLinearMap.comp_apply, map_zero, add_zero] using
      (hP j).clm_apply (hasDerivWithinAt_const t I (b i))

omit [FiniteDimensional ℝ E] [Fintype κ] in
/-- Each matrix Wronskian entry is the canonical vector-covector pairing of two columns. -/
theorem rectangular_wronskian_apply (b : Basis ι ℝ E) (J : κ → E)
    (P : κ → E →L[ℝ] ℝ) (i j : κ) :
    ((vectorFamilyRectMatrix b J)ᵀ * covectorFamilyRectMatrix b P -
      (covectorFamilyRectMatrix b P)ᵀ * vectorFamilyRectMatrix b J) i j =
      P j (J i) - P i (J j) := by
  simp only [Matrix.sub_apply, Matrix.mul_apply, Matrix.transpose_apply,
    vectorFamilyRectMatrix, covectorFamilyRectMatrix]
  rw [basis_pairing_sum]
  congr 1
  simpa only [mul_comm] using basis_pairing_sum b (P i) (J j)

end OTSelector.Geometry

end
