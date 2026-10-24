import Mathlib.Analysis.Matrix.Normed
import OTSelector.Analysis.Convex.Legendre.Parametric
import OTSelector.Geometry.Finsler.Hamiltonian.Basic
import OTSelector.Geometry.Finsler.Hamiltonian.Hessian
import OTSelector.Geometry.Finsler.Jacobi.VariationalFlow
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Geometry.HamiltonianMatrixCoordinates.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Geometry.HamiltonianMatrixCoordinates`; the selected original proof blocks follow. -/
section

/-!
Conditions: Specified vector/covector dual bases and actual derivatives of a Hamiltonian variation.

Objects: Coordinate action, transpose and pairing identities and the matrix variational equations.

Proof detail: Expand both vector and covector evaluations in the dual bases and apply the actual linearized phase equation column by column.

Sources: Jiří Lebl, Section 8.1.3, Propositions 8.1.17–8.1.18, p. 15 (https://www.jirka.org/ra/realanal2.pdf#page=15); Gerald Teschl, Section 2.4, pp. 45–47, equations (2.46)–(2.50), Theorem 2.10 (https://www.mat.univie.ac.at/~gerald/ftp/book-ode/ode.pdf#page=56); Ana Cannas da Silva, Homework 1, Symplectic Linear Algebra, p. 8; Section 2.2, pp. 9–10 (https://people.math.ethz.ch/~acannas/Papers/lsg.pdf#page=16).
Relation: Basis-level adapters; no inner-product identification or dimension reduction is assumed.
-/

/-!
# Finite-basis coordinates of actual Hamiltonian variations

An arbitrary finite basis of the real model space gives vector coordinates and dual
covector coordinates. The canonical Hamiltonian block equations then become the matrix
equations used by `JacobiCancellation`, with the dual action represented by a transpose.
The final bridge applies this calculation to actual initial-state derivatives of a
Hamiltonian flow. No inner product, transverse reduction, or distance Hessian is chosen.
-/

open Set Matrix Module
open scoped ContDiff Matrix.Norms.Operator

namespace OTSelector.Geometry

variable {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [Fintype ι]

/-- The continuous coordinate covector associated with a finite basis. -/
noncomputable def basisCovector (b : Basis ι ℝ E) (i : ι) : E →L[ℝ] ℝ :=
  (b.coord i).toContinuousLinearMap

omit [Fintype ι] in
/-- A coordinate covector evaluates to the corresponding basis coefficient. -/
@[simp] theorem basisCovector_apply (b : Basis ι ℝ E) (i : ι) (v : E) :
    basisCovector b i v = b.repr v i := rfl

/-- The columns are the coordinates of a family of vectors. -/
noncomputable def vectorFamilyMatrix (b : Basis ι ℝ E) (J : ι → E) : Matrix ι ι ℝ :=
  fun i j ↦ b.repr (J j) i

/-- The columns are covector values on basis vectors. -/
noncomputable def covectorFamilyMatrix (b : Basis ι ℝ E) (P : ι → E →L[ℝ] ℝ) : Matrix ι ι ℝ :=
  fun i j ↦ P j (b i)

/-- Coordinates of the vector-to-covector Hamiltonian block. -/
noncomputable def hamiltonianMatrixA (b : Basis ι ℝ E) (A : E →L[ℝ] (E →L[ℝ] ℝ)) :
    Matrix ι ι ℝ := fun i j ↦ A (b j) (b i)

/-- Coordinates of the vector-to-vector Hamiltonian block. -/
noncomputable def hamiltonianMatrixB (b : Basis ι ℝ E) (B : E →L[ℝ] E) :
    Matrix ι ι ℝ := fun i j ↦ b.repr (B (b j)) i

/-- Coordinates of the covector-to-vector Hamiltonian block in the dual basis. -/
noncomputable def hamiltonianMatrixC (b : Basis ι ℝ E)
    (C : (E →L[ℝ] ℝ) →L[ℝ] E) : Matrix ι ι ℝ :=
  fun i j ↦ b.repr (C (basisCovector b j)) i

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

private theorem matrixB_mul_vector (b : Basis ι ℝ E) (B : E →L[ℝ] E) (J : ι → E) :
    hamiltonianMatrixB b B * vectorFamilyMatrix b J =
      vectorFamilyMatrix b (fun j ↦ B (J j)) := by
  ext i j
  simpa only [Matrix.mul_apply, hamiltonianMatrixB, vectorFamilyMatrix,
    basisCovector_apply,
    ContinuousLinearMap.comp_apply, mul_comm] using
    basis_pairing_sum b ((basisCovector b i).comp B) (J j)

private theorem matrixC_mul_covector (b : Basis ι ℝ E)
    (C : (E →L[ℝ] ℝ) →L[ℝ] E) (P : ι → E →L[ℝ] ℝ) :
    hamiltonianMatrixC b C * covectorFamilyMatrix b P =
      vectorFamilyMatrix b (fun j ↦ C (P j)) := by
  ext i j
  have h := congrArg ((basisCovector b i).comp C) (sum_basisCovector b (P j))
  simpa only [Matrix.mul_apply, hamiltonianMatrixC, covectorFamilyMatrix, vectorFamilyMatrix,
    map_sum, map_smul, ContinuousLinearMap.comp_apply, basisCovector_apply, smul_eq_mul, mul_comm] using h

omit [FiniteDimensional ℝ E] in
private theorem matrixA_mul_vector (b : Basis ι ℝ E)
    (A : E →L[ℝ] (E →L[ℝ] ℝ)) (J : ι → E) :
    hamiltonianMatrixA b A * vectorFamilyMatrix b J =
      covectorFamilyMatrix b (fun j ↦ A (J j)) := by
  ext i j
  have h := congrArg (fun v ↦ A v (b i)) (b.sum_repr (J j))
  simpa only [Matrix.mul_apply, hamiltonianMatrixA, vectorFamilyMatrix, covectorFamilyMatrix,
    map_sum, map_smul, _root_.sum_apply, _root_.smul_apply,
    smul_eq_mul, mul_comm] using h

omit [FiniteDimensional ℝ E] in
private theorem matrixB_transpose_mul_covector (b : Basis ι ℝ E)
    (B : E →L[ℝ] E) (P : ι → E →L[ℝ] ℝ) :
    (hamiltonianMatrixB b B)ᵀ * covectorFamilyMatrix b P =
      covectorFamilyMatrix b (fun j ↦ (P j).comp B) := by
  ext i j
  exact basis_pairing_sum b (P j) (B (b i))

omit [FiniteDimensional ℝ E] [Fintype ι] in
/-- Canonical symmetry of the vector-to-covector block gives a symmetric matrix. -/
theorem hamiltonianMatrixA_transpose (b : Basis ι ℝ E)
    {A : E →L[ℝ] (E →L[ℝ] ℝ)} (hA : ∀ v w, A v w = A w v) :
    (hamiltonianMatrixA b A)ᵀ = hamiltonianMatrixA b A := by
  ext i j
  exact hA (b i) (b j)

omit [Fintype ι] in
/-- Canonical symmetry on the dual space gives a symmetric momentum matrix. -/
theorem hamiltonianMatrixC_transpose (b : Basis ι ℝ E)
    {C : (E →L[ℝ] ℝ) →L[ℝ] E}
    (hC : ∀ p q : E →L[ℝ] ℝ, q (C p) = p (C q)) :
    (hamiltonianMatrixC b C)ᵀ = hamiltonianMatrixC b C := by
  ext i j
  exact hC (basisCovector b i) (basisCovector b j)

/-- Within derivatives of the actual vector and covector columns imply the two matrix
Hamiltonian equations. This applies to arbitrary time sets, including closed intervals. -/
theorem hasDerivWithinAt_hamiltonian_family_matrices (b : Basis ι ℝ E)
    {J : ι → ℝ → E} {P : ι → ℝ → E →L[ℝ] ℝ}
    {A : E →L[ℝ] (E →L[ℝ] ℝ)} {B : E →L[ℝ] E} {C : (E →L[ℝ] ℝ) →L[ℝ] E}
    {I : Set ℝ} {t : ℝ}
    (hJ : ∀ j, HasDerivWithinAt (J j) (B (J j t) + C (P j t)) I t)
    (hP : ∀ j, HasDerivWithinAt (P j) (-A (J j t) - (P j t).comp B) I t) :
    HasDerivWithinAt (fun s ↦ vectorFamilyMatrix b (fun j ↦ J j s))
      (hamiltonianMatrixB b B * vectorFamilyMatrix b (fun j ↦ J j t) +
        hamiltonianMatrixC b C * covectorFamilyMatrix b (fun j ↦ P j t)) I t ∧
    HasDerivWithinAt (fun s ↦ covectorFamilyMatrix b (fun j ↦ P j s))
      (-hamiltonianMatrixA b A * vectorFamilyMatrix b (fun j ↦ J j t) -
        (hamiltonianMatrixB b B)ᵀ * covectorFamilyMatrix b (fun j ↦ P j t)) I t := by
  rw [matrixB_mul_vector, matrixC_mul_covector, Matrix.neg_mul,
    matrixA_mul_vector, matrixB_transpose_mul_covector]
  constructor
  · apply hasDerivWithinAt_pi.mpr
    intro i
    apply hasDerivWithinAt_pi.mpr
    intro j
    simpa only [vectorFamilyMatrix, Matrix.add_apply, basisCovector_apply,
      Function.comp_def, map_add, Finsupp.add_apply] using
      (basisCovector b i).hasFDerivAt.comp_hasDerivWithinAt t (hJ j)
  · apply hasDerivWithinAt_pi.mpr
    intro i
    apply hasDerivWithinAt_pi.mpr
    intro j
    simpa only [covectorFamilyMatrix, Matrix.sub_apply, Matrix.neg_apply,
      _root_.sub_apply, _root_.neg_apply,
      ContinuousLinearMap.comp_apply, map_zero, add_zero] using
      (hP j).clm_apply (hasDerivWithinAt_const t I (b i))

omit [FiniteDimensional ℝ E] in
/-- Each matrix Wronskian entry is the canonical vector-covector pairing of two columns. -/
theorem matrix_wronskian_apply (b : Basis ι ℝ E) (J : ι → E)
    (P : ι → E →L[ℝ] ℝ) (i j : ι) :
    ((vectorFamilyMatrix b J)ᵀ * covectorFamilyMatrix b P -
      (covectorFamilyMatrix b P)ᵀ * vectorFamilyMatrix b J) i j =
      P j (J i) - P i (J j) := by
  simp only [Matrix.sub_apply, Matrix.mul_apply, Matrix.transpose_apply,
    vectorFamilyMatrix, covectorFamilyMatrix]
  rw [basis_pairing_sum]
  congr 1
  simpa only [mul_comm] using basis_pairing_sum b (P i) (J j)

/-- The matrices formed from actual initial-state Fréchet derivatives of the same
Hamiltonian flow satisfy the genuine matrix system, with symmetric actual Hessian blocks. -/
theorem hasDerivWithinAt_hamiltonianFlowVariation_matrices (b : Basis ι ℝ E)
    {L : E × E → ℝ} {e : OpenPartialHomeomorph (E × E) (E × (E →L[ℝ] ℝ))}
    (he : (e : (E × E) → (E × (E →L[ℝ] ℝ))) = parametricLegendre L)
    (hL : ContDiffOn ℝ ∞ L e.source) (hG : ContDiffOn ℝ ∞ e.symm e.target)
    {Φ : (E × (E →L[ℝ] ℝ)) × ℝ → E × (E →L[ℝ] ℝ)}
    {p : E × (E →L[ℝ] ℝ)} {δ : ι → E × (E →L[ℝ] ℝ)} {I : Set ℝ} {t : ℝ}
    (ht : Φ (p, t) ∈ e.target)
    (hvar : ∀ j, HasDerivWithinAt (fun s ↦ fderiv ℝ (fun q ↦ Φ (q, s)) p (δ j))
      (fderiv ℝ (localHamiltonianVectorField L e) (Φ (p, t))
        (fderiv ℝ (fun q ↦ Φ (q, t)) p (δ j))) I t) :
    let J := fun s ↦ vectorFamilyMatrix b (fun j ↦ flowPositionVariation Φ p (δ j) s)
    let P := fun s ↦ covectorFamilyMatrix b (fun j ↦ flowMomentumVariation Φ p (δ j) s)
    let A := hamiltonianMatrixA b (localHamiltonianBlockA L e (Φ (p, t)))
    let B := hamiltonianMatrixB b (localHamiltonianBlockB L e (Φ (p, t)))
    let C := hamiltonianMatrixC b (localHamiltonianBlockC L e (Φ (p, t)))
    HasDerivWithinAt J (B * J t + C * P t) I t ∧
      HasDerivWithinAt P (-A * J t - Bᵀ * P t) I t ∧ Aᵀ = A ∧ Cᵀ = C := by
  dsimp only
  have hd := hasDerivWithinAt_hamiltonian_family_matrices b
    (fun j ↦ (hasDerivWithinAt_hamiltonianFlowVariation_blocks he hL hG ht (hvar j)).1)
    (fun j ↦ (hasDerivWithinAt_hamiltonianFlowVariation_blocks he hL hG ht (hvar j)).2)
  exact ⟨hd.1, hd.2,
    hamiltonianMatrixA_transpose b (localHamiltonianBlockA_symm he hL hG ht),
    hamiltonianMatrixC_transpose b (localHamiltonianBlockC_symm he hL hG ht)⟩

end OTSelector.Geometry

end
