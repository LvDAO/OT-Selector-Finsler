import OTSelector.Analysis.Calculus.Variational.EndpointJacobiCompliance
import OTSelector.Analysis.ODE.Hamiltonian.MatrixCoordinates
import OTSelector.LinearAlgebra.Matrix.LabelHessianMatrix
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Geometry.FinslerIntrinsicCostCoefficientMatrix.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Geometry.FinslerIntrinsicCostCoefficientMatrix`; the selected original proof blocks follow. -/
section

/-!
Conditions: An integrable/continuous operator family and fixed bases or continuous linear readouts, with the stated inverses.

Objects: Coordinates of the actual interval-integrated compliance and its pairing/inverse matrix identities.

Proof detail: Commute bounded linear readouts with the integral, expand coordinates and simplify the actual inverse identities.

Sources: Jiří Lebl, Section 9.1, Theorem 9.1.1 (Leibniz integral rule), Exercise 9.1.5 (several parameters) (https://www.jirka.org/ra/html/sec_diffunderint.html); D. H. Fremlin, Exercises 253Y(f)(i)–(vii), 253Y(g)–(h), pp. 46–47: Banach-valued L1, bounded bilinear maps and section integrals (https://www1.essex.ac.uk/maths/people/fremlin/chap25.pdf#page=46); Jiří Lebl, Section 8.1.3, Propositions 8.1.17–8.1.18, p. 15 (https://www.jirka.org/ra/realanal2.pdf#page=15).
Relation: Finite-dimensional integral-coordinate adapter; the integral remains the actual operator integral.
-/

/-!
# Fixed-basis matrices of the actual compliance integral

The same fixed label basis commutes with the actual operator integral. Its matrix
inverse therefore gives the original inverse-compliance quadratic coefficient.
-/

open Set MeasureTheory Matrix Module
open scoped Topology Matrix.Norms.Operator

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OTSelector.Geometry

variable {W ι : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [FiniteDimensional ℝ W] [Fintype ι] [DecidableEq ι]

local instance : ENormedAddMonoid ((W →L[ℝ] ℝ) →L[ℝ] W) := by
  exact_mod_cast (NormedAddGroup.toENormedAddMonoid (F := (W →L[ℝ] ℝ) →L[ℝ] W))

/-- Reading a dual-to-vector response in a fixed basis is a continuous linear operation. -/
def hamiltonianMatrixCLinear (b : Basis ι ℝ W) :
    ((W →L[ℝ] ℝ) →L[ℝ] W) →L[ℝ] Matrix ι ι ℝ :=
  LinearMap.toContinuousLinearMap {
    toFun := hamiltonianMatrixC b
    map_add' := by intros; ext i j; simp [hamiltonianMatrixC]
    map_smul' := by intros; ext i j; simp [hamiltonianMatrixC] }

/-- Fixed-basis coordinates commute with the genuine compliance integral. -/
theorem hamiltonianMatrixC_endpointCompliance (b : Basis ι ℝ W)
    {C : ℝ → (W →L[ℝ] ℝ) →L[ℝ] W} {a b' : ℝ}
    (hab : a ≤ b') (hC : ContinuousOn C (Icc a b')) :
    hamiltonianMatrixC b (endpointCompliance C a b') =
      ∫ t in a..b', hamiltonianMatrixC b (C t) := by
  have hi : IntervalIntegrable C volume a b' := by
    simpa using! (ContinuousOn.intervalIntegrable_of_Icc (u := C) (μ := volume) hab
      (by exact_mod_cast hC))
  simpa only [hamiltonianMatrixCLinear, endpointCompliance] using!
    (ContinuousLinearMap.intervalIntegral_comp_comm (𝕜 := ℝ)
      (E := (W →L[ℝ] ℝ) →L[ℝ] W) (F := Matrix ι ι ℝ)
      (by exact_mod_cast hamiltonianMatrixCLinear b) (f := C)
      (a := a) (b := b') (μ := volume) (by exact_mod_cast hi)).symm

/-- An actual positive response integral has the inverse matrix of its fixed-basis integral. -/
theorem endpointCompliance_inverse_matrix (b : Basis ι ℝ W)
    {C : ℝ → (W →L[ℝ] ℝ) →L[ℝ] W} {a b' : ℝ}
    (hab : a < b') (hC : ContinuousOn C (Icc a b'))
    (hpos : ∀ t ∈ Icc a b', ∀ p : W →L[ℝ] ℝ, p ≠ 0 → 0 < p (C t p)) :
    hamiltonianMatrixA b (endpointCompliance C a b').inverse =
      (∫ t in a..b', hamiltonianMatrixC b (C t))⁻¹ := by
  have hS := endpointCompliance_isInvertible hab hC hpos
  have hm := hamiltonianMatrixA_mul_inverse b (endpointCompliance C a b').inverse
    (fun v hv ↦ endpointCompliance_inverse_pos hab hC hpos hv)
  rw [hS.inverse_inverse] at hm
  rw [← hamiltonianMatrixC_endpointCompliance b hab.le hC]
  exact (Matrix.inv_eq_left_inv hm).symm

omit [FiniteDimensional ℝ W] [DecidableEq ι] in
/-- A bilinear form evaluated on vectors is its actual fixed-basis matrix pairing. -/
theorem hamiltonianMatrixA_pairing (b : Basis ι ℝ W)
    (H : W →L[ℝ] W →L[ℝ] ℝ) (u v : W) :
    H u v = b.equivFun v ⬝ᵥ (hamiltonianMatrixA b H *ᵥ b.equivFun u) := by
  conv_lhs => rw [← b.sum_repr u, ← b.sum_repr v]
  simp only [map_sum, _root_.sum_apply, _root_.map_smul, _root_.smul_apply,
    smul_eq_mul, dotProduct, Matrix.mulVec, hamiltonianMatrixA, Finset.mul_sum,
    Basis.equivFun_apply]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

/-- The real coefficient of the actual inverse compliance is given by the same
integrated response matrix, with the fixed label basis retained. -/
theorem endpointCompliance_inverse_pairing_matrix (b : Basis ι ℝ W)
    {C : ℝ → (W →L[ℝ] ℝ) →L[ℝ] W} {a b' : ℝ}
    (hab : a < b') (hC : ContinuousOn C (Icc a b'))
    (hpos : ∀ t ∈ Icc a b', ∀ p : W →L[ℝ] ℝ, p ≠ 0 → 0 < p (C t p))
    (u v : W) :
    (endpointCompliance C a b').inverse u v =
      b.equivFun v ⬝ᵥ ((∫ t in a..b', hamiltonianMatrixC b (C t))⁻¹ *ᵥ b.equivFun u) := by
  rw [hamiltonianMatrixA_pairing b, endpointCompliance_inverse_matrix b hab hC hpos]

end OTSelector.Geometry

end
end
