import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.LinearAlgebra.Trace
import Mathlib.MeasureTheory.Integral.DivergenceTheorem
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Reconstruction.OriginalOrthonormalCubeDivergence.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Reconstruction.OriginalOrthonormalCubeDivergence`; the selected original proof blocks follow. -/
section

/-!
Conditions: A finite-dimensional orthonormal frame and an actual C1 vector field under a continuous linear coordinate equivalence.

Objects: Divergence invariance between frame coordinates and the raw coordinate current.

Proof detail: Identify the sum of diagonal pairings as the linear trace, use invariance under conjugacy and apply the actual derivative chain rule.

Sources: Jiří Lebl, Section 8.1.3, Propositions 8.1.17–8.1.18, p. 15 (https://www.jirka.org/ra/realanal2.pdf#page=15); Jiří Lebl, Section 8.3, Theorem 8.3.7, p. 38; Exercise 8.3.7, p. 45 (differentiate the inverse identity) (https://www.jirka.org/ra/realanal2.pdf#page=38).
Relation: Basis/trace adapter for divergence. The coordinate map need not be assumed orthogonal when trace conjugacy suffices.
-/

/-! True invariance of divergence between orthonormal physical coordinates and the raw current. -/

open Function
open scoped BigOperators InnerProductSpace

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace OTSelector.Reconstruction

/-- The actual orthonormal diagonal sum is the basis-independent trace. -/
theorem sum_orthonormal_diagonal_eq_trace
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {q : ℕ}
    (b : OrthonormalBasis (Fin q) ℝ E) (L : E →L[ℝ] E) :
    (∑ i : Fin q, ⟪b i, L (b i)⟫_ℝ) = LinearMap.trace ℝ E L.toLinearMap := by
  classical
  rw [LinearMap.trace_eq_matrix_trace ℝ b.toBasis]
  simp only [Matrix.trace, Matrix.diag_apply, LinearMap.toMatrix_apply, OrthonormalBasis.coe_toBasis,
    OrthonormalBasis.coe_toBasis_repr_apply, OrthonormalBasis.repr_apply_apply]
  rfl

/-- The raw coordinate diagonal sum is the same basis-independent trace. -/
theorem sum_raw_coordinate_diagonal_eq_trace {q : ℕ}
    (L : (Fin q → ℝ) →L[ℝ] (Fin q → ℝ)) :
    (∑ k : Fin q, L (Pi.single k 1) k) =
      LinearMap.trace ℝ (Fin q → ℝ) L.toLinearMap := by
  classical
  rw [LinearMap.trace_eq_matrix_trace ℝ (Pi.basisFun ℝ (Fin q))]
  simp only [Matrix.trace, Matrix.diag_apply, LinearMap.toMatrix_apply,
    Pi.basisFun_apply, Pi.basisFun_repr]
  rfl

/-- The actual Fréchet chain rule conjugates a raw current's derivative, and trace conjugation
identifies its physical orthonormal divergence with its original raw coordinate divergence. -/
theorem orthonormal_divergence_conjugate_raw_current
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {q : ℕ}
    (b : OrthonormalBasis (Fin q) ℝ E) (e : E ≃L[ℝ] (Fin q → ℝ))
    {J : (Fin q → ℝ) → (Fin q → ℝ)} (hJ : ContDiff ℝ 1 J) (x : E) :
    (∑ i : Fin q, ⟪b i, fderiv ℝ (fun z ↦ e.symm (J (e z))) x (b i)⟫_ℝ) =
      ∑ k : Fin q, fderiv ℝ J (e x) (Pi.single k 1) k := by
  have hd : HasFDerivAt (fun z ↦ e.symm (J (e z)))
      ((e.symm : (Fin q → ℝ) →L[ℝ] E).comp
        ((fderiv ℝ J (e x)).comp (e : E →L[ℝ] (Fin q → ℝ)))) x := by
    simpa only [Function.comp_def] using e.symm.hasFDerivAt.comp x
      ((hJ.differentiable one_ne_zero (e x)).hasFDerivAt.comp x e.hasFDerivAt)
  have heq : (fderiv ℝ (fun z ↦ e.symm (J (e z))) x).toLinearMap =
      e.symm.toLinearEquiv.conj (fderiv ℝ J (e x)).toLinearMap := by
    rw [hd.fderiv]
    ext v
    rfl
  rw [sum_orthonormal_diagonal_eq_trace, sum_raw_coordinate_diagonal_eq_trace, heq]
  exact LinearMap.trace_conj' _ e.symm.toLinearEquiv

/-- For the literal physical Euclidean realization of the original raw current, the chosen
normal-frame divergence equals the original raw coordinate divergence, with no fitted map. -/
theorem orthonormal_divergence_physical_raw_current
    {q : ℕ} (b : OrthonormalBasis (Fin q) ℝ (EuclideanSpace ℝ (Fin q)))
    {J : (Fin q → ℝ) → (Fin q → ℝ)} (hJ : ContDiff ℝ 1 J)
    (x : EuclideanSpace ℝ (Fin q)) :
    (∑ i : Fin q, ⟪b i, fderiv ℝ (fun z ↦
        (EuclideanSpace.equiv (Fin q) ℝ).symm (J (EuclideanSpace.equiv (Fin q) ℝ z)))
        x (b i)⟫_ℝ) =
      ∑ k : Fin q, fderiv ℝ J (EuclideanSpace.equiv (Fin q) ℝ x) (Pi.single k 1) k :=
  orthonormal_divergence_conjugate_raw_current b (EuclideanSpace.equiv (Fin q) ℝ) hJ x

end OTSelector.Reconstruction

end
end
