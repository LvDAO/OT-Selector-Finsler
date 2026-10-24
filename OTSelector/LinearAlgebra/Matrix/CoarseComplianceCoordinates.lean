import Mathlib.Analysis.Matrix.MeasurableSpace
import Mathlib.Analysis.Matrix.Order
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import OTSelector.LinearAlgebra.Matrix.ComplianceCongruenceCovariance
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Reconstruction.CoarseCompliancePhase.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Reconstruction.CoarseCompliancePhase`; the selected original proof blocks follow. -/
section

/-!
# Reconstruction.CoarseCompliancePhase

**Conditions:** An invertible real spatial frame T and a nonzero scalar coarse scale.

**Objects:** Paired position/momentum coordinates preserving the same original source and target points.

**Proof detail:** Transform compliance by TUTᵀ and momentum by inverse transpose, cancel the scalar and inverse factors in the path-offset identity, and use determinant multiplicativity for frame invertibility.

**Sources:** [Stephen Boyd; Lieven Vandenberghe, Convex Optimization (2004)](https://web.stanford.edu/~boyd/cvxbook/bv_cvxbook.pdf#page=662), Appendix A.5.1, pp. 645–646 (range/nullspace/rank); A.5.2, p. 647 (positive square root); A.5.4, pp. 648–649 (SVD and the nonzero spectra of A^T A and A A^T); [Terence Tao, Analysis I](https://github.com/teorth/analysis/blob/main/Analysis/Section_7_1.lean), Sections 4.3 (absolute value) and 7.1 (finite series), in particular Proposition 7.1.11.

Source relation (corollary): The cited sections provide the stated mathematical foundations; the exact finite construction and quantitative bound in this module are local consequences, not a claim that the book states the Lean theorem verbatim.
-/

/-!
# Exact coarse anisotropic coordinates retain the same original source point

Position and momentum use the paired contragredient changes of variables. The
single scalar coarse scale cancels exactly, while the physical source envelope
has the original Jacobian of its true spatial frame.
-/
open Set Function Matrix MeasureTheory
open scoped Topology
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The physical spatial frame of a genuine nonzero coarse anisotropic scale is invertible. -/
theorem isUnit_det_coarsePhaseFrame (T : Matrix ι ι ℝ) [Invertible T]
    {ℓ : ℝ} (hℓ : ℓ ≠ 0) : IsUnit (ℓ • T⁻¹).det := by
  rw [Matrix.det_smul, Matrix.det_nonsing_inv, Ring.inverse_eq_inv, isUnit_iff_ne_zero]
  exact mul_ne_zero (pow_ne_zero _ hℓ)
    (inv_ne_zero (isUnit_iff_ne_zero.mp (Matrix.isUnit_det_of_invertible T)))

/-- The actual source x=z-Up is exactly unchanged by the coarse phase normalization. -/
theorem coarsePhaseFrame_source_identity (T U : Matrix ι ι ℝ) [Invertible T]
    {ℓ : ℝ} (hℓ : ℓ ≠ 0) (z p : ι → ℝ) :
    (ℓ • T⁻¹) *ᵥ ((ℓ⁻¹ • (T *ᵥ z)) -
      (T * U * Tᵀ) *ᵥ (ℓ⁻¹ • ((Tᵀ)⁻¹ *ᵥ p))) = z - U *ᵥ p := by
  have hinner : (ℓ⁻¹ • (T *ᵥ z)) -
      (T * U * Tᵀ) *ᵥ (ℓ⁻¹ • ((Tᵀ)⁻¹ *ᵥ p)) =
      ℓ⁻¹ • (T *ᵥ (z - U *ᵥ p)) := by
    rw [Matrix.mulVec_smul, compliance_congruence_path_offset, ← smul_sub,
      ← Matrix.mulVec_sub]
  rw [hinner, Matrix.smul_mulVec, Matrix.mulVec_smul, smul_smul,
    mul_inv_cancel₀ hℓ, one_smul, Matrix.mulVec_mulVec,
    Matrix.inv_mul_of_invertible, Matrix.one_mulVec]

/-- The same paired normalization retains the unchanged actual target z+Vp. -/
theorem coarsePhaseFrame_target_identity (T V : Matrix ι ι ℝ) [Invertible T]
    {ℓ : ℝ} (hℓ : ℓ ≠ 0) (z p : ι → ℝ) :
    (ℓ • T⁻¹) *ᵥ ((ℓ⁻¹ • (T *ᵥ z)) +
      (T * V * Tᵀ) *ᵥ (ℓ⁻¹ • ((Tᵀ)⁻¹ *ᵥ p))) = z + V *ᵥ p := by
  have h := coarsePhaseFrame_source_identity T V hℓ z (-p)
  simpa only [Matrix.mulVec_neg, smul_neg, sub_neg_eq_add] using h

end OTSelector.Reconstruction

end
end
