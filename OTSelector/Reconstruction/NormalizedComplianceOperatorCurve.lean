import OTSelector.Reconstruction.NormalizedComplianceCurve

/-!
# Original compliance as an operator curve

The fixed-coordinate matrix integral is the very same continuous linear map on
phase position. Its norm and difference norm agree with the matrix operator norm.
-/

open Set Matrix MeasureTheory
open scoped Topology Matrix.Norms.Operator
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option linter.unusedSectionVars false

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The unchanged matrix acting on the actual phase position space. -/
def matrixPhaseOperator (A : Matrix ι ι ℝ) : (ι → ℝ) →L[ℝ] (ι → ℝ) :=
  A.mulVecLin.toContinuousLinearMap

theorem matrixPhaseOperator_apply (A : Matrix ι ι ℝ) (v : ι → ℝ) :
    matrixPhaseOperator A v = A *ᵥ v := rfl

theorem norm_matrixPhaseOperator (A : Matrix ι ι ℝ) : ‖matrixPhaseOperator A‖ = ‖A‖ := by
  exact (Matrix.linfty_opNorm_eq_opNorm A).symm

theorem matrixPhaseOperator_sub (A B : Matrix ι ι ℝ) :
    matrixPhaseOperator (A - B) = matrixPhaseOperator A - matrixPhaseOperator B := by
  ext v i
  simp [matrixPhaseOperator_apply, Matrix.sub_mulVec]

/-- The true matrix bound passes to the actual continuous linear operator. -/
theorem norm_matrixPhaseOperator_sub (A B : Matrix ι ι ℝ) :
    ‖matrixPhaseOperator A - matrixPhaseOperator B‖ = ‖A - B‖ := by
  rw [← matrixPhaseOperator_sub, norm_matrixPhaseOperator]

/-- One genuine normalized compliance family, interpreted as operators. -/
def normalizedComplianceOperatorCurve (W : ℝ → Matrix ι ι ℝ) (T : Matrix ι ι ℝ)
    (c ell r : ℝ) : (ι → ℝ) →L[ℝ] (ι → ℝ) :=
  matrixPhaseOperator (normalizedComplianceCurve W T c ell r)

/-- The same operator family starts from zero and has the genuine uniform and speed bounds. -/
theorem normalizedComplianceOperatorCurve_bounds
    (W : ℝ → Matrix ι ι ℝ) (T : Matrix ι ι ℝ) {c ell t B : ℝ}
    (ht : 0 < t) (hB : 0 ≤ B) (hW : ContinuousOn W (uIcc c (c + ell)))
    (hbound : ∀ u ∈ uIcc c (c + ell), ‖t • (T * W u * Tᵀ)‖ ≤ B) :
    normalizedComplianceOperatorCurve W T c ell 0 = 0 ∧
      (∀ r ∈ Icc (0 : ℝ) 1, ‖normalizedComplianceOperatorCurve W T c ell r‖ ≤
        B * |ell| / t) ∧
      ∀ r ∈ Icc (0 : ℝ) 1, ∀ s ∈ Icc (0 : ℝ) 1,
        ‖normalizedComplianceOperatorCurve W T c ell r -
          normalizedComplianceOperatorCurve W T c ell s‖ ≤
            (B * |ell| / t) * |r - s| := by
  refine ⟨?_, ?_, ?_⟩
  · ext v i
    simp [normalizedComplianceOperatorCurve, normalizedComplianceCurve_zero,
      matrixPhaseOperator_apply]
  · intro r hr
    rw [normalizedComplianceOperatorCurve, norm_matrixPhaseOperator]
    exact norm_normalizedComplianceCurve_le W T ht hB hW hbound hr
  · intro r hr s hs
    rw [normalizedComplianceOperatorCurve, normalizedComplianceOperatorCurve,
      norm_matrixPhaseOperator_sub]
    exact norm_normalizedComplianceCurve_sub_le W T ht hB hW hbound hr hs

end OTSelector.Reconstruction
