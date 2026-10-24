import OTSelector.Reconstruction.OriginalSeedPairCoefficient

/-!
# Bounds for positive compliance matrices

Matrix inversion reverses positive semidefinite comparison. A trace bound on
positive semidefinite inverse coefficients controls their fixed operator norm.
-/

open Set Matrix MeasureTheory
open scoped Topology Matrix.Norms.Operator

noncomputable section
namespace OTSelector.Reconstruction

set_option backward.isDefEq.respectTransparency false

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Positive definite inversion reverses the semidefinite comparison. -/
theorem posSemidef_inverse_sub_inverse {A B : Matrix n n ℝ}
    (hA : A.PosDef) (hB : B.PosDef) (hBA : (B - A).PosSemidef) :
    (A⁻¹ - B⁻¹).PosSemidef := by
  let := hA.isUnit.invertible
  let := hB.isUnit.invertible
  have h := (hA.posSemidef.conjTranspose_mul_mul_same (A⁻¹ - B⁻¹)).add
    (hBA.conjTranspose_mul_mul_same B⁻¹)
  have heq : (A⁻¹ - B⁻¹)ᴴ * A * (A⁻¹ - B⁻¹) + B⁻¹ᴴ * (B - A) * B⁻¹ =
      A⁻¹ - B⁻¹ := by
    rw [conjTranspose_sub, hA.inv.isHermitian.eq, hB.inv.isHermitian.eq]
    simp only [mul_sub, sub_mul, Matrix.mul_assoc, Matrix.mul_inv_of_invertible,
      Matrix.inv_mul_cancel_left_of_invertible, Matrix.mul_one]
    abel
  rwa [heq] at h

/-- Every entry of a positive semidefinite real matrix is bounded by its trace. -/
theorem abs_entry_le_trace_of_posSemidef {A : Matrix n n ℝ} (hA : A.PosSemidef) (i j : n) :
    |A i j| ≤ A.trace := by
  have hp := hA.dotProduct_mulVec_nonneg (Pi.single i 1 + Pi.single j 1)
  have hm := hA.dotProduct_mulVec_nonneg (Pi.single i 1 - Pi.single j 1)
  have hsym : A j i = A i j := by simpa using hA.isHermitian.apply i j
  simp only [star_trivial, mulVec_add, mulVec_sub,
    dotProduct_add, dotProduct_sub, add_dotProduct, sub_dotProduct,
    single_dotProduct, mulVec_single, one_mul, MulOpposite.op_one, one_smul,
    Matrix.col_apply, hsym] at hp hm
  have hi : A i i ≤ A.trace := by
    exact Finset.single_le_sum (f := fun k ↦ A k k)
      (fun k _ ↦ hA.diag_nonneg) (Finset.mem_univ i)
  have hj : A j j ≤ A.trace := by
    exact Finset.single_le_sum (f := fun k ↦ A k k)
      (fun k _ ↦ hA.diag_nonneg) (Finset.mem_univ j)
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- A common trace bound controls any fixed matrix norm, without an endpoint rank condition. -/
theorem exists_norm_bound_of_posSemidef_trace_le (C : ℝ) :
    ∃ R ≥ 0, ∀ A : Matrix n n ℝ, A.PosSemidef → A.trace ≤ C → ‖A‖ ≤ R := by
  let box : Set (Matrix n n ℝ) := Set.pi univ (fun _ ↦ Set.pi univ (fun _ ↦ Icc (-C) C))
  have hc : IsCompact box := isCompact_univ_pi (fun _ ↦ isCompact_univ_pi (fun _ ↦ isCompact_Icc))
  have hb : ∃ R, ∀ A ∈ box, ‖A‖ ≤ R :=
    hc.exists_bound_of_continuousOn
      (f := fun A : Matrix n n ℝ ↦ A) continuous_id.continuousOn
  obtain ⟨R, hR⟩ := hb
  refine ⟨max R 0, le_max_right _ _, fun A hA hC ↦ (hR A ?_).trans (le_max_left _ _)⟩
  intro i _ j _
  exact abs_le.mp ((abs_entry_le_trace_of_posSemidef hA i j).trans hC)

end OTSelector.Reconstruction
