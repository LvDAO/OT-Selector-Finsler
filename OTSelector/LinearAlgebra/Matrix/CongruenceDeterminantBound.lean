import Mathlib.Analysis.Matrix.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import OTSelector.LinearAlgebra.Matrix.DeterminantLoewner
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Probability.PhaseDeterminantDomination.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Probability.PhaseDeterminantDomination`; the selected original proof blocks follow. -/
section

/-!
# Probability.PhaseDeterminantDomination

**Conditions:** A fixed finite matrix T, positive-semidefinite varying matrices U, and a scalar Gram bound TᵀT≤cI with c≥1.

**Objects:** Determinants det(I+TUTᵀ), a fixed-frame domination constant and transferred integrability.

**Proof detail:** Use a positive square root and determinant cyclicity to compare Gram forms in Loewner order, then bound det(I+cU) by c^d det(I+U); apply measurable integrable domination.

**Sources:** [Stephen Boyd; Lieven Vandenberghe, Convex Optimization (2004)](https://web.stanford.edu/~boyd/cvxbook/bv_cvxbook.pdf#page=660), Section 2.2.5, p. 34; Section 2.4.1, Example 2.15, p. 43; Appendix A.5.2, pp. 646–647 (spectral decomposition, determinant, definiteness, symmetric square root); [Stephen Boyd; Lieven Vandenberghe, Convex Optimization (2004)](https://web.stanford.edu/~boyd/cvxbook/bv_cvxbook.pdf#page=662), Appendix A.5.1, pp. 645–646 (range/nullspace/rank); A.5.2, p. 647 (positive square root); A.5.4, pp. 648–649 (SVD and the nonzero spectra of A^T A and A A^T); [Sheldon Axler, Measure, Integration & Real Analysis (author PDF, 12 June 2026)](https://measure.axler.net/MIRA.pdf), Section 3A (integration), Theorem 3.31 (dominated convergence); Section 5B, Theorems 5.28/5.32 (Tonelli/Fubini).

Source relation (corollary): The cited sections provide the stated mathematical foundations; the exact finite construction and quantitative bound in this module are local consequences, not a claim that the book states the Lean theorem verbatim.
-/

/-! Fixed anisotropic frames preserve determinant integrability of positive phase legs. -/
open Matrix
open scoped MatrixOrder
noncomputable section
namespace OTSelector.Probability
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A scalar bound on the fixed frame Gram matrix controls every positive phase leg. -/
theorem det_one_add_congruence_le_of_gram_bound
    (T : Matrix ι ι ℝ) {c : ℝ} (hc : 1 ≤ c)
    (hgram : (c • (1 : Matrix ι ι ℝ) - Tᵀ * T).PosSemidef)
    {U : Matrix ι ι ℝ} (hU : U.PosSemidef) :
    det (1 + T * U * Tᵀ) ≤ c ^ Fintype.card ι * det (1 + U) := by
  let S := CFC.sqrt U
  have hS : S.PosSemidef := (CFC.sqrt_nonneg U).posSemidef
  have hSsq : S * S = U := by simpa only [pow_two] using CFC.sq_sqrt U
  let A := (1 : Matrix ι ι ℝ) + S * (Tᵀ * T) * S
  have hinner : (S * (Tᵀ * T) * S).PosSemidef := by
    have h := (posSemidef_conjTranspose_mul_self T).conjTranspose_mul_mul_same S
    simpa only [hS.isHermitian.eq, conjTranspose_eq_transpose_of_trivial] using h
  have hA : A.PosDef := PosDef.one.add_posSemidef hinner
  have hdiff : (c • (1 + U) - A).PosSemidef := by
    have hsmall : ((c - 1) • (1 : Matrix ι ι ℝ)).PosSemidef :=
      PosSemidef.one.smul (sub_nonneg.mpr hc)
    have hconj : (S * (c • 1 - Tᵀ * T) * S).PosSemidef := by
      simpa only [hS.isHermitian.eq] using hgram.conjTranspose_mul_mul_same S
    have hconjEq : S * (c • 1 - Tᵀ * T) * S =
        c • (S * S) - S * (Tᵀ * T) * S := by
      rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one]
    have heq : c • (1 + U) - A =
        (c - 1) • (1 : Matrix ι ι ℝ) + S * (c • 1 - Tᵀ * T) * S := by
      rw [hconjEq, smul_add, ← hSsq]
      dsimp [A]
      module
    rw [heq]
    exact hsmall.add hconj
  have hdetEq : det (1 + T * U * Tᵀ) = det A := by
    calc
      _ = det (1 + (T * S) * (S * Tᵀ)) := by
        congr 1
        rw [← hSsq]
        noncomm_ring
      _ = det (1 + (S * Tᵀ) * (T * S)) := det_one_add_mul_comm _ _
      _ = det A := by congr 1; dsimp [A]; noncomm_ring
  rw [hdetEq]
  have h := det_mono_of_posDef_of_posSemidef_sub hA hdiff
  simpa only [det_smul] using h

/-- Every fixed real frame, including a singular frame, preserves the determinant
moment with one finite constant independent of the positive phase leg. -/
theorem exists_det_one_add_congruence_bound (T : Matrix ι ι ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ U : Matrix ι ι ℝ, U.PosSemidef →
      det (1 + T * U * Tᵀ) ≤ C * det (1 + U) := by
  let c : ℝ := 1 + ∑ i, ∑ j, T i j ^ 2
  have hsum : 0 ≤ ∑ i, ∑ j, T i j ^ 2 :=
    Finset.sum_nonneg (fun _ _ ↦ Finset.sum_nonneg (fun _ _ ↦ sq_nonneg _))
  have hc : 1 ≤ c := by dsimp [c]; linarith
  have hgram : (c • (1 : Matrix ι ι ℝ) - Tᵀ * T).PosSemidef := by
    apply PosSemidef.of_dotProduct_mulVec_nonneg
      ((isHermitian_one.smul (show IsSelfAdjoint c from rfl)).sub
        (by simpa only [conjTranspose_eq_transpose_of_trivial] using
          isHermitian_conjTranspose_mul_self T))
    intro v
    have hsq : 0 ≤ ∑ j, v j ^ 2 := Finset.sum_nonneg (fun _ _ ↦ sq_nonneg _)
    have hrow : ∀ i, (∑ j, T i j * v j) ^ 2 ≤
        (∑ j, T i j ^ 2) * ∑ j, v j ^ 2 := fun i ↦
      Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun j ↦ T i j) v
    have hnorm : (T *ᵥ v) ⬝ᵥ (T *ᵥ v) ≤
        (∑ i, ∑ j, T i j ^ 2) * ∑ j, v j ^ 2 := by
      calc
        _ = ∑ i, (∑ j, T i j * v j) ^ 2 := by simp only [dotProduct, mulVec, pow_two]
        _ ≤ ∑ i, (∑ j, T i j ^ 2) * ∑ j, v j ^ 2 := Finset.sum_le_sum (fun i _ ↦ hrow i)
        _ = _ := (Finset.sum_mul _ _ _).symm
    have hid : v ⬝ᵥ v = ∑ j, v j ^ 2 := by simp only [dotProduct, pow_two]
    have hprod : v ⬝ᵥ ((Tᵀ * T) *ᵥ v) = (T *ᵥ v) ⬝ᵥ (T *ᵥ v) := by
      rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_transpose_mulVec]
    simp only [star_trivial, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
      dotProduct_sub, dotProduct_smul, smul_eq_mul, hid, hprod]
    dsimp [c]
    nlinarith
  refine ⟨c ^ Fintype.card ι, pow_pos (lt_of_lt_of_le zero_lt_one hc) _, ?_⟩
  intro U hU
  exact det_one_add_congruence_le_of_gram_bound T hc hgram hU

/-- A fixed anisotropic frame transports the actual determinant moment without
requiring an additional moment or a positive lower bound on the phase leg. -/
theorem integrable_det_one_add_congruence
    {Ω : Type*} [MeasurableSpace Ω] {μ : MeasureTheory.Measure Ω}
    (T : Matrix ι ι ℝ) {U : Ω → Matrix ι ι ℝ}
    (hm : AEMeasurable U μ)
    (hU : ∀ᵐ x ∂μ, (U x).PosSemidef)
    (hI : MeasureTheory.Integrable (fun x ↦ det (1 + U x)) μ) :
    MeasureTheory.Integrable (fun x ↦ det (1 + T * U x * Tᵀ)) μ := by
  obtain ⟨C, _, hbound⟩ := exists_det_one_add_congruence_bound T
  have hc : Continuous (fun A : Matrix ι ι ℝ ↦ det (1 + T * A * Tᵀ)) := by fun_prop
  apply (hI.const_mul C).mono_nonneg (hc.measurable.comp_aemeasurable hm).aestronglyMeasurable
  · filter_upwards [hU] with x hx
    have hpos := PosSemidef.one.add (hx.mul_mul_conjTranspose_same T)
    simpa only [conjTranspose_eq_transpose_of_trivial, RCLike.re_to_real,
      Function.comp_apply] using (RCLike.nonneg_iff.mp hpos.det_nonneg).1
  · filter_upwards [hU] with x hx
    exact hbound (U x) hx

end OTSelector.Probability

end
end
