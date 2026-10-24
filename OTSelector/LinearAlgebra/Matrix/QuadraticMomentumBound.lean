import OTSelector.LinearAlgebra.Matrix.CompactPositiveQuadratic
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Reconstruction.MarkedStationaryValueLegalMomentumQuadratic.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Reconstruction.MarkedStationaryValueLegalMomentumQuadratic`; the selected original proof blocks follow. -/
section

/-!
# Reconstruction.MarkedStationaryValueLegalMomentumQuadratic

**Conditions:** A positive-semidefinite real finite matrix and, for the norm estimate, its explicit quadratic upper bound.

**Objects:** The actual matrix momentum Av and its component/norm squared energy control.

**Proof detail:** Positivity of the quadratic in v+t ei gives the component Cauchy–Schwarz bound; use the upper bound on diagonal directions and finite-coordinate norm comparison to obtain the stated constant.

**Sources:** [Stephen Boyd; Lieven Vandenberghe, Convex Optimization (2004)](https://web.stanford.edu/~boyd/cvxbook/bv_cvxbook.pdf#page=660), Section 2.2.5, p. 34; Section 2.4.1, Example 2.15, p. 43; Appendix A.5.2, pp. 646–647 (spectral decomposition, determinant, definiteness, symmetric square root); [Terence Tao, An Epsilon of Room, I: Real Analysis (author preliminary version)](https://terrytao.wordpress.com/wp-content/uploads/2012/12/gsm-117-tao3-epsilon1.pdf#page=57), Section 1.4, Lemma 1.4.7 (Cauchy–Schwarz inequality), p. 48.

Source relation (corollary): The cited sections provide the stated mathematical foundations; the exact finite construction and quantitative bound in this module are local consequences, not a claim that the book states the Lean theorem verbatim.
-/

/-!
# Weighted quadratic energy controls the actual momentum

A positive semidefinite matrix bounds each component of its momentum by its
diagonal coefficient and the original quadratic energy. An upper quadratic
bound consequently gives a momentum second moment without any positive lower
bound for the displacement energy.
-/
open Set Function Matrix
open scoped BigOperators Classical
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Positive semidefiniteness gives the exact componentwise momentum-energy
Cauchy inequality, including singular coefficient matrices. -/
theorem mulVec_component_sq_le_diag_quadratic {A : Matrix ι ι ℝ} (hA : A.PosSemidef)
    (v : ι → ℝ) (i : ι) : (A *ᵥ v) i ^ 2 ≤ A i i * (v ⬝ᵥ (A *ᵥ v)) := by
  let e : ι → ℝ := Pi.single i 1
  have hee : e ⬝ᵥ (A *ᵥ e) = A i i := by
    simp [e, single_dotProduct, mulVec_single]
  have hev : e ⬝ᵥ (A *ᵥ v) = (A *ᵥ v) i := by simp [e]
  have hve : v ⬝ᵥ (A *ᵥ e) = (A *ᵥ v) i := by
    have hsym (j : ι) : A j i = A i j := by simpa using hA.isHermitian.apply i j
    change v ⬝ᵥ (A *ᵥ Pi.single i (1 : ℝ)) = (A *ᵥ v) i
    rw [mulVec_single_one]
    change (∑ j, v j * A j i) = ∑ j, A i j * v j
    apply Finset.sum_congr rfl
    intro j hj
    rw [hsym j, mul_comm]
  have hp (r : ℝ) :
      0 ≤ A i i * (r * r) + (2 * (A *ᵥ v) i) * r + v ⬝ᵥ (A *ᵥ v) := by
    have h := hA.dotProduct_mulVec_nonneg (v + r • e)
    simp only [star_trivial, mulVec_add, mulVec_smul, add_dotProduct, smul_dotProduct,
      dotProduct_add, dotProduct_smul, smul_eq_mul, hee, hev, hve] at h
    nlinarith [h]
  have hdisc := discrim_le_zero hp
  dsimp [discrim] at hdisc
  nlinarith

/-- A quadratic upper bound controls the momentum in the actual fixed
coordinate norm, even if the coefficient has arbitrarily small eigenvalues. -/
theorem norm_mulVec_sq_le_quadratic_of_sum_bound
    {A : Matrix ι ι ℝ} (hA : A.PosSemidef) {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ v : ι → ℝ, |matrixQuadratic A v| ≤ C * ∑ i, v i ^ 2)
    (v : ι → ℝ) : ‖A *ᵥ v‖ ^ 2 ≤ 4 * C * matrixQuadratic A v := by
  have hQ : 0 ≤ matrixQuadratic A v := by
    apply mul_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)
    simpa only [star_trivial] using hA.dotProduct_mulVec_nonneg v
  have hdiag (i : ι) : A i i ≤ 2 * C := by
    have hs : (∑ j : ι, ((Pi.single i (1 : ℝ) : ι → ℝ) j) ^ 2) = 1 := by
      rw [Finset.sum_eq_single i]
      · simp
      · intro j hj hji
        simp [hji]
      · simp
    have h : |(1 / 2 : ℝ) * A i i| ≤ C := by
      simpa [matrixQuadratic, hs] using hbound (Pi.single i (1 : ℝ))
    have hn : 0 ≤ A i i := hA.diag_nonneg
    rw [abs_of_nonneg (mul_nonneg (by norm_num) hn)] at h
    linarith
  have hcomponent (i : ι) : (A *ᵥ v) i ^ 2 ≤ 4 * C * matrixQuadratic A v := by
    have h := mulVec_component_sq_le_diag_quadratic hA v i
    have hquad : v ⬝ᵥ (A *ᵥ v) = 2 * matrixQuadratic A v := by
      dsimp [matrixQuadratic]
      ring
    rw [hquad] at h
    calc
      _ ≤ A i i * (2 * matrixQuadratic A v) := h
      _ ≤ (2 * C) * (2 * matrixQuadratic A v) :=
        mul_le_mul_of_nonneg_right (hdiag i) (mul_nonneg (by norm_num) hQ)
      _ = _ := by ring
  have hn : 0 ≤ 4 * C * matrixQuadratic A v := by positivity
  have hnorm : ‖A *ᵥ v‖ ≤ Real.sqrt (4 * C * matrixQuadratic A v) := by
    apply (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).mpr
    intro i
    rw [Real.norm_eq_abs]
    apply (Real.le_sqrt (abs_nonneg _) hn).mpr
    simpa only [sq_abs] using hcomponent i
  nlinarith [Real.sq_sqrt hn, norm_nonneg (A *ᵥ v), Real.sqrt_nonneg (4 * C * matrixQuadratic A v)]

end OTSelector.Reconstruction

end
end
