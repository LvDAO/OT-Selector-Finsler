import Mathlib.Algebra.Order.Star.Real
import OTSelector.LinearAlgebra.Matrix.CompactPositiveQuadratic
import OTSelector.LinearAlgebra.Matrix.FourLegMomentumBound
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Reconstruction.PositiveLegInverseQuadratic.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Reconstruction.PositiveLegInverseQuadratic`; the selected original proof blocks follow. -/
section

/-!
# Reconstruction.PositiveLegInverseQuadratic

**Conditions:** Each original positive leg has the geometric semidefinite lower bound A≥hI with h>0; the cycle bound has D₀≥0.

**Objects:** Positive definiteness, exact inverse-quadratic control and the resulting actual momentum estimate.

**Proof detail:** Evaluate the lower bound on nonzero vectors to obtain positive definiteness, then on A⁻¹v and apply Cauchy–Schwarz to bound its inverse quadratic; substitute C=1/(2h) into the common cycle estimate.

**Sources:** [Stephen Boyd; Lieven Vandenberghe, Convex Optimization (2004)](https://web.stanford.edu/~boyd/cvxbook/bv_cvxbook.pdf#page=660), Section 2.2.5, p. 34; Section 2.4.1, Example 2.15, p. 43; Appendix A.5.2, pp. 646–647 (spectral decomposition, determinant, definiteness, symmetric square root); [Terence Tao, An Epsilon of Room, I: Real Analysis (author preliminary version)](https://terrytao.wordpress.com/wp-content/uploads/2012/12/gsm-117-tao3-epsilon1.pdf#page=57), Section 1.4, Lemma 1.4.7 (Cauchy–Schwarz inequality), p. 48; [Stephen Boyd; Lieven Vandenberghe, Convex Optimization](https://web.stanford.edu/~boyd/cvxbook/bv_cvxbook.pdf#page=108), Section 3.3.2, Fenchel’s inequality and quadratic example, p. 94; [OTSelector project, Common-cut approximate momentum field and phase-cell envelopes](main.tex#degenerate-central-phase-envelope), main.tex label degenerate-central-phase-envelope, line 9561.

Source relation (corollary): The cited sections provide the stated mathematical foundations; the exact finite construction and quantitative bound in this module are local consequences, not a claim that the book states the Lean theorem verbatim.
-/

/-!
# Local positive-leg lower bounds give the required inverse quadratic bound

The traffic scale condition is the geometric Loewner inequality `A ≥ h I`, with `h > 0`.
It internally gives positive definiteness and the exact inverse quadratic bound, so no
independent inverse-norm or rank assumption is required.
-/

open Set Function Matrix
open scoped Matrix.Norms.Operator

noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
set_option linter.unusedSectionVars false

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A genuine strict Loewner lower bound makes the original leg positive definite. -/
theorem posDef_of_scalar_identity_lower_bound {A : Matrix ι ι ℝ} {h : ℝ}
    (hh : 0 < h) (hA : (A - h • (1 : Matrix ι ι ℝ)).PosSemidef) : A.PosDef := by
  have hI : (h • (1 : Matrix ι ι ℝ)).PosDef := Matrix.PosDef.one.smul hh
  simpa only [sub_add_cancel] using Matrix.PosDef.posSemidef_add hA hI

/-- The local geometric lower bound gives the original inverse-compliance quadratic upper
bound with its exact Taylor factor one half, in every finite dimension. -/
theorem matrixQuadratic_inverse_le_of_scalar_identity_lower_bound
    {A : Matrix ι ι ℝ} {h : ℝ} (hh : 0 < h)
    (hA : (A - h • (1 : Matrix ι ι ℝ)).PosSemidef) (v : ι → ℝ) :
    matrixQuadratic A⁻¹ v ≤ (1 / (2 * h)) * ∑ i, v i ^ 2 := by
  have hpos := posDef_of_scalar_identity_lower_bound hh hA
  let _ := hpos.isUnit.invertible
  let p := A⁻¹ *ᵥ v
  have hAp : A *ᵥ p = v := by
    dsimp [p]
    rw [Matrix.mulVec_mulVec, Matrix.mul_inv_of_invertible, Matrix.one_mulVec]
  have hlo := hA.dotProduct_mulVec_nonneg p
  simp only [star_trivial, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
    dotProduct_sub, dotProduct_smul, smul_eq_mul, hAp] at hlo
  have hlo' : h * (∑ i, p i ^ 2) ≤ p ⬝ᵥ v := by
    have heq : p ⬝ᵥ p = ∑ i, p i ^ 2 := by simp only [dotProduct, pow_two]
    rw [heq] at hlo
    linarith
  have hupper : 2 * h * (p ⬝ᵥ v) ≤ (∑ i, v i ^ 2) + h ^ 2 * ∑ i, p i ^ 2 := by
    calc
      _ = ∑ i, 2 * h * (p i * v i) := by rw [dotProduct, Finset.mul_sum]
      _ ≤ ∑ i, (v i ^ 2 + h ^ 2 * p i ^ 2) := by
        apply Finset.sum_le_sum
        intro i _
        nlinarith [sq_nonneg (v i - h * p i)]
      _ = _ := by rw [Finset.sum_add_distrib, ← Finset.mul_sum]
  have htimes := mul_le_mul_of_nonneg_left hlo' hh.le
  have hprod : h * (p ⬝ᵥ v) ≤ ∑ i, v i ^ 2 := by nlinarith
  have hcost : matrixQuadratic A⁻¹ v = (1 / 2 : ℝ) * (p ⬝ᵥ v) := by
    dsimp only [matrixQuadratic, p]
    rw [dotProduct_comm]
  have hdiv : (1 / (2 * h)) * (∑ i, v i ^ 2) = (∑ i, v i ^ 2) / (2 * h) := by ring
  rw [hcost, hdiv]
  apply (le_div_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 2) hh)).mpr
  nlinarith

/-- The geometric lower bound on the four local legs directly produces the common-cut
momentum estimate; no separate inverse-quadratic assumption remains. -/
theorem legalTwoCycle_momentum_norm_sq_le_of_leg_lower_bounds
    {A₁ B₁ A₂ B₂ : Matrix ι ι ℝ} {h D₀ : ℝ} (hh : 0 < h) (hD₀ : 0 ≤ D₀)
    (hA₁ : (A₁ - h • (1 : Matrix ι ι ℝ)).PosSemidef)
    (hB₁ : (B₁ - h • (1 : Matrix ι ι ℝ)).PosSemidef)
    (hA₂ : (A₂ - h • (1 : Matrix ι ι ℝ)).PosSemidef)
    (hB₂ : (B₂ - h • (1 : Matrix ι ι ℝ)).PosSemidef)
    (p₁ p₂ δ : ι → ℝ)
    (hcycle : matrixQuadratic (A₁ + B₁) p₁ + matrixQuadratic (A₂ + B₂) p₂ ≤
      matrixQuadratic (A₁ + B₂)⁻¹ (δ + A₁ *ᵥ p₁ + B₂ *ᵥ p₂) +
        matrixQuadratic (A₂ + B₁)⁻¹ (-δ + A₂ *ᵥ p₂ + B₁ *ᵥ p₁) + D₀) :
    ‖p₁ - p₂‖ ^ 2 ≤ (Fintype.card ι : ℝ) / h ^ 2 * ‖δ‖ ^ 2 + 2 * D₀ / h := by
  have hn := legalTwoCycle_momentum_norm_sq_le
    (posDef_of_scalar_identity_lower_bound hh hA₁)
    (posDef_of_scalar_identity_lower_bound hh hB₁)
    (posDef_of_scalar_identity_lower_bound hh hA₂)
    (posDef_of_scalar_identity_lower_bound hh hB₂)
    p₁ p₂ δ hD₀ (show 0 ≤ 1 / (2 * h) by positivity) hcycle
    (fun v ↦ ⟨matrixQuadratic_inverse_le_of_scalar_identity_lower_bound hh hA₁ v,
      matrixQuadratic_inverse_le_of_scalar_identity_lower_bound hh hA₂ v,
      matrixQuadratic_inverse_le_of_scalar_identity_lower_bound hh hB₁ v,
      matrixQuadratic_inverse_le_of_scalar_identity_lower_bound hh hB₂ v⟩)
  have heq : 4 * (1 / (2 * h)) *
      (D₀ + (1 / (2 * h)) * (Fintype.card ι : ℝ) * ‖δ‖ ^ 2) =
      (Fintype.card ι : ℝ) / h ^ 2 * ‖δ‖ ^ 2 + 2 * D₀ / h := by
    field_simp
    ring
  rwa [heq] at hn

end OTSelector.Reconstruction

end
end
