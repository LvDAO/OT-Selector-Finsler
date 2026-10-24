import OTSelector.LinearAlgebra.Matrix.CompactPositiveQuadratic
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Reconstruction.LegalCycleComplianceVariation.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Reconstruction.LegalCycleComplianceVariation`; the selected original proof blocks follow. -/
section

/-!
# Reconstruction.LegalCycleComplianceVariation

**Conditions:** Four original compliance legs are positive definite; the original legal crossed-pair quadratic comparison is an explicit premise.

**Objects:** Exact inverse-quadratic split competitors and the four-leg variation inequality.

**Proof detail:** Complete the square to identify inverse quadratic energy as a Legendre maximum; split the crossed displacement into leg competitors and expand the shifted energies, keeping the true one-half normalization.

**Sources:** [Stephen Boyd; Lieven Vandenberghe, Convex Optimization](https://web.stanford.edu/~boyd/cvxbook/bv_cvxbook.pdf#page=108), Section 3.3.2, Fenchel’s inequality and quadratic example, p. 94; [Stephen Boyd; Lieven Vandenberghe, Convex Optimization (2004)](https://web.stanford.edu/~boyd/cvxbook/bv_cvxbook.pdf#page=660), Section 2.2.5, p. 34; Section 2.4.1, Example 2.15, p. 43; Appendix A.5.2, pp. 646–647 (spectral decomposition, determinant, definiteness, symmetric square root); [OTSelector project, Four-leg positive quadratic interface velocity calculation](main.tex#lem:highd-interface-velocity), main.tex label lem:highd-interface-velocity, line 3161.

Source relation (corollary): Quadratic conjugacy is classical. The exact four-leg competitor built from the supplied legal two-cycle inequality is a local combination; it assumes neither commuting legs nor simultaneous diagonalization.
-/

/-!
# Deterministic compliance competitors for legal two-cycles

The original positive compliance legs give exact split-path competitors for each legal
crossed pair.  No simultaneous diagonalization, fixed curvature, or uniform coefficient
lower bound is imposed.  These inequalities are the algebraic input of the local phase
momentum estimate, independently of the separate minimizer-to-cycle producer.
-/

open Set Function Matrix
open scoped Matrix.Norms.Operator

noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
set_option linter.unusedSectionVars false

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The original half-quadratic convention has the usual symmetric bilinear expansion. -/
theorem matrixQuadratic_add_of_isHermitian {A : Matrix ι ι ℝ} (hA : A.IsHermitian)
    (v w : ι → ℝ) :
    matrixQuadratic A (v + w) = matrixQuadratic A v + matrixQuadratic A w + v ⬝ᵥ (A *ᵥ w) := by
  have ht : Aᵀ = A := (Matrix.isHermitian_iff_isSymm.mp hA).eq
  have hsym : w ⬝ᵥ (A *ᵥ v) = v ⬝ᵥ (A *ᵥ w) := by
    simpa only [ht] using Matrix.dotProduct_transpose_mulVec A w v
  simp only [matrixQuadratic, Matrix.mulVec_add, add_dotProduct, dotProduct_add]
  rw [hsym]
  ring

/-- The inverse-compliance quadratic is the exact Legendre maximum of the original positive
compliance quadratic, in the fixed original basis. -/
theorem matrixQuadratic_inverse_ge_linear_sub {A : Matrix ι ι ℝ} (hA : A.PosDef)
    (p v : ι → ℝ) :
    p ⬝ᵥ v - matrixQuadratic A p ≤ matrixQuadratic A⁻¹ v := by
  let _ := hA.isUnit.invertible
  have hinv : A⁻¹ *ᵥ (A *ᵥ p) = p := by
    rw [Matrix.mulVec_mulVec, Matrix.inv_mul_of_invertible, Matrix.one_mulVec]
  have hnonneg := hA.inv.posSemidef.dotProduct_mulVec_nonneg (v - A *ᵥ p)
  simp only [star_trivial, Matrix.mulVec_sub, hinv, sub_dotProduct, dotProduct_sub] at hnonneg
  rw [dotProduct_comm v p, dotProduct_comm (A *ᵥ p) p] at hnonneg
  have hc : (A *ᵥ p) ⬝ᵥ (A⁻¹ *ᵥ v) = p ⬝ᵥ v := by
    have ht : (A⁻¹)ᵀ = A⁻¹ :=
      (Matrix.isHermitian_iff_isSymm.mp hA.inv.isHermitian).eq
    have he := Matrix.dotProduct_transpose_mulVec A⁻¹ (A *ᵥ p) v
    rw [ht, hinv] at he
    exact he.trans (dotProduct_comm v p)
  rw [hc] at hnonneg
  dsimp [matrixQuadratic]
  linarith

/-- Splitting a legal compliance interval at any interior position gives an upper competitor
for its actual inverse-compliance cost. -/
theorem matrixQuadratic_inverse_add_le_split {A B : Matrix ι ι ℝ}
    (hA : A.PosDef) (hB : B.PosDef) (u v : ι → ℝ) :
    matrixQuadratic (A + B)⁻¹ (u + v) ≤
      matrixQuadratic A⁻¹ u + matrixQuadratic B⁻¹ v := by
  let C := A + B
  have hC : C.PosDef := hA.add hB
  let _ := hC.isUnit.invertible
  let p := C⁻¹ *ᵥ (u + v)
  have hCp : C *ᵥ p = u + v := by
    dsimp [p]
    rw [Matrix.mulVec_mulVec, Matrix.mul_inv_of_invertible, Matrix.one_mulVec]
  have hsum := add_le_add (matrixQuadratic_inverse_ge_linear_sub hA p u)
    (matrixQuadratic_inverse_ge_linear_sub hB p v)
  have hquad : matrixQuadratic A p + matrixQuadratic B p = matrixQuadratic C p := by
    simp only [C, matrixQuadratic, Matrix.add_mulVec, dotProduct_add]
    ring
  have hself : p ⬝ᵥ (u + v) = 2 * matrixQuadratic C p := by
    rw [← hCp]
    dsimp [matrixQuadratic]
    ring
  have hdual : matrixQuadratic C p = matrixQuadratic C⁻¹ (u + v) := by
    dsimp [matrixQuadratic]
    rw [hCp, dotProduct_comm]
  rw [sub_add_sub_comm, ← dotProduct_add, hquad, hself, hdual] at hsum
  dsimp [C] at hsum
  linarith

/-- Shifting the meeting point on one positive original compliance leg has this exact cost. -/
theorem matrixQuadratic_inverse_compliance_shift {A : Matrix ι ι ℝ} (hA : A.PosDef)
    (p h : ι → ℝ) :
    matrixQuadratic A⁻¹ (A *ᵥ p + h) =
      matrixQuadratic A p + p ⬝ᵥ h + matrixQuadratic A⁻¹ h := by
  let _ := hA.isUnit.invertible
  have hinv : A⁻¹ *ᵥ (A *ᵥ p) = p := by
    rw [Matrix.mulVec_mulVec, Matrix.inv_mul_of_invertible, Matrix.one_mulVec]
  have hquad : matrixQuadratic A⁻¹ (A *ᵥ p) = matrixQuadratic A p := by
    simp only [matrixQuadratic, hinv]
    rw [dotProduct_comm]
  rw [add_comm (A *ᵥ p) h, matrixQuadratic_add_of_isHermitian hA.inv.isHermitian,
    hinv, hquad, dotProduct_comm h p]
  ring

/-- The original inverse coefficient cost equals compliance energy of its actual momentum. -/
theorem matrixQuadratic_compliance_momentum {A : Matrix ι ι ℝ} (hA : A.PosDef)
    (v : ι → ℝ) :
    matrixQuadratic A (A⁻¹ *ᵥ v) = matrixQuadratic A⁻¹ v := by
  let _ := hA.isUnit.invertible
  have hcancel : A *ᵥ (A⁻¹ *ᵥ v) = v := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_inv_of_invertible, Matrix.one_mulVec]
  simp only [matrixQuadratic, hcancel]
  rw [dotProduct_comm]

/-- Legal two-cycle optimality implies the exact four-leg meeting-point variation inequality.
Here δ is the actual path-position separation at the common cut and p₁,p₂ are unchanged
original momenta. All four positive legs may be different and need not commute. -/
theorem legalTwoCycle_fourLeg_variation
    {A₁ B₁ A₂ B₂ : Matrix ι ι ℝ}
    (hA₁ : A₁.PosDef) (hB₁ : B₁.PosDef) (hA₂ : A₂.PosDef) (hB₂ : B₂.PosDef)
    (p₁ p₂ δ : ι → ℝ) (D₀ : ℝ)
    (hcycle : matrixQuadratic (A₁ + B₁) p₁ + matrixQuadratic (A₂ + B₂) p₂ ≤
      matrixQuadratic (A₁ + B₂)⁻¹ (δ + A₁ *ᵥ p₁ + B₂ *ᵥ p₂) +
        matrixQuadratic (A₂ + B₁)⁻¹ (-δ + A₂ *ᵥ p₂ + B₁ *ᵥ p₁) + D₀)
    (h : ι → ℝ) :
    0 ≤ D₀ + 2 * ((p₁ - p₂) ⬝ᵥ h) - (p₁ - p₂) ⬝ᵥ δ +
      matrixQuadratic A₁⁻¹ h + matrixQuadratic A₂⁻¹ h +
      matrixQuadratic B₁⁻¹ (h - δ) + matrixQuadratic B₂⁻¹ (h - δ) := by
  have hfirst := matrixQuadratic_inverse_add_le_split hA₁ hB₂
    (A₁ *ᵥ p₁ + h) (B₂ *ᵥ p₂ + (δ - h))
  have hsecond := matrixQuadratic_inverse_add_le_split hA₂ hB₁
    (A₂ *ᵥ p₂ + -h) (B₁ *ᵥ p₁ + (h - δ))
  have hdisp₁ : (A₁ *ᵥ p₁ + h) + (B₂ *ᵥ p₂ + (δ - h)) =
      δ + A₁ *ᵥ p₁ + B₂ *ᵥ p₂ := by abel
  have hdisp₂ : (A₂ *ᵥ p₂ + -h) + (B₁ *ᵥ p₁ + (h - δ)) =
      -δ + A₂ *ᵥ p₂ + B₁ *ᵥ p₁ := by abel
  rw [hdisp₁] at hfirst
  rw [hdisp₂] at hsecond
  have hc := hcycle.trans (add_le_add (add_le_add hfirst hsecond) (le_refl D₀))
  rw [matrixQuadratic_inverse_compliance_shift hA₁,
    matrixQuadratic_inverse_compliance_shift hB₂,
    matrixQuadratic_inverse_compliance_shift hA₂,
    matrixQuadratic_inverse_compliance_shift hB₁] at hc
  have hneg (A : Matrix ι ι ℝ) (v : ι → ℝ) : matrixQuadratic A (-v) = matrixQuadratic A v := by
    simpa using matrixQuadratic_smul A (-1) v
  have hδ : δ - h = -(h - δ) := by abel
  rw [hδ, hneg, hneg] at hc
  simp only [dotProduct_sub, sub_dotProduct, dotProduct_neg, Matrix.add_mulVec,
    matrixQuadratic] at hc ⊢
  simp only [dotProduct_add] at hc
  linarith

end OTSelector.Reconstruction

end
end
