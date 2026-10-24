import OTSelector.LinearAlgebra.FrozenQuadraticBound
import OTSelector.LinearAlgebra.Matrix.CompactPositiveQuadratic
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Reconstruction.FinslerOriginalNondegenerateKinetic.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Reconstruction.FinslerOriginalNondegenerateKinetic`; the selected original proof blocks follow. -/
section

/-!
# Reconstruction.FinslerOriginalNondegenerateKinetic

**Conditions:** The kinetic equals a nonzero scalar times a positive-definite quadratic form and a genuine nonzero displacement/mark pair is supplied.

**Objects:** A nonzero value of the actual frozen kinetic.

**Proof detail:** Positive definiteness makes the quadratic strictly positive at the nonzero displacement; multiplying by the nonzero weight cannot vanish, yielding the existential nondegeneracy witness.

**Sources:** [Stephen Boyd; Lieven Vandenberghe, Convex Optimization (2004)](https://web.stanford.edu/~boyd/cvxbook/bv_cvxbook.pdf#page=660), Section 2.2.5, p. 34; Section 2.4.1, Example 2.15, p. 43; Appendix A.5.2, pp. 646–647 (spectral decomposition, determinant, definiteness, symmetric square root).

Source relation (corollary): The cited sections provide the stated mathematical foundations; the exact finite construction and quantitative bound in this module are local consequences, not a claim that the book states the Lean theorem verbatim.
-/

/-!
# Non-degenerate kinetic at the lane

This module supplies the non-degeneracy input used by the F13 radius falsity: the
actual frozen kinetic is nonzero for some mark pair and nonzero displacement.  The
only analytic input is positive definiteness of the frozen coefficient matrix
(`∀ u ≠ 0, 0 < matrixQuadratic A u`) together with a nonzero kinetic weight and the
height-slice identification of the kinetic with the weighted quadratic form.

Residual data (stated exactly): a mark pair with nonzero displacement (`v ≠ 0`, i.e.
two distinct marks on the atlas image in the seed covector coordinates), a nonzero
weight `w`, and the identification `FrozenKineticQuadraticForm kin A w`.
-/

open Set Function Matrix Module
open scoped Topology ENNReal NNReal BigOperators

noncomputable section
namespace OTSelector.Reconstruction

/-- Non-degeneracy of the kinetic cost: there is a mark pair and a nonzero
displacement on which the kinetic is nonzero. -/
def KineticNondegenerate {C₀ B n : Type*} (kin : C₀ → B → (n → ℝ) → ℝ) : Prop :=
  ∃ (c : C₀) (b : B) (v : n → ℝ), kin c b v ≠ 0

/-- **Non-degeneracy from positive definiteness.**  A nonzero displacement, a nonzero
weight, the height-slice identification and positive definiteness of the frozen
coefficient matrix give a nonzero kinetic value at some mark pair. -/
theorem KineticNondegenerate.of_posDef {C₀ B n : Type*} [Fintype n]
    {kin : C₀ → B → (n → ℝ) → ℝ} {A : Matrix n n ℝ} {w : ℝ}
    (hform : FrozenKineticQuadraticForm kin A w) (hw : w ≠ 0)
    (hpos : ∀ u : n → ℝ, u ≠ 0 → 0 < matrixQuadratic A u)
    {c : C₀} {b : B} {v : n → ℝ} (hv : v ≠ 0) : KineticNondegenerate kin := by
  refine ⟨c, b, v, ?_⟩
  rw [hform c b v]
  have h : 0 < matrixQuadratic A v := hpos v hv
  exact mul_ne_zero hw (ne_of_gt h)

/-- The same non-degeneracy packaged as the existential nonzero kinetic value used by
the F13 falsity statement. -/
theorem exists_kinetic_ne_zero_of_posDef {C₀ B n : Type*} [Fintype n]
    {kin : C₀ → B → (n → ℝ) → ℝ} {A : Matrix n n ℝ} {w : ℝ}
    (hform : FrozenKineticQuadraticForm kin A w) (hw : w ≠ 0)
    (hpos : ∀ u : n → ℝ, u ≠ 0 → 0 < matrixQuadratic A u)
    {c : C₀} {b : B} {v : n → ℝ} (hv : v ≠ 0) :
    ∃ (c' : C₀) (b' : B) (v' : n → ℝ), kin c' b' v' ≠ 0 := by
  refine ⟨c, b, v, ?_⟩
  rw [hform c b v]
  exact mul_ne_zero hw (ne_of_gt (hpos v hv))

end OTSelector.Reconstruction
end
end
