import Mathlib.Analysis.Matrix.Normed
import Mathlib.LinearAlgebra.Matrix.PosDef
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Reconstruction.FinslerOriginalKineticBoundProducer.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Reconstruction.FinslerOriginalKineticBoundProducer`; the selected original proof blocks follow. -/
section

/-!
# Reconstruction.FinslerOriginalKineticBoundProducer

**Conditions:** A finite-dimensional kinetic satisfies its explicit absolute quadratic bound; scaling is nonnegative and increasing the bound uses nonnegativity of the square sum.

**Objects:** The KineticQuadraticBound predicate and its elementary closure properties.

**Proof detail:** Multiply the original bound by the nonnegative scalar and use |w kin|=w|kin|; monotonicity of the coefficient follows from the nonnegative sum of coordinate squares.

**Sources:** [Terence Tao, Analysis I](https://github.com/teorth/analysis/blob/main/Analysis/Section_7_1.lean), Sections 4.3 (absolute value) and 7.1 (finite series), in particular Proposition 7.1.11; [Stephen Boyd; Lieven Vandenberghe, Convex Optimization (2004)](https://web.stanford.edu/~boyd/cvxbook/bv_cvxbook.pdf#page=660), Section 2.2.5, p. 34; Section 2.4.1, Example 2.15, p. 43; Appendix A.5.2, pp. 646–647 (spectral decomposition, determinant, definiteness, symmetric square root).

Source relation (adapter): The cited sections provide the stated mathematical foundations; the exact finite construction and quantitative bound in this module are local consequences, not a claim that the book states the Lean theorem verbatim.
-/

/-!
# Per-pair kinetic bound producer

This module names the per-pair kinetic bound consumed by
`hCbnd_intrinsic_blockW_of_hkin_bound` with its exact type, and proves the elementary
closure properties needed to produce it for the actual frozen kinetic.

The bound is `KineticQuadraticBound kin Cb`, i.e. `∀ a b v, |kin a b v| ≤ Cb * ∑ i, v i ^ 2`
for the mark pair `(a, b)` and the displacement `v` in the seed covector coordinates.
The actual frozen kinetic of the lane is `w ^ (-(2 / q)) * frozenPhysicalCost`
(a scalar times a frozen quadratic form `matrixQuadratic`), so the producer reduces to:
(i) the coefficient quadratic bound `|matrixQuadratic (C.matrix z0 q) v| ≤ Cb * ∑ v^2`
on the compact coefficient matrix class (Matrix operator bound times the finite sum
comparison), and (ii) the non-negativity of the weight factor so scalar scaling
preserves the bound (proved here).

Remaining exact input: step (i), the coefficient quadratic bound on the compact
matrix class (from `CompactQuadraticCoefficient` operator-norm continuity plus the
finite-dimensional sup-norm/Euclidean-norm comparison; the frozen matrix class is
compact), and the identification of the lane's kinetic with the weighted frozen
quadratic form on the height slice.
-/

open Set Function Matrix Module
open scoped Topology ENNReal Matrix.Norms.Operator NNReal BigOperators

noncomputable section
namespace OTSelector.Reconstruction

/-- The per-pair kinetic quadratic bound: for every mark pair and displacement the
kinetic seed cost is bounded by `Cb` times the squared displacement. -/
def KineticQuadraticBound {A B n : Type*} [Fintype n] (kin : A → B → (n → ℝ) → ℝ)
    (Cb : ℝ) : Prop :=
  ∀ (a : A) (b : B) (v : n → ℝ), |kin a b v| ≤ Cb * ∑ i, v i ^ 2

/-- The bound is monotone in the constant. -/
theorem KineticQuadraticBound.mono {A B n : Type*} [Fintype n]
    {kin : A → B → (n → ℝ) → ℝ} {Cb Cb' : ℝ} (h : KineticQuadraticBound kin Cb)
    (hsum : ∀ v : n → ℝ, 0 ≤ ∑ i, v i ^ 2) (hCC : Cb ≤ Cb') :
    KineticQuadraticBound kin Cb' := by
  intro a b v
  have h0 : 0 ≤ ∑ i, v i ^ 2 := hsum v
  calc |kin a b v| ≤ Cb * ∑ i, v i ^ 2 := h a b v
    _ ≤ Cb' * ∑ i, v i ^ 2 := by nlinarith

/-- Scalar scaling with a non-negative weight preserves the quadratic bound. -/
theorem kineticQuadraticBound_const_mul {A B n : Type*} [Fintype n]
    {kin : A → B → (n → ℝ) → ℝ} {Cb w : ℝ} (hw : 0 ≤ w)
    (h : KineticQuadraticBound kin Cb) :
    KineticQuadraticBound (fun a b v => w * kin a b v) (w * Cb) := by
  intro a b v
  calc |w * kin a b v| = w * |kin a b v| := by rw [abs_mul, abs_of_nonneg hw]
    _ ≤ w * (Cb * ∑ i, v i ^ 2) := mul_le_mul_of_nonneg_left (h a b v) hw
    _ = w * Cb * ∑ i, v i ^ 2 := by ring

end OTSelector.Reconstruction
end
end
