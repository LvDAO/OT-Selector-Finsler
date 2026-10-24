import OTSelector.LinearAlgebra.Matrix.CompactPositiveQuadratic
import OTSelector.LinearAlgebra.QuadraticEnergyBound
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Reconstruction.FinslerOriginalCoefficientQuadraticBound.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Reconstruction.FinslerOriginalCoefficientQuadraticBound`; the selected original proof blocks follow. -/
section

/-!
# Reconstruction.FinslerOriginalCoefficientQuadraticBound

**Conditions:** The actual kinetic is identified with a nonnegative scalar times a finite quadratic form, and that form has the explicit absolute coefficient bound.

**Objects:** FrozenKineticQuadraticForm, CoefficientQuadraticBound and the resulting kinetic bound.

**Proof detail:** Substitute the exact quadratic-form identification, factor the nonnegative scalar out of the absolute value and multiply the supplied coefficient estimate.

**Sources:** [Stephen Boyd; Lieven Vandenberghe, Convex Optimization (2004)](https://web.stanford.edu/~boyd/cvxbook/bv_cvxbook.pdf#page=660), Section 2.2.5, p. 34; Section 2.4.1, Example 2.15, p. 43; Appendix A.5.2, pp. 646–647 (spectral decomposition, determinant, definiteness, symmetric square root); [Terence Tao, Analysis I](https://github.com/teorth/analysis/blob/main/Analysis/Section_7_1.lean), Sections 4.3 (absolute value) and 7.1 (finite series), in particular Proposition 7.1.11.

Source relation (adapter): The cited sections provide the stated mathematical foundations; the exact finite construction and quantitative bound in this module are local consequences, not a claim that the book states the Lean theorem verbatim.
-/

/-!
# Coefficient quadratic bound producer

This module finishes the kinetic bound route structurally: the per-pair kinetic
bound `KineticQuadraticBound` for the actual lane kinetic is reduced to

(a) ONE typed identification input `FrozenKineticQuadraticForm kin A w`: the lane
kinetic is the weighted frozen quadratic form `w * matrixQuadratic A` on the height
slice (this is the height-slice pairing form of FinslerOriginalKinPairingIdentification
with A := C.matrix z₀ q and w := w^(-(2/q))), and

(b) the coefficient quadratic bound `CoefficientQuadraticBound A Cb`, i.e.
`∀ v, |matrixQuadratic A v| ≤ Cb * ∑ i, v i ^ 2` on the compact frozen coefficient
matrix class.

Given (a) and (b) with `0 ≤ w`, the lane bound `KineticQuadraticBound kin (w * Cb)`
holds, with no other input.  The coefficient bound (b) itself is the remaining
analytic estimate (see the producer module doc: sup-norm operator estimate for
matrixQuadratic and compactness of the frozen matrix class).
-/

open Set Function Matrix Module
open scoped Topology ENNReal NNReal BigOperators

noncomputable section
namespace OTSelector.Reconstruction

/-- Typed height-slice identification input: the actual lane kinetic is the weighted
frozen quadratic form of a coefficient matrix. -/
def FrozenKineticQuadraticForm {A₀ B n : Type*} [Fintype n]
    (kin : A₀ → B → (n → ℝ) → ℝ) (A : Matrix n n ℝ) (w : ℝ) : Prop :=
  ∀ (a : A₀) (b : B) (v : n → ℝ), kin a b v = w * matrixQuadratic A v

/-- The coefficient quadratic bound for a frozen coefficient matrix: the exact
remaining analytic input. -/
def CoefficientQuadraticBound {n : Type*} [Fintype n] (A : Matrix n n ℝ) (Cb : ℝ) : Prop :=
  ∀ v : n → ℝ, |matrixQuadratic A v| ≤ Cb * ∑ i, v i ^ 2

/-- From the height-slice identification and the coefficient quadratic bound, with a
non-negative kinetic weight, the per-pair kinetic bound holds. -/
theorem kineticQuadraticBound_of_frozenQuadraticForm {A₀ B n : Type*} [Fintype n]
    {kin : A₀ → B → (n → ℝ) → ℝ} {A : Matrix n n ℝ} {w Cb : ℝ} (hw : 0 ≤ w)
    (hform : FrozenKineticQuadraticForm kin A w)
    (hQ : CoefficientQuadraticBound A Cb) :
    KineticQuadraticBound kin (w * Cb) := by
  intro a b v
  rw [hform a b v, abs_mul, abs_of_nonneg hw]
  calc w * |matrixQuadratic A v| ≤ w * (Cb * ∑ i, v i ^ 2) :=
        mul_le_mul_of_nonneg_left (hQ v) hw
    _ = w * Cb * ∑ i, v i ^ 2 := by ring

/-- The same conclusion with the identification and the coefficient constant kept as
separate outputs of the compact coefficient class. -/
theorem kineticQuadraticBound_of_frozenQuadraticForm' {A₀ B n : Type*} [Fintype n]
    {kin : A₀ → B → (n → ℝ) → ℝ} {A : Matrix n n ℝ} {w Cb : ℝ} (hw : 0 ≤ w)
    (hform : FrozenKineticQuadraticForm kin A w)
    (hQ : ∀ v : n → ℝ, |matrixQuadratic A v| ≤ Cb * ∑ i, v i ^ 2) :
    KineticQuadraticBound kin (w * Cb) :=
  kineticQuadraticBound_of_frozenQuadraticForm hw hform hQ

end OTSelector.Reconstruction

end
end
