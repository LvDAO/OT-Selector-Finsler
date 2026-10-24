import OTSelector.LinearAlgebra.FrozenQuadraticBound
import OTSelector.LinearAlgebra.Matrix.CompactPositiveQuadratic
import OTSelector.LinearAlgebra.QuadraticEnergyBound
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Reconstruction.FinslerOriginalCoefficientQuadraticBoundComplete.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Reconstruction.FinslerOriginalCoefficientQuadraticBoundComplete`; the selected original proof blocks follow. -/
section

/-!
# Reconstruction.FinslerOriginalCoefficientQuadraticBoundComplete

**Conditions:** An arbitrary real finite coefficient matrix and, in the kinetic consumer, its exact nonnegative scalar identification.

**Objects:** The explicit coefficient bound (1/2)Σij|Aij| times Σivi² and its weighted kinetic version.

**Proof detail:** Each |vi| is bounded by the square root of the sum of squares; bound every quadratic cross term, sum the absolute coefficients, and retain the matrixQuadratic one-half factor.

**Sources:** [Terence Tao, An Epsilon of Room, I: Real Analysis (author preliminary version)](https://terrytao.wordpress.com/wp-content/uploads/2012/12/gsm-117-tao3-epsilon1.pdf#page=57), Section 1.4, Lemma 1.4.7 (Cauchy–Schwarz inequality), p. 48; [Terence Tao, Analysis I](https://github.com/teorth/analysis/blob/main/Analysis/Section_7_1.lean), Sections 4.3 (absolute value) and 7.1 (finite series), in particular Proposition 7.1.11; [Stephen Boyd; Lieven Vandenberghe, Convex Optimization (2004)](https://web.stanford.edu/~boyd/cvxbook/bv_cvxbook.pdf#page=660), Section 2.2.5, p. 34; Section 2.4.1, Example 2.15, p. 43; Appendix A.5.2, pp. 646–647 (spectral decomposition, determinant, definiteness, symmetric square root).

Source relation (corollary): The cited sections provide the stated mathematical foundations; the exact finite construction and quantitative bound in this module are local consequences, not a claim that the book states the Lean theorem verbatim.
-/

/-!
# The coefficient quadratic bound, completed

The remaining analytic input of `FinslerOriginalCoefficientQuadraticBound` is proved:
for every frozen coefficient matrix `A`,

    |matrixQuadratic A v| <= (1/2 * sum_i sum_j |A_ij|) * sum_i v_i^2.

Proof: `matrixQuadratic A v = 1/2 * sum_i v_i * (sum_j A_ij v_j)`; the inner sum is
bounded by `(sum_j |A_ij|) * sqrt S` with `S = sum_i v_i^2` using
`|v_j| <= sqrt S` (`Finset.single_le_sum` on the squares), each outer term by
`sqrt S * ((sum_j |A_ij|) * sqrt S) = (sum_j |A_ij|) * S` using
`Real.mul_self_sqrt`, and the sum over `i` gives `(sum_i sum_j |A_ij|) * S`.
The factor one half of `matrixQuadratic` is kept explicit.

`kineticQuadraticBound_of_frozenQuadraticForm_complete` then wires this into the
kinetic bound producer at the concrete constant `Cb = 1/2 * sum_i sum_j |A_ij|`.
No `sorry`, `admit` or added axiom.
-/

open Set Function Matrix Module
open scoped Topology ENNReal NNReal BigOperators

noncomputable section
namespace OTSelector.Reconstruction

variable {n : Type*} [Fintype n]

/-- **The coefficient quadratic bound**, proved for every matrix `A` with the explicit
constant `1/2 * sum_i sum_j |A_ij|`. -/
theorem coefficientQuadraticBound_of_abs_sum (A : Matrix n n ℝ) :
    CoefficientQuadraticBound A ((1 / 2 : ℝ) * ∑ i, ∑ j, |A i j|) := by
  intro v
  let S : ℝ := ∑ i, v i ^ 2
  have hS0 : 0 ≤ S := by
    show 0 ≤ ∑ i, v i ^ 2
    exact Finset.sum_nonneg fun i _ ↦ sq_nonneg (v i)
  have hvi : ∀ i, |v i| ≤ Real.sqrt S := by
    intro i
    have h1 : (v i) ^ 2 ≤ S := by
      show (v i) ^ 2 ≤ ∑ j, v j ^ 2
      exact Finset.single_le_sum (f := fun j ↦ v j ^ 2)
        (fun j _ ↦ sq_nonneg (v j)) (Finset.mem_univ i)
    calc |v i| = Real.sqrt ((v i) ^ 2) := by rw [Real.sqrt_sq_eq_abs]
      _ ≤ Real.sqrt S := Real.sqrt_le_sqrt h1
  have hD : v ⬝ᵥ (A *ᵥ v) = ∑ i, v i * (∑ j, A i j * v j) := by
    simp [dotProduct, mulVec_apply]
  have hterm : ∀ i, Real.sqrt S * (∑ j, |A i j| * Real.sqrt S) =
      (∑ j, |A i j|) * S := by
    intro i
    let x : ℝ := ∑ j, |A i j|
    have hx : Real.sqrt S * (x * Real.sqrt S) = x * S := by
      calc Real.sqrt S * (x * Real.sqrt S) = x * (Real.sqrt S * Real.sqrt S) := by ring
        _ = x * S := by rw [Real.mul_self_sqrt hS0]
    simpa only [x, Finset.sum_mul] using hx
  have hsum : |v ⬝ᵥ (A *ᵥ v)| ≤ (∑ i, ∑ j, |A i j|) * S := by
    rw [hD]
    calc |∑ i, v i * (∑ j, A i j * v j)|
        ≤ ∑ i, |v i * (∑ j, A i j * v j)| :=
          Finset.abs_sum_le_sum_abs (Finset.univ)
            (f := fun i ↦ v i * (∑ j, A i j * v j))
      _ ≤ ∑ i, Real.sqrt S * (∑ j, |A i j| * Real.sqrt S) := by
          refine Finset.sum_le_sum fun i _ ↦ ?_
          rw [abs_mul]
          refine mul_le_mul (hvi i) ?_ (abs_nonneg _) (Real.sqrt_nonneg S)
          calc |∑ j, A i j * v j| ≤ ∑ j, |A i j * v j| :=
                Finset.abs_sum_le_sum_abs (Finset.univ) (f := fun j ↦ A i j * v j)
            _ = ∑ j, |A i j| * |v j| := by
                exact Finset.sum_congr rfl fun j _ ↦ abs_mul (A i j) (v j)
            _ ≤ ∑ j, |A i j| * Real.sqrt S :=
                Finset.sum_le_sum fun j _ ↦
                  mul_le_mul_of_nonneg_left (hvi j) (abs_nonneg _)
      _ = (∑ i, ∑ j, |A i j|) * S := by
          rw [Finset.sum_congr rfl fun i _ ↦ hterm i, ← Finset.sum_mul]
  rw [matrixQuadratic]
  calc |(1 / 2 : ℝ) * (v ⬝ᵥ (A *ᵥ v))|
      = (1 / 2 : ℝ) * |v ⬝ᵥ (A *ᵥ v)| := by
        rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
    _ ≤ (1 / 2 : ℝ) * ((∑ i, ∑ j, |A i j|) * S) :=
        mul_le_mul_of_nonneg_left hsum (by norm_num)
    _ = ((1 / 2 : ℝ) * ∑ i, ∑ j, |A i j|) * S := by ring
    _ = ((1 / 2 : ℝ) * ∑ i, ∑ j, |A i j|) * ∑ i, v i ^ 2 := rfl

/-- **The completed kinetic bound producer**: with the height-slice identification and
non-negative weight, the lane kinetic bound holds at the concrete frozen constant
`w * (1/2 * sum_i sum_j |A_ij|)`, with no coefficient-bound input left. -/
theorem kineticQuadraticBound_of_frozenQuadraticForm_complete
    {A₀ B : Type*} {n : Type*} [Fintype n]
    {kin : A₀ → B → (n → ℝ) → ℝ} {A : Matrix n n ℝ} {w : ℝ} (hw : 0 ≤ w)
    (hform : FrozenKineticQuadraticForm kin A w) :
    KineticQuadraticBound kin
      (w * ((1 / 2 : ℝ) * ∑ i, ∑ j, |A i j|)) :=
  kineticQuadraticBound_of_frozenQuadraticForm hw hform
    (coefficientQuadraticBound_of_abs_sum A)

end OTSelector.Reconstruction

end
end
