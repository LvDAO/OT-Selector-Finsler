import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Matrix.Normed
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic.NoncommRing
import Mathlib.Topology.Instances.Matrix
import Mathlib.Topology.Order.Compact

/-!
# Geometry.Jacobi.HamiltonianSecondSolution

## Lemma skeleton

* **Conditions:** Finite real matrix Hamiltonian data; the inverse identities require the stated determinant and symmetry/Wronskian assumptions, while determinant bounds only require continuous J,K on a compact interval.

* **Objects:** The explicit second matrix solution and determinant-weighted cancellation bounds.

* **Proof detail:** Differentiate the actual inverse and transpose, substitute the Hamiltonian equations with their original multiplication order, and cancel using the Wronskian identity. Differentiate the Wronskian to prove constancy. Factor det(J±JT) and bound the continuous determinant expressions on the closed interval.

## Mathematical sources

- [Jiří Lebl, Basic Analysis II: Introduction to Real Analysis, Volume II (version 6.3, 15 May 2026)](https://www.jirka.org/ra/realanal2.pdf#page=38): Section 8.3, Theorem 8.3.7, p. 38; Exercise 8.3.7, p. 45 (differentiate the inverse identity).
- [Matias Dahl, An brief introduction to Finsler geometry (12 July 2006)](https://math.aalto.fi/~fdahl/finsler/finsler.pdf#page=31): Section 7, Definition 7.5 and Proposition 7.6, pp. 31–32.
- [Gerald Teschl, Ordinary Differential Equations and Dynamical Systems (AMS 2012 author preliminary version)](https://www.mat.univie.ac.at/~gerald/ftp/book-ode/ode.pdf#page=56): Section 2.4, pp. 45–47, equations (2.46)–(2.50), Theorem 2.10.
- [Stephen Boyd; Lieven Vandenberghe, Convex Optimization (2004)](https://web.stanford.edu/~boyd/cvxbook/bv_cvxbook.pdf#page=660): Section 2.2.5, p. 34; Section 2.4.1, Example 2.15, p. 43; Appendix A.5.2, pp. 646–647 (spectral decomposition, determinant, definiteness, symmetric square root).
- [OTSelector project, Second Jacobi solution and determinant cancellation](main.tex#lem:curved-jacobi-second-solution): main.tex label lem:curved-jacobi-second-solution, line 9098.

Source relation (composition): The matrix identities/cancellation are the paper’s algebraic construction. The module does not construct the compliance primitive or prove focal-endpoint continuation; those are not attributed to these lemmas.
-/

/-!
# Jacobi second-solution and determinant cancellation

For real finite matrices satisfying the first-order Hamiltonian equations, symmetry of `C`,
nonsingularity of `J`, and the Wronskian identity imply that `K = J * T` and
`R = P * T + J⁻¹ᵀ` solve the same equations when `T' = J⁻¹ * C * J⁻¹ᵀ`.
The inverse-transpose derivative is derived from the derivative of the actual matrix inverse;
it is not a premise. All multiplication orders are retained. Symmetric `A` and `C` also imply
Wronskian conservation on an open interval, independently of invertibility.

The determinant identities hold for arbitrary matrices, including singular ones. If `J` and
`K` extend continuously over a closed interval, they bound the determinant-weighted factors
`|det (1 ± T)| * |det J|` on its interior even when `T` does not extend to the endpoints.

This module proves the finite-dimensional analytic and algebraic ingredients. It does not
construct the compliance primitive `T`, prove smooth ODE continuation through focal endpoints,
or identify these matrices with the Jacobi data of a genuine Finsler distance.
-/

open Matrix Set
open scoped Matrix.Norms.Operator

namespace OTSelector.Geometry

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The derivative of the actual nonsingular matrix inverse at a nonsingular value. -/
theorem hasDerivAt_matrix_inverse {J : ℝ → Matrix n n ℝ}
    {J' : Matrix n n ℝ} {x : ℝ} (hJ : HasDerivAt J J' x) (hd : (J x).det ≠ 0) :
    HasDerivAt (fun t ↦ (J t)⁻¹) (-(J x)⁻¹ * J' * (J x)⁻¹) x := by
  obtain ⟨u, hu⟩ := (Matrix.isUnit_iff_isUnit_det (J x)).mpr (isUnit_iff_ne_zero.mpr hd)
  have hi : HasFDerivAt Ring.inverse
      (-ContinuousLinearMap.mulLeftRight ℝ (Matrix n n ℝ) (J x)⁻¹ (J x)⁻¹) (J x) := by
    simpa only [Matrix.coe_units_inv, hu] using (hasFDerivAt_ringInverse (𝕜 := ℝ) u)
  simpa only [Function.comp_def, ← Matrix.nonsing_inv_eq_ringInverse, neg_apply,
    ContinuousLinearMap.mulLeftRight_apply, neg_mul] using! hi.comp_hasDerivAt x hJ

omit [DecidableEq n] in
/-- Transposition carries a matrix derivative to its transpose. -/
theorem hasDerivAt_matrix_transpose {J : ℝ → Matrix n n ℝ}
    {J' : Matrix n n ℝ} {x : ℝ} (hJ : HasDerivAt J J' x) :
    HasDerivAt (fun t ↦ (J t).transpose) J'.transpose x := by
  let L : Matrix n n ℝ →L[ℝ] Matrix n n ℝ :=
    (Matrix.transposeLinearEquiv n n ℝ ℝ).toLinearMap.toContinuousLinearMap
  exact L.hasFDerivAt.comp_hasDerivAt x hJ

/-- Invertibility turns the Wronskian identity into the ordered inverse-matrix identity. -/
theorem wronskian_inverse_identity (J P : Matrix n n ℝ) (hJ : J.det ≠ 0)
    (hW : Jᵀ * P = Pᵀ * J) : P * J⁻¹ = J⁻¹ᵀ * Pᵀ := by
  have hJu : IsUnit J.det := isUnit_iff_ne_zero.mpr hJ
  have hleft : J⁻¹ᵀ * Jᵀ = 1 := by
    rw [← Matrix.transpose_mul, Matrix.mul_nonsing_inv _ hJu, Matrix.transpose_one]
  have hw := congrArg (fun M ↦ J⁻¹ᵀ * M * J⁻¹) hW
  simpa only [← Matrix.mul_assoc, hleft, Matrix.one_mul,
    Matrix.mul_nonsing_inv_cancel_right _ _ hJu] using hw

/-- The position equation after the product rule, keeping all matrix factors in order. -/
theorem second_position_algebra (B C J P T : Matrix n n ℝ) (hJ : J.det ≠ 0) :
    (B * J + C * P) * T + J * (J⁻¹ * C * J⁻¹ᵀ) =
      B * (J * T) + C * (P * T + J⁻¹ᵀ) := by
  have hunit : J * J⁻¹ = 1 := J.mul_nonsing_inv (isUnit_iff_ne_zero.mpr hJ)
  simp only [Matrix.add_mul, Matrix.mul_add, ← Matrix.mul_assoc, hunit, Matrix.one_mul, add_assoc]

/-- The inverse-transpose derivative simplifies using symmetry of `C` and invertibility. -/
theorem inverse_transpose_algebra (B C J P : Matrix n n ℝ) (hJ : J.det ≠ 0)
    (hC : Cᵀ = C) :
    -J⁻¹ᵀ * (B * J + C * P)ᵀ * J⁻¹ᵀ =
      -Bᵀ * J⁻¹ᵀ - J⁻¹ᵀ * Pᵀ * C * J⁻¹ᵀ := by
  have hunit : J⁻¹ᵀ * Jᵀ = 1 := by
    rw [← Matrix.transpose_mul, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hJ),
      Matrix.transpose_one]
  simp only [Matrix.transpose_add, Matrix.transpose_mul, hC,
    Matrix.mul_add, Matrix.add_mul, Matrix.neg_mul, ← Matrix.mul_assoc, hunit, Matrix.one_mul]
  noncomm_ring

/-- The two momentum terms cancel by the Wronskian identity, without commuting matrices. -/
theorem second_momentum_algebra (A B C J P T : Matrix n n ℝ) (hJ : J.det ≠ 0)
    (hW : Jᵀ * P = Pᵀ * J) :
    (-A * J - Bᵀ * P) * T + P * (J⁻¹ * C * J⁻¹ᵀ) +
        (-Bᵀ * J⁻¹ᵀ - J⁻¹ᵀ * Pᵀ * C * J⁻¹ᵀ) =
      -A * (J * T) - Bᵀ * (P * T + J⁻¹ᵀ) := by
  have hw := wronskian_inverse_identity J P hJ hW
  simp only [← Matrix.mul_assoc, hw]
  noncomm_ring

/-- The Hamiltonian inverse-transpose derivative follows from nonsingularity and the actual
matrix inverse derivative, rather than being assumed as a separate equation. -/
theorem hasDerivAt_inverse_transpose_hamiltonian
    {J : ℝ → Matrix n n ℝ} {B C P : Matrix n n ℝ} {x : ℝ}
    (hJ : HasDerivAt J (B * J x + C * P) x) (hd : (J x).det ≠ 0)
    (hC : Cᵀ = C) :
    HasDerivAt (fun t ↦ (J t)⁻¹ᵀ)
      (-Bᵀ * (J x)⁻¹ᵀ - (J x)⁻¹ᵀ * Pᵀ * C * (J x)⁻¹ᵀ) x := by
  have hi : HasDerivAt (fun t ↦ (J t)⁻¹ᵀ)
      (-(J x)⁻¹ᵀ * (B * J x + C * P)ᵀ * (J x)⁻¹ᵀ) x := by
    convert hasDerivAt_matrix_transpose (hasDerivAt_matrix_inverse hJ hd) using 1
    simp only [Matrix.transpose_mul, Matrix.transpose_neg]
    noncomm_ring
  simpa only [inverse_transpose_algebra B C (J x) P hd hC] using hi

/-- The actual product derivatives of `K = J * T` and `R = P * T + J⁻¹ᵀ` satisfy the
original Hamiltonian system. The matrices `A`, `B`, and `C` are their values at the time `x`;
no derivative of these coefficient matrices is used. -/
theorem hasDerivAt_second_jacobi_solution
    {J P T : ℝ → Matrix n n ℝ} {A B C : Matrix n n ℝ} {x : ℝ}
    (hJ : HasDerivAt J (B * J x + C * P x) x)
    (hP : HasDerivAt P (-A * J x - Bᵀ * P x) x)
    (hT : HasDerivAt T ((J x)⁻¹ * C * (J x)⁻¹ᵀ) x)
    (hd : (J x).det ≠ 0) (hC : Cᵀ = C) (hW : (J x)ᵀ * P x = (P x)ᵀ * J x) :
    HasDerivAt (fun t ↦ J t * T t)
        (B * (J x * T x) + C * (P x * T x + (J x)⁻¹ᵀ)) x ∧
      HasDerivAt (fun t ↦ P t * T t + (J t)⁻¹ᵀ)
        (-A * (J x * T x) - Bᵀ * (P x * T x + (J x)⁻¹ᵀ)) x := by
  have hprod : HasDerivAt (fun t ↦ J t * T t)
      ((B * J x + C * P x) * T x + J x * ((J x)⁻¹ * C * (J x)⁻¹ᵀ)) x := by
    simpa only [Pi.mul_apply] using! hJ.mul hT
  have hpt : HasDerivAt (fun t ↦ P t * T t)
      ((-A * J x - Bᵀ * P x) * T x + P x * ((J x)⁻¹ * C * (J x)⁻¹ᵀ)) x := by
    simpa only [Pi.mul_apply] using! hP.mul hT
  have hsum : HasDerivAt (fun t ↦ P t * T t + (J t)⁻¹ᵀ)
      (((-A * J x - Bᵀ * P x) * T x + P x * ((J x)⁻¹ * C * (J x)⁻¹ᵀ)) +
        (-Bᵀ * (J x)⁻¹ᵀ - (J x)⁻¹ᵀ * (P x)ᵀ * C * (J x)⁻¹ᵀ)) x := by
    simpa only [Pi.add_apply] using!
      hpt.add (hasDerivAt_inverse_transpose_hamiltonian hJ hd hC)
  constructor
  · simpa only [second_position_algebra B C (J x) (P x) (T x) hd] using hprod
  · simpa only [second_momentum_algebra A B C (J x) (P x) (T x) hd hW] using hsum

/-- Symmetric Hamiltonian coefficient matrices make the Wronskian derivative vanish.
Neither invertibility of `J` nor a zero initial Wronskian is needed for this identity. -/
theorem hasDerivAt_wronskian_zero
    {J P : ℝ → Matrix n n ℝ} {A B C : Matrix n n ℝ} {x : ℝ}
    (hJ : HasDerivAt J (B * J x + C * P x) x)
    (hP : HasDerivAt P (-A * J x - Bᵀ * P x) x)
    (hA : Aᵀ = A) (hC : Cᵀ = C) :
    HasDerivAt (fun t ↦ (J t)ᵀ * P t - (P t)ᵀ * J t) 0 x := by
  have hw : HasDerivAt (fun t ↦ (J t)ᵀ * P t - (P t)ᵀ * J t)
      (((B * J x + C * P x)ᵀ * P x + (J x)ᵀ * (-A * J x - Bᵀ * P x)) -
        ((-A * J x - Bᵀ * P x)ᵀ * J x + (P x)ᵀ * (B * J x + C * P x))) x := by
    simpa only [Pi.mul_apply, Pi.sub_apply] using!
      ((hasDerivAt_matrix_transpose hJ).mul hP).sub
        ((hasDerivAt_matrix_transpose hP).mul hJ)
  have hz : ((B * J x + C * P x)ᵀ * P x + (J x)ᵀ * (-A * J x - Bᵀ * P x)) -
        ((-A * J x - Bᵀ * P x)ᵀ * J x + (P x)ᵀ * (B * J x + C * P x)) = 0 := by
    simp only [Matrix.transpose_add, Matrix.transpose_sub, Matrix.transpose_mul,
      Matrix.transpose_neg, Matrix.transpose_transpose, hA, hC]
    noncomm_ring
  rwa [hz] at hw

/-- The Wronskian is conserved on an open interval under the symmetric Hamiltonian system. -/
theorem wronskian_constant_on_Ioo
    {J P A B C : ℝ → Matrix n n ℝ} {a b : ℝ}
    (hJ : ∀ t ∈ Ioo a b, HasDerivAt J (B t * J t + C t * P t) t)
    (hP : ∀ t ∈ Ioo a b, HasDerivAt P (-A t * J t - (B t)ᵀ * P t) t)
    (hA : ∀ t ∈ Ioo a b, (A t)ᵀ = A t)
    (hC : ∀ t ∈ Ioo a b, (C t)ᵀ = C t)
    {x y : ℝ} (hx : x ∈ Ioo a b) (hy : y ∈ Ioo a b) :
    (J x)ᵀ * P x - (P x)ᵀ * J x = (J y)ᵀ * P y - (P y)ᵀ * J y := by
  have hd : ∀ t ∈ Ioo a b,
      HasDerivAt (fun t ↦ (J t)ᵀ * P t - (P t)ᵀ * J t) 0 t :=
    fun t ht ↦ hasDerivAt_wronskian_zero (hJ t ht) (hP t ht) (hA t ht) (hC t ht)
  exact isOpen_Ioo.is_const_of_deriv_eq_zero (convex_Ioo a b).isPreconnected
    (fun t ht ↦ (hd t ht).differentiableAt.differentiableWithinAt)
    (fun t ht ↦ (hd t ht).deriv) hx hy

/-- A zero Wronskian at one interior time propagates throughout the interval. -/
theorem wronskian_identity_on_Ioo
    {J P A B C : ℝ → Matrix n n ℝ} {a b c : ℝ}
    (hJ : ∀ t ∈ Ioo a b, HasDerivAt J (B t * J t + C t * P t) t)
    (hP : ∀ t ∈ Ioo a b, HasDerivAt P (-A t * J t - (B t)ᵀ * P t) t)
    (hA : ∀ t ∈ Ioo a b, (A t)ᵀ = A t)
    (hC : ∀ t ∈ Ioo a b, (C t)ᵀ = C t)
    (hc : c ∈ Ioo a b) (hinit : (J c)ᵀ * P c = (P c)ᵀ * J c) :
    ∀ t ∈ Ioo a b, (J t)ᵀ * P t = (P t)ᵀ * J t := by
  intro t ht
  apply sub_eq_zero.mp
  rw [wronskian_constant_on_Ioo hJ hP hA hC ht hc, hinit, sub_self]

/-- Exact determinant cancellation for the positive sign; no invertibility is required. -/
theorem abs_det_add_mul (J T : Matrix n n ℝ) :
    |(1 + T).det| * |J.det| = |(J + J * T).det| := by
  have hfactor : J + J * T = J * (1 + T) := by noncomm_ring
  rw [hfactor, Matrix.det_mul, abs_mul, mul_comm]

/-- Exact determinant cancellation for the negative sign; no invertibility is required. -/
theorem abs_det_sub_mul (J T : Matrix n n ℝ) :
    |(1 - T).det| * |J.det| = |(J - J * T).det| := by
  have hfactor : J - J * T = J * (1 - T) := by noncomm_ring
  rw [hfactor, Matrix.det_mul, abs_mul, mul_comm]

/-- Continuous extensions of `J` and `K` bound both determinant expressions on a closed interval.
The matrices are allowed to be singular at any point. -/
theorem exists_abs_det_add_sub_bound {J K : ℝ → Matrix n n ℝ} {a b : ℝ}
    (hJ : ContinuousOn J (Icc a b)) (hK : ContinuousOn K (Icc a b)) :
    ∃ C : ℝ, ∀ t ∈ Icc a b,
      |(J t + K t).det| ≤ C ∧ |(J t - K t).det| ≤ C := by
  have hplus : ContinuousOn (fun t ↦ |(J t + K t).det|) (Icc a b) :=
    ((continuous_id.matrix_det).comp_continuousOn (hJ.add hK)).abs
  have hminus : ContinuousOn (fun t ↦ |(J t - K t).det|) (Icc a b) :=
    ((continuous_id.matrix_det).comp_continuousOn (hJ.sub hK)).abs
  obtain ⟨Cplus, hcplus⟩ := isCompact_Icc.bddAbove_image hplus
  obtain ⟨Cminus, hcminus⟩ := isCompact_Icc.bddAbove_image hminus
  refine ⟨max Cplus Cminus, fun t ht ↦ ⟨?_, ?_⟩⟩
  · exact (hcplus (mem_image_of_mem _ ht)).trans (le_max_left _ _)
  · exact (hcminus (mem_image_of_mem _ ht)).trans (le_max_right _ _)

/-- Determinant-weighted bounds persist to the ends from continuous `J` and `K = J * T`.
No continuity, boundedness, or endpoint definition compatible with a limit is required of `T`. -/
theorem exists_weighted_det_cancellation_bound {J K T : ℝ → Matrix n n ℝ} {a b : ℝ}
    (hJ : ContinuousOn J (Icc a b)) (hK : ContinuousOn K (Icc a b))
    (hKT : ∀ t ∈ Ioo a b, K t = J t * T t) :
    ∃ C : ℝ, ∀ t ∈ Ioo a b,
      |(1 + T t).det| * |(J t).det| ≤ C ∧
      |(1 - T t).det| * |(J t).det| ≤ C := by
  obtain ⟨C, hc⟩ := exists_abs_det_add_sub_bound hJ hK
  refine ⟨C, fun t ht ↦ ?_⟩
  rw [abs_det_add_mul, abs_det_sub_mul, ← hKT t ht]
  exact hc t ⟨ht.1.le, ht.2.le⟩

end OTSelector.Geometry
