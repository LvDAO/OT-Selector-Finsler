import Mathlib.Analysis.InnerProductSpace.Calculus
import OTSelector.Analysis.Convex.FiniteSoftMinimum
import OTSelector.Analysis.Convex.SoftMinimumHamiltonJacobi
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Reconstruction.QuadraticSoftHamiltonJacobi.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Reconstruction.QuadraticSoftHamiltonJacobi`; the selected original proof blocks follow. -/
section

/-!
Conditions: A finite nonempty branch family in a real Hilbert space, with nonzero time and nonzero smoothing parameter as in the actual signature.

Objects: Actual derivatives of quadratic branches and their soft minimum, satisfying the Hamilton–Jacobi subsolution inequality.

Proof detail: Differentiate squared distance divided by time, use the exact branch equation and bound the squared weighted gradient by the weighted squared norms.

Sources: Stephen Boyd, Section 3.1.5, pp. 72–74, log-sum-exp example and derivative calculation (https://web.stanford.edu/~boyd/cvxbook/bv_cvxbook.pdf#page=86); Gabriel Peyré, Section 7.1, equations (7.1)–(7.5), pp. 112–113 (https://optimaltransport.github.io/pdf/ComputationalOT.pdf#page=116); Jiří Lebl, Section 8.3, Theorem 8.3.7, p. 38; Exercise 8.3.7, p. 45 (differentiate the inverse identity) (https://www.jirka.org/ra/realanal2.pdf#page=38).
Relation: Explicit soft-minimum subsolution calculation. Positivity of time or epsilon is not added when only nonzero is required.
-/

/-!
# Actual quadratic Hamilton-Jacobi tests for residual transport

The finite branches use the true squared Euclidean displacement to each original
endpoint. Their smooth minimum has actual time derivative and spatial gradient
and satisfies Hamilton-Jacobi on positive times.
-/
open InnerProductSpace
open scoped BigOperators RealInnerProductSpace
noncomputable section
namespace OTSelector.Reconstruction
set_option maxHeartbeats 2200000

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- The exact quadratic-cost Hamilton-Jacobi branch for one original endpoint. -/
def quadraticHamiltonJacobiBranch (a : ℝ) (y : H) (τ : ℝ) (x : H) : ℝ :=
  a + ‖x - y‖ ^ 2 / (2 * τ)

omit [InnerProductSpace ℝ H] [CompleteSpace H] in
theorem hasDerivAt_quadraticHamiltonJacobiBranch
    (a : ℝ) (y x : H) {τ : ℝ} (hτ : τ ≠ 0) :
    HasDerivAt (fun σ ↦ quadraticHamiltonJacobiBranch a y σ x)
      (-‖x - y‖ ^ 2 / (2 * τ ^ 2)) τ := by
  have hden : HasDerivAt (fun σ : ℝ ↦ 2 * σ) 2 τ := by
    simpa only [mul_one, id_eq] using (hasDerivAt_id τ).const_mul (2 : ℝ)
  have hd := ((hasDerivAt_const τ (‖x - y‖ ^ 2)).div hden
    (mul_ne_zero two_ne_zero hτ)).const_add a
  change HasDerivAt (fun σ ↦ a + ‖x - y‖ ^ 2 / (2 * σ)) _ τ
  apply hd.congr_deriv
  field_simp
  ring

theorem hasGradientAt_quadraticHamiltonJacobiBranch
    (a : ℝ) (y x : H) {τ : ℝ} (hτ : τ ≠ 0) :
    HasGradientAt (quadraticHamiltonJacobiBranch a y τ) (τ⁻¹ • (x - y)) x := by
  apply hasGradientAt_iff_hasFDerivAt.mpr
  have hv : HasFDerivAt (fun z : H ↦ z - y) (ContinuousLinearMap.id ℝ H) x :=
    (hasFDerivAt_id x).sub_const y
  have hd := (hv.norm_sq.const_smul ((2 * τ)⁻¹)).const_add a
  dsimp only [Pi.smul_apply] at hd
  have hfun : (fun z : H ↦ a + (2 * τ)⁻¹ • ‖z - y‖ ^ 2) =
      quadraticHamiltonJacobiBranch a y τ := by
    funext z
    simp only [quadraticHamiltonJacobiBranch, smul_eq_mul, div_eq_mul_inv, mul_comm]
  rw [hfun] at hd
  apply hd.congr_fderiv
  ext z
  simp only [toDual_apply_apply, real_inner_smul_left, smul_eq_mul, smul_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply, innerSL_apply_apply]
  field_simp
  simp only [two_smul, two_mul]

omit [CompleteSpace H] in
theorem quadraticHamiltonJacobiBranch_identity (y x : H) {τ : ℝ} (hτ : τ ≠ 0) :
    -‖x - y‖ ^ 2 / (2 * τ ^ 2) + ‖τ⁻¹ • (x - y)‖ ^ 2 / 2 = 0 := by
  simp only [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  field_simp
  ring

/-- The actual finite soft quadratic potential is a genuine smooth
Hamilton-Jacobi subsolution, with no supplied derivative or gradient. -/
theorem quadraticSoftMinimum_hamiltonJacobi
    {I : Type*} [Fintype I] [Nonempty I]
    (ε : ℝ) (hε : ε ≠ 0) (a : I → ℝ) (y : I → H)
    (τ : ℝ) (hτ : τ ≠ 0) (x : H) :
    let F := fun i σ z ↦ quadraticHamiltonJacobiBranch (a i) (y i) σ z
    let w := finiteSoftMinimumWeight ε (fun i ↦ F i τ x)
    let p := ∑ i, w i • (τ⁻¹ • (x - y i))
    let d := ∑ i, w i * (-‖x - y i‖ ^ 2 / (2 * τ ^ 2))
    HasDerivAt (fun σ ↦ finiteSoftMinimum ε (fun i ↦ F i σ x)) d τ ∧
    HasGradientAt (fun z ↦ finiteSoftMinimum ε (fun i ↦ F i τ z)) p x ∧
    d + ‖p‖ ^ 2 / 2 ≤ 0 := by
  apply finiteSoftMinimum_hamiltonJacobi ε hε
  · intro i
    exact hasDerivAt_quadraticHamiltonJacobiBranch (a i) (y i) x hτ
  · intro i
    exact hasGradientAt_quadraticHamiltonJacobiBranch (a i) (y i) x hτ
  · intro i
    exact (quadraticHamiltonJacobiBranch_identity (y i) x hτ).le

end OTSelector.Reconstruction

end
end
