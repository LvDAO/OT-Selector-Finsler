import OTSelector.Analysis.Convex.FiniteSoftMinimum
import OTSelector.Analysis.Convex.QuadraticSoftHamiltonJacobi
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Reconstruction.QuadraticSoftSmoothness.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Reconstruction.QuadraticSoftSmoothness`; the selected original proof blocks follow. -/
section

/-!
# Reconstruction.QuadraticSoftSmoothness

**Conditions:** A finite family of original quadratic branches and nonzero time; smoothing ε is arbitrary for the regularity statement.

**Objects:** Joint time-space and spatial smoothness of the actual quadratic soft tests.

**Proof detail:** Compose smooth squared norm, time inversion and finite exponential sums; strict positivity of the exponential sum permits logarithmic differentiation to every requested finite or infinite order.

**Sources:** [Stephen Boyd; Lieven Vandenberghe, Convex Optimization (2004)](https://web.stanford.edu/~boyd/cvxbook/bv_cvxbook.pdf#page=86), Section 3.1.5, pp. 72–74, log-sum-exp example and derivative calculation; [Jiří Lebl, Basic Analysis II: Introduction to Real Analysis, Volume II (version 6.3, 15 May 2026)](https://www.jirka.org/ra/realanal2.pdf#page=37), Section 8.3, Proposition 8.3.6 and Theorem 8.3.7, pp. 37–38; Section 8.6, pp. 60–61.

Source relation (corollary): The cited sections provide the stated mathematical foundations; the exact finite construction and quantitative bound in this module are local consequences, not a claim that the book states the Lean theorem verbatim.
-/

/-!
# Genuine joint smoothness of the quadratic soft tests

Smoothness is proved for the same original finite branches and their actual
positive exponential sum, so these functions can be localized to the original
compactly supported Neumann test space.
-/
open scoped BigOperators
noncomputable section
namespace OTSelector.Reconstruction
set_option maxHeartbeats 1800000

variable {I H : Type*} [Fintype I] [Nonempty I]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Joint smoothness of the original quadratic branch off zero time. -/
theorem contDiffAt_quadraticHamiltonJacobiBranch
    (n : ℕ∞) (a : ℝ) (y : H) (τ : ℝ) (hτ : τ ≠ 0) (x : H) :
    ContDiffAt ℝ n (fun z : ℝ × H ↦ quadraticHamiltonJacobiBranch a y z.1 z.2) (τ, x) :=
  contDiffAt_const.add
    (((contDiffAt_snd.sub contDiffAt_const).norm_sq ℝ).div
      (contDiffAt_const.mul contDiffAt_fst) (mul_ne_zero two_ne_zero hτ))

/-- The actual finite soft quadratic test is jointly smooth, of every finite or
infinite differentiability order, away from zero time. -/
theorem contDiffAt_quadraticSoftMinimum
    (n : ℕ∞) (ε : ℝ) (a : I → ℝ) (y : I → H)
    (τ : ℝ) (hτ : τ ≠ 0) (x : H) :
    ContDiffAt ℝ n (fun z : ℝ × H ↦ finiteSoftMinimum ε
      (fun i ↦ quadraticHamiltonJacobiBranch (a i) (y i) z.1 z.2)) (τ, x) := by
  have hsum : ContDiffAt ℝ n (fun z : ℝ × H ↦
      ∑ i, Real.exp (-ε⁻¹ * quadraticHamiltonJacobiBranch (a i) (y i) z.1 z.2)) (τ, x) :=
    ContDiffAt.sum fun i _ ↦ (contDiffAt_const.mul
      (contDiffAt_quadraticHamiltonJacobiBranch n (a i) (y i) τ hτ x)).exp
  exact contDiffAt_const.mul
    (hsum.log (finiteSoftMinimum_sum_exp_pos ε
      (fun i ↦ quadraticHamiltonJacobiBranch (a i) (y i) τ x)).ne')

/-- In particular the original spatial test at a fixed nonzero time is smooth
on the whole original Euclidean coordinate space. -/
theorem contDiff_quadraticSoftMinimum
    (n : ℕ∞) (ε : ℝ) (a : I → ℝ) (y : I → H) (τ : ℝ) (hτ : τ ≠ 0) :
    ContDiff ℝ n (fun x ↦ finiteSoftMinimum ε
      (fun i ↦ quadraticHamiltonJacobiBranch (a i) (y i) τ x)) := by
  apply contDiff_iff_contDiffAt.mpr
  intro x
  exact (contDiffAt_quadraticSoftMinimum n ε a y τ hτ x).comp x
    (contDiffAt_const.prodMk contDiffAt_id)

end OTSelector.Reconstruction

end
end
