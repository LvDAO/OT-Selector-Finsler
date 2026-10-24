import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Convex.Mul
import OTSelector.Analysis.Convex.FiniteSoftMinimum
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Reconstruction.SoftMinimumHamiltonJacobi.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Reconstruction.SoftMinimumHamiltonJacobi`; the selected original proof blocks follow. -/
section

/-!
# Reconstruction.SoftMinimumHamiltonJacobi

**Conditions:** Finitely many branches have the stated time derivatives and spatial gradients; ε≠0 and each branch obeys its Hamilton–Jacobi inequality.

**Objects:** The actual finite soft minimum, its common exponential weights, and its derivative/gradient subsolution.

**Proof detail:** Differentiate the same positive exponential sum for both variables; its normalized weights are nonnegative and sum to one, so convexity of squared norm bounds the weighted gradient energy.

**Sources:** [Stephen Boyd; Lieven Vandenberghe, Convex Optimization (2004)](https://web.stanford.edu/~boyd/cvxbook/bv_cvxbook.pdf#page=86), Section 3.1.5, pp. 72–74, log-sum-exp example and derivative calculation; [Stephen Boyd; Lieven Vandenberghe, Convex Optimization (2004)](https://web.stanford.edu/~boyd/cvxbook/bv_cvxbook.pdf#page=83), Sections 3.1.3–3.1.4, pp. 69–71, first-order support inequality (3.2) and positive-semidefinite Hessian criterion; [Jiří Lebl, Basic Analysis II: Introduction to Real Analysis, Volume II (version 6.3, 15 May 2026)](https://www.jirka.org/ra/realanal2.pdf#page=37), Section 8.3, Proposition 8.3.6 and Theorem 8.3.7, pp. 37–38; Section 8.6, pp. 60–61.

Source relation (corollary): The cited sections provide the stated mathematical foundations; the exact finite construction and quantitative bound in this module are local consequences, not a claim that the book states the Lean theorem verbatim.
-/

/-!
# Genuine Hamilton-Jacobi subsolutions from finite smooth minima

The derivative and gradient use exactly the same internally generated positive
weights. Convexity of the squared norm then preserves the subsolution inequality.
-/
open Set Finset InnerProductSpace
open scoped BigOperators RealInnerProductSpace
noncomputable section
namespace OTSelector.Reconstruction
set_option maxHeartbeats 1800000

variable {I H : Type*} [Fintype I] [Nonempty I]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Actual gradients obey the same finite smooth-minimum derivative rule. -/
theorem hasGradientAt_finiteSoftMinimum
    (ε : ℝ) (hε : ε ≠ 0) (F : I → H → ℝ) (p : I → H) (x : H)
    (hF : ∀ i, HasGradientAt (F i) (p i) x) :
    HasGradientAt (fun y ↦ finiteSoftMinimum ε (fun i ↦ F i y))
      (∑ i, finiteSoftMinimumWeight ε (fun j ↦ F j x) i • p i) x := by
  apply hasGradientAt_iff_hasFDerivAt.mpr
  simpa only [map_sum, map_smul, RingHom.id_apply] using
    hasFDerivAt_finiteSoftMinimum ε hε F (fun i ↦ toDual ℝ H (p i)) x
      (fun i ↦ (hF i).hasFDerivAt)

omit [CompleteSpace H] in
/-- The squared norm of the actual smooth-minimum gradient is bounded by the
same weighted original squared gradients. -/
theorem finiteSoftMinimum_gradient_norm_sq_le (ε : ℝ) (a : I → ℝ) (p : I → H) :
    ‖∑ i, finiteSoftMinimumWeight ε a i • p i‖ ^ 2 ≤
      ∑ i, finiteSoftMinimumWeight ε a i * ‖p i‖ ^ 2 := by
  have hconv : ConvexOn ℝ univ (fun y : H ↦ ‖y‖ ^ 2) :=
    (convexOn_univ_norm.pow (fun x _ ↦ norm_nonneg x) 2)
  simpa only [smul_eq_mul] using hconv.map_sum_le
    (t := univ) (w := finiteSoftMinimumWeight ε a) (p := p)
    (fun i _ ↦ (finiteSoftMinimumWeight_pos ε a i).le)
    (sum_finiteSoftMinimumWeight ε a) (fun _ _ ↦ mem_univ _)

/-- The actual soft-minimum derivative and gradient satisfy Hamilton-Jacobi
whenever the original finite branches do. No derivative is chosen independently. -/
theorem finiteSoftMinimum_hamiltonJacobi
    (ε : ℝ) (hε : ε ≠ 0) (F : I → ℝ → H → ℝ) (d : I → ℝ) (p : I → H)
    (τ : ℝ) (x : H)
    (ht : ∀ i, HasDerivAt (fun σ ↦ F i σ x) (d i) τ)
    (hx : ∀ i, HasGradientAt (F i τ) (p i) x)
    (hHJ : ∀ i, d i + ‖p i‖ ^ 2 / 2 ≤ 0) :
    let w := finiteSoftMinimumWeight ε (fun i ↦ F i τ x)
    HasDerivAt (fun σ ↦ finiteSoftMinimum ε (fun i ↦ F i σ x)) (∑ i, w i * d i) τ ∧
    HasGradientAt (fun y ↦ finiteSoftMinimum ε (fun i ↦ F i τ y)) (∑ i, w i • p i) x ∧
    (∑ i, w i * d i) + ‖∑ i, w i • p i‖ ^ 2 / 2 ≤ 0 := by
  dsimp only
  refine ⟨hasDerivAt_finiteSoftMinimum ε hε _ d τ ht,
    hasGradientAt_finiteSoftMinimum ε hε _ p x hx, ?_⟩
  have hnorm := finiteSoftMinimum_gradient_norm_sq_le ε (fun i ↦ F i τ x) p
  have hsum : (∑ i, finiteSoftMinimumWeight ε (fun i ↦ F i τ x) i *
      (d i + ‖p i‖ ^ 2 / 2)) ≤ 0 :=
    Finset.sum_nonpos fun i _ ↦ mul_nonpos_of_nonneg_of_nonpos
      (finiteSoftMinimumWeight_pos ε _ i).le (hHJ i)
  simp_rw [mul_add, Finset.sum_add_distrib, ← mul_div_assoc, ← Finset.sum_div] at hsum
  linarith

end OTSelector.Reconstruction

end
end
