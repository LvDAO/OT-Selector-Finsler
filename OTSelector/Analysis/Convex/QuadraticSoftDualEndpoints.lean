import OTSelector.Analysis.Convex.FiniteSoftMinimum
import OTSelector.Analysis.Convex.FiniteSoftMinimumBounds
import OTSelector.Analysis.Convex.QuadraticSoftHamiltonJacobi
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Reconstruction.QuadraticSoftDualEndpoints.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Reconstruction.QuadraticSoftDualEndpoints`; the selected original proof blocks follow. -/
section

/-!
# Reconstruction.QuadraticSoftDualEndpoints

**Conditions:** Positive smoothing and nonnegative time offset; arbitrary feasible finite quadratic dual potentials and the given uniform node-pair cost bound.

**Objects:** Endpoint inequalities for the actual soft quadratic Hamilton–Jacobi tests.

**Proof detail:** At the source use its own branch as a competitor; at the target use finite dual feasibility and the changed time denominator, then combine with the ε log(card I) soft-minimum error.

**Sources:** [Stephen Boyd; Lieven Vandenberghe, Convex Optimization (2004)](https://web.stanford.edu/~boyd/cvxbook/bv_cvxbook.pdf#page=86), Section 3.1.5, pp. 72–74, log-sum-exp example and derivative calculation; [Gabriel Peyré; Marco Cuturi, Computational Optimal Transport](https://optimaltransport.github.io/pdf/ComputationalOT.pdf#page=31), Section 2.5, Proposition 2.4, p. 27, equations (2.19)–(2.20); [Stephen Boyd; Lieven Vandenberghe, Convex Optimization](https://web.stanford.edu/~boyd/cvxbook/bv_cvxbook.pdf#page=108), Section 3.3.2, Fenchel’s inequality and quadratic example, p. 94.

Source relation (corollary): The cited sections provide the stated mathematical foundations; the exact finite construction and quantitative bound in this module are local consequences, not a claim that the book states the Lean theorem verbatim.
-/

/-!
# The actual finite transportation dual is read by the smooth quadratic tests

The two endpoint inequalities use only the original finite dual feasibility.
They do not require a new bound on the arbitrary dual potential values.
-/
open scoped BigOperators
noncomputable section
namespace OTSelector.Reconstruction
set_option maxHeartbeats 1800000

variable {H I J : Type*} [NormedAddCommGroup H] [Fintype I] [Nonempty I]

omit [Nonempty I] in
/-- At a source node the actual soft quadratic test is at most its original
negative source price, by its own branch. -/
theorem quadraticSoftMinimum_sourceNode_le
    {ε δ : ℝ} (hε : 0 < ε) (u : I → ℝ) (x : I → H) (i : I) :
    finiteSoftMinimum ε (fun k ↦ quadraticHamiltonJacobiBranch (-u k) (x k) δ (x i)) ≤
      -u i := by
  simpa only [quadraticHamiltonJacobiBranch, sub_self, norm_zero, zero_pow two_ne_zero,
    zero_div, add_zero] using finiteSoftMinimum_le_component hε
      (fun k ↦ quadraticHamiltonJacobiBranch (-u k) (x k) δ (x i)) i

/-- A finite dual branch remains above its original target price up to the
explicit positive time shift times the original maximum quadratic cost. -/
theorem quadraticHamiltonJacobiBranch_target_le_error
    {δ M u v : ℝ} (hδ : 0 ≤ δ) (x y : H)
    (hdual : u + v ≤ ‖y - x‖ ^ 2 / 2) (hcost : ‖y - x‖ ^ 2 / 2 ≤ M) :
    v - M * δ ≤ quadraticHamiltonJacobiBranch (-u) x (1 + δ) y := by
  have hd : 0 < 2 * (1 + δ) := by positivity
  have hmul : (‖y - x‖ ^ 2 / 2) * δ ≤ M * δ := mul_le_mul_of_nonneg_right hcost hδ
  have hM : 0 ≤ M := (div_nonneg (sq_nonneg _) (by positivity)).trans hcost
  apply (le_of_mul_le_mul_right ?_ hd)
  dsimp only [quadraticHamiltonJacobiBranch]
  rw [add_mul, div_mul_cancel₀ _ hd.ne']
  nlinarith [mul_nonneg hM (sq_nonneg δ)]

/-- The true finite transportation dual pair is bounded by the same smooth
Hamilton-Jacobi endpoint readout, with only the explicit time and entropy errors. -/
theorem quadraticSoftMinimum_dual_endpoints
    {ε δ M : ℝ} (hε : 0 < ε) (hδ : 0 ≤ δ)
    (u : I → ℝ) (v : J → ℝ) (x : I → H) (y : J → H)
    (hdual : ∀ i j, u i + v j ≤ ‖y j - x i‖ ^ 2 / 2)
    (hcost : ∀ i j, ‖y j - x i‖ ^ 2 / 2 ≤ M) (i : I) (j : J) :
    u i + v j ≤
      finiteSoftMinimum ε
        (fun k ↦ quadraticHamiltonJacobiBranch (-u k) (x k) (1 + δ) (y j)) -
      finiteSoftMinimum ε
        (fun k ↦ quadraticHamiltonJacobiBranch (-u k) (x k) δ (x i)) +
      M * δ + ε * Real.log (Fintype.card I) := by
  have hlo := finiteSoftMinimum_lower hε
    (fun k ↦ quadraticHamiltonJacobiBranch (-u k) (x k) (1 + δ) (y j))
    (fun k ↦ quadraticHamiltonJacobiBranch_target_le_error hδ (x k) (y j)
      (hdual k j) (hcost k j))
  have hup := quadraticSoftMinimum_sourceNode_le (δ := δ) hε u x i
  linarith

end OTSelector.Reconstruction

end
end
