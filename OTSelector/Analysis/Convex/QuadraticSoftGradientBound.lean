import OTSelector.Analysis.Convex.FiniteSoftMinimum
import OTSelector.Analysis.Convex.QuadraticSoftHamiltonJacobi
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Reconstruction.QuadraticSoftGradientBound.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Reconstruction.QuadraticSoftGradientBound`; the selected original proof blocks follow. -/
section

/-!
# Reconstruction.QuadraticSoftGradientBound

**Conditions:** Positive time τ, bounded node-to-point distances D and, for spatial comparison, a convex target set and ε≠0.

**Objects:** A gradient bound D/τ and spatial soft-test approximation error independent of dual potential values.

**Proof detail:** The true gradient is a convex combination of branch gradients τ⁻¹(x−yi), hence has norm ≤D/τ; integrate the derivative bound along a segment in the convex set.

**Sources:** [Stephen Boyd; Lieven Vandenberghe, Convex Optimization (2004)](https://web.stanford.edu/~boyd/cvxbook/bv_cvxbook.pdf#page=86), Section 3.1.5, pp. 72–74, log-sum-exp example and derivative calculation; [Jiří Lebl, Basic Analysis II: Introduction to Real Analysis, Volume II (version 6.3, 15 May 2026)](https://www.jirka.org/ra/realanal2.pdf#page=46), Section 8.4.1, Lemma 8.4.1 and Proposition 8.4.2, pp. 46–47.

Source relation (corollary): The cited sections provide the stated mathematical foundations; the exact finite construction and quantitative bound in this module are local consequences, not a claim that the book states the Lean theorem verbatim.
-/

/-!
# Uniform original-node gradient bounds and spatial approximation error

The constants depend only on the node geometry and the positive time, not on
the arbitrary finite dual potential values or the smoothing parameter.
-/
open Set Finset InnerProductSpace
open scoped BigOperators RealInnerProductSpace
noncomputable section
namespace OTSelector.Reconstruction
set_option maxHeartbeats 1800000

variable {I H : Type*} [Fintype I] [Nonempty I]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

omit [CompleteSpace H] in
/-- The actual soft quadratic gradient is bounded solely by the original node
distances, uniformly in all potential values and in the smoothing parameter. -/
theorem quadraticSoftMinimum_gradient_norm_le
    (ε : ℝ) (a : I → ℝ) (y : I → H) (x : H) {τ D : ℝ} (hτ : 0 < τ)
    (hD : ∀ i, ‖x - y i‖ ≤ D) :
    ‖∑ i, finiteSoftMinimumWeight ε
        (fun j ↦ quadraticHamiltonJacobiBranch (a j) (y j) τ x) i •
          (τ⁻¹ • (x - y i))‖ ≤ D / τ := by
  let w := finiteSoftMinimumWeight ε
    (fun j ↦ quadraticHamiltonJacobiBranch (a j) (y j) τ x)
  have hbranch (i : I) : ‖τ⁻¹ • (x - y i)‖ ≤ D / τ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hτ), div_eq_mul_inv,
      mul_comm D]
    exact mul_le_mul_of_nonneg_left (hD i) (inv_nonneg.mpr hτ.le)
  calc
    _ ≤ ∑ i, w i * ‖τ⁻¹ • (x - y i)‖ := by
      simpa only [smul_eq_mul] using
        (convexOn_univ_norm (E := H)).map_sum_le
          (t := univ) (w := w) (p := fun i ↦ τ⁻¹ • (x - y i))
          (fun i _ ↦ (finiteSoftMinimumWeight_pos ε _ i).le)
          (sum_finiteSoftMinimumWeight ε _) (fun _ _ ↦ mem_univ _)
    _ ≤ ∑ i, w i * (D / τ) := Finset.sum_le_sum fun i _ ↦
      mul_le_mul_of_nonneg_left (hbranch i) (finiteSoftMinimumWeight_pos ε _ i).le
    _ = D / τ := by
      rw [← Finset.sum_mul]
      change (∑ i, finiteSoftMinimumWeight ε _ i) * (D / τ) = _
      rw [sum_finiteSoftMinimumWeight, one_mul]

/-- The actual quadratic soft test controls the original finite-grid readout
error on any convex physical window. No potential bound is required. -/
theorem quadraticSoftMinimum_norm_sub_le
    (ε : ℝ) (hε : ε ≠ 0) (a : I → ℝ) (y : I → H)
    {τ D : ℝ} (hτ : 0 < τ) {S : Set H} (hS : Convex ℝ S)
    (hD : ∀ x ∈ S, ∀ i, ‖x - y i‖ ≤ D) {x z : H} (hx : x ∈ S) (hz : z ∈ S) :
    ‖finiteSoftMinimum ε (fun i ↦ quadraticHamiltonJacobiBranch (a i) (y i) τ z) -
      finiteSoftMinimum ε (fun i ↦ quadraticHamiltonJacobiBranch (a i) (y i) τ x)‖ ≤
        (D / τ) * ‖z - x‖ := by
  let F := fun b ↦ finiteSoftMinimum ε
    (fun i ↦ quadraticHamiltonJacobiBranch (a i) (y i) τ b)
  let p := fun b ↦ ∑ i, finiteSoftMinimumWeight ε
    (fun j ↦ quadraticHamiltonJacobiBranch (a j) (y j) τ b) i • (τ⁻¹ • (b - y i))
  have hgrad (b : H) : HasGradientAt F (p b) b :=
    (quadraticSoftMinimum_hamiltonJacobi ε hε a y τ hτ.ne' b).2.1
  exact Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le
    (fun b _ ↦ (hgrad b).hasFDerivAt.hasFDerivWithinAt)
    (fun b hb ↦ by
      rw [(toDual ℝ H).norm_map]
      exact quadraticSoftMinimum_gradient_norm_le ε a y b hτ (hD b hb)) hS hx hz

end OTSelector.Reconstruction

end
end
