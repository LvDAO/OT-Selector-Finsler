import OTSelector.Analysis.Normed.BallCubeEmbedding
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Reconstruction.FiniteLabelCubes.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Reconstruction.FiniteLabelCubes`; the selected original proof blocks follow. -/
section

/-!
# Reconstruction.FiniteLabelCubes

**Conditions:** Finitely many finite-dimensional normed spaces have specified bases and positive ball radii.

**Objects:** Continuous injective-on-ball maps into a common unit cube and one finite inverse Lipschitz constant.

**Proof detail:** Use finite basis coordinates and a clipped affine rescaling, whose clipping is inactive on the closed balls; choose the maximum of finitely many coordinate-equivalence constants and square the distance comparison.

**Sources:** [Stephen Boyd; Lieven Vandenberghe, Convex Optimization (2004)](https://web.stanford.edu/~boyd/cvxbook/bv_cvxbook.pdf#page=662), Appendix A.5.1, pp. 645–646 (range/nullspace/rank); A.5.2, p. 647 (positive square root); A.5.4, pp. 648–649 (SVD and the nonzero spectra of A^T A and A A^T); [Terence Tao, An Epsilon of Room, I: Real Analysis (author preliminary version)](https://terrytao.wordpress.com/wp-content/uploads/2012/12/gsm-117-tao3-epsilon1.pdf#page=110), Sections 1.6.2 and 1.8.1, compactness by finite subcovers, pp. 78 and 101–102; Section 1.8.3, Proposition 1.8.10, pp. 107–108 (finite products); [Terence Tao, Analysis I](https://github.com/teorth/analysis/blob/main/Analysis/Section_7_1.lean), Sections 4.3 (absolute value) and 7.1 (finite series), in particular Proposition 7.1.11.

Source relation (corollary): The cited sections provide the stated mathematical foundations; the exact finite construction and quantitative bound in this module are local consequences, not a claim that the book states the Lean theorem verbatim.
-/

/-!
# One cube scale for finitely many actual bounded label charts

Each closed label ball is embedded into the same standard cube dimension. A
single finite inverse Lipschitz constant preserves all actual pair distances.
-/

open Set Metric Module
open scoped BigOperators
noncomputable section
namespace OTSelector.Reconstruction

variable {ι β : Type*} [Fintype ι] [Fintype β]
  {W : ι → Type*} [∀ i, NormedAddCommGroup (W i)] [∀ i, NormedSpace ℝ (W i)]

/-- Finitely many actual closed label balls admit continuous cube-valued maps
with one common inverse Lipschitz constant on their original domains. -/
theorem exists_finite_labelUnitCubeMaps (b : ∀ i, Basis β ℝ (W i))
    {r : ι → ℝ} (hr : ∀ i, 0 < r i) :
    ∃ (Q : ∀ i, W i → β → Icc (0 : ℝ) 1) (L : ℝ), 0 < L ∧
      ∀ i, Continuous (Q i) ∧ InjOn (Q i) (closedBall 0 (r i)) ∧
        ∀ w ∈ closedBall 0 (r i), ∀ z ∈ closedBall 0 (r i),
          ‖w - z‖ ≤ L * ‖(fun j ↦ (Q i w j : ℝ)) - (fun j ↦ (Q i z j : ℝ))‖ := by
  classical
  have hlocal (i : ι) := exists_labelUnitCubeMap_on_ball (b i)
    (show 0 < 2 * r i by linarith [hr i])
  choose Q L hQ hinj hL hbound using hlocal
  let L₀ := (∑ i, L i) + 1
  have hL₀ : 0 < L₀ := by
    have hsum : 0 ≤ ∑ i, L i := Finset.sum_nonneg (fun i _ ↦ (hL i).le)
    dsimp only [L₀]
    linarith
  refine ⟨Q, L₀, hL₀, fun i ↦ ⟨hQ i, ?_, ?_⟩⟩
  · exact (hinj i).mono (closedBall_subset_ball (by linarith [hr i]))
  · intro w hw z hz
    have hi : L i ≤ L₀ := by
      have hsum := Finset.single_le_sum (f := L) (fun j _ ↦ (hL j).le)
        (Finset.mem_univ i)
      dsimp only [L₀]
      linarith
    exact (hbound i w (closedBall_subset_ball (by linarith [hr i]) hw)
      z (closedBall_subset_ball (by linarith [hr i]) hz)).trans
        (mul_le_mul_of_nonneg_right hi (norm_nonneg _))

/-- The actual label-distance comparison transports any original quadratic
upper bound to the same cube coordinates without changing either endpoint. -/
theorem quadratic_upper_of_labelCube_bound {X : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    {C L error : ℝ} (hC : 0 ≤ C)
    {w z : X} {a b : β → ℝ}
    (hlabel : ‖z - w‖ ≤ L * ‖b - a‖)
    (hcost : error ≤ C * ‖z - w‖ ^ 2) : error ≤ (C * L ^ 2) * ‖b - a‖ ^ 2 := by
  have hsq : ‖z - w‖ ^ 2 ≤ (L * ‖b - a‖) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) hlabel 2
  calc
    error ≤ C * ‖z - w‖ ^ 2 := hcost
    _ ≤ C * (L * ‖b - a‖) ^ 2 := mul_le_mul_of_nonneg_left hsq hC
    _ = (C * L ^ 2) * ‖b - a‖ ^ 2 := by ring

end OTSelector.Reconstruction

end
end
