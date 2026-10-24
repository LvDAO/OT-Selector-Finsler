import Mathlib.Analysis.InnerProductSpace.MeanErgodic
import Mathlib.Topology.MetricSpace.UniformConvergence

/-!
# Analysis.InnerProductSpace.ContractionAverages

## Lemma skeleton

* **Conditions:** A complete real Hilbert space, contractions U_i and a uniformly contractive family A_n; A_n kills every U_i y−y asymptotically and x is orthogonal to all common fixed vectors.

* **Objects:** Convergence A_n x→0 along the supplied arbitrary filter.

* **Proof detail:** Let W be the span of the ranges U_i−Id. A vector in W-perp is fixed by each U_i, using the contraction equality case. Thus x lies in closure W. The set of vectors killed by A_n is a closed subspace by uniform equicontinuity and contains W.

## Mathematical sources

- [Terence Tao, An Epsilon of Room, I: Real Analysis (author preliminary version)](https://terrytao.wordpress.com/wp-content/uploads/2012/12/gsm-117-tao3-epsilon1.pdf#page=61): Section 1.4, Exercises 1.4.12–1.4.13, pp. 52–53.

Source relation (generalization): This is the closed-range/orthogonal-complement core of mean-ergodic arguments. It assumes the explicit cancellation of A_n and is not attributed as a verbatim Cesaro-average theorem.
-/

/-! Contraction averages converge to zero on the common-invariant complement. -/
open Set Function Filter
open scoped Topology
noncomputable section
namespace OTSelector.Probability

/-- A contraction averaging family that asymptotically annihilates every
translation difference tends to zero on the complement of all common fixed
vectors. The transformations form an arbitrary family, so invariance under a
single lattice step is never substituted for full spatial invariance. -/
theorem tendsto_zero_of_common_fixed_orthogonal
    {H I J : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (U : I → H →L[ℝ] H) (hU : ∀ i, ‖U i‖ ≤ 1)
    (l : Filter J) (A : J → H →L[ℝ] H) (hA : ∀ n, ‖A n‖ ≤ 1)
    (hcancel : ∀ i y, Tendsto (fun n ↦ A n (U i y - y)) l (𝓝 0))
    (x : H) (hcenter : ∀ y, (∀ i, U i y = y) → inner ℝ y x = 0) :
    Tendsto (fun n ↦ A n x) l (𝓝 0) := by
  let W : Submodule ℝ H := ⨆ i, (U i - ContinuousLinearMap.id ℝ H).toLinearMap.range
  have hfixed (y : H) (hy : y ∈ Wᗮ) : ∀ i, U i y = y := by
    intro i
    have hi : y ∈ (U i - ContinuousLinearMap.id ℝ H).toLinearMap.rangeᗮ :=
      Submodule.orthogonal_le (le_iSup (fun i ↦
        (U i - ContinuousLinearMap.id ℝ H).toLinearMap.range) i) hy
    apply eq_of_norm_le_re_inner_eq_norm_sq (𝕜 := ℝ)
    · simpa only [one_mul] using (U i).le_of_opNorm_le (hU i) y
    · have hpair : ∀ z, inner ℝ (U i z) y = inner ℝ z y := by
        simpa [Submodule.mem_orthogonal, inner_sub_left, sub_eq_zero] using hi
      simp [hpair]
  have hx : x ∈ W.topologicalClosure := by
    rw [← Submodule.orthogonal_orthogonal_eq_closure]
    exact fun y hy ↦ hcenter y (hfixed y hy)
  let S : Submodule ℝ H := {
    carrier := {y | Tendsto (fun n ↦ A n y) l (𝓝 0)}
    zero_mem' := by
      change Tendsto (fun n ↦ A n 0) l (𝓝 0)
      simpa only [map_zero] using
        (tendsto_const_nhds : Tendsto (fun _ : J ↦ (0 : H)) l (𝓝 0))
    add_mem' := by
      intro y z hy hz
      change Tendsto (fun n ↦ A n (y + z)) l (𝓝 0)
      simpa only [map_add, zero_add] using hy.add hz
    smul_mem' := by
      intro c y hy
      change Tendsto (fun n ↦ A n (c • y)) l (𝓝 0)
      simpa only [map_smul, smul_zero] using hy.const_smul c }
  have hS : IsClosed (S : Set H) := by
    exact (LipschitzWith.uniformEquicontinuous (fun n y ↦ A n y) 1
      (fun n ↦ (A n).lipschitzWith.weaken (hA n))).equicontinuous.isClosed_setOfPred_tendsto
        continuous_const
  have hWS : W ≤ S := by
    apply iSup_le
    intro i y hy
    obtain ⟨z, rfl⟩ := hy
    change Tendsto (fun n ↦ A n (U i z - z)) l (𝓝 0)
    exact hcancel i z
  exact W.topologicalClosure_minimal hWS hS hx

end OTSelector.Probability
