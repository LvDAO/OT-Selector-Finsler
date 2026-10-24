import OTSelector.Reconstruction.LipschitzPreservingSmoothApproximation

/-! Choose a genuine same-space smooth cutoff and a larger test compact for
every original compact support, including the empty set and zero dimension. -/

open Set Filter TopologicalSpace
open scoped Distributions Topology

noncomputable section
namespace OTSelector.Reconstruction

/-- An actual original compact support admits a larger compact test carrier
and a true smooth test equal to one on a neighborhood of every support point.
The existing project cutoff construction supplies the smooth function. -/
theorem exists_originalNeumannTestCutoff
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (K₀ : Set (ι → ℝ)) (hK₀ : IsCompact K₀) :
    ∃ (K : Compacts (ι → ℝ)) (χ : 𝓓_{K}(ι → ℝ, ℝ)),
      K₀ ⊆ interior (K : Set (ι → ℝ)) ∧
      ∀ x ∈ K₀, (χ : (ι → ℝ) → ℝ) =ᶠ[𝓝 x] fun _ ↦ 1 := by
  obtain ⟨R, _, hR⟩ := hK₀.isBounded.exists_pos_norm_le
  let K : Compacts (ι → ℝ) := ⟨Metric.closedBall 0 (R + 1), isCompact_closedBall _ _⟩
  have hK : K₀ ⊆ interior (K : Set (ι → ℝ)) := by
    intro x hx
    apply Metric.ball_subset_interior_closedBall
    change dist x 0 < R + 1
    rw [dist_zero_right]
    linarith [hR x hx]
  obtain ⟨c, hc, hcsupp, U, hU, hK₀U, hcone⟩ := exists_contDiff_cutoff K hK₀ hK
  let χ : 𝓓_{K}(ι → ℝ, ℝ) := ContDiffMapSupportedIn.of_support_subset hc hcsupp
  refine ⟨K, χ, hK, ?_⟩
  intro x hx
  filter_upwards [hU.mem_nhds (hK₀U hx)] with y hy
  exact hcone y hy

end OTSelector.Reconstruction
