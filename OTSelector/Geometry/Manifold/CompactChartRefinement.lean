import Mathlib.Geometry.Manifold.IsManifold.ExtChartAt
import Mathlib.Topology.MetricSpace.Pseudo.Basic

/-!
# Geometry.Manifold.CompactChartRefinement

## Lemma skeleton

* **Conditions:** A compact subset of a finite-dimensional real charted space under the source’s stated metric/topological hypotheses.

* **Objects:** Finitely many compact model-space chart cores whose inverse images cover exactly the original compact set.

* **Proof detail:** Choose small closed neighborhoods subordinate to each chart source, extract a finite cover of the original compact set, and map the compact intersections into the legal chart targets.

## Mathematical sources

- [John M. Lee, Introduction to Smooth Manifolds, second edition (2013)](https://sites.math.washington.edu/~lee/Books/ISM/front-matter.pdf#page=10): Chapter 3, sections “The Differential of a Smooth Map” pp. 55–59, “Computations in Coordinates” pp. 60–64, “The Tangent Bundle” pp. 65–67, “Velocity Vectors of Curves” pp. 68–70.
- [Terence Tao, An Epsilon of Room, I: Real Analysis (author preliminary version)](https://terrytao.wordpress.com/wp-content/uploads/2012/12/gsm-117-tao3-epsilon1.pdf#page=110): Sections 1.6.2 and 1.8.1, compactness by finite subcovers, pp. 78 and 101–102; Section 1.8.3, Proposition 1.8.10, pp. 107–108 (finite products).

Source relation (corollary): Compact chart refinement with actual legal-domain containment; no properness or smoothness of the charted space is silently added.
-/

/-!
# Finite compact coordinate cores covering an actual compact set

Closed small metric balls subordinate to chart sources, intersected with the original
compact set, give compact coordinate cores. Their inverse chart images cover exactly
the original set. No properness, nonemptiness, or smoothness of the charted space is needed.
-/

open Set Filter Metric Manifold
open scoped Topology

namespace OTSelector.Geometry

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MetricSpace M] [ChartedSpace E M]

/-- Every compact subset of a metrizable charted space has a finite exact covering
by inverse images of compact coordinate cores lying in their genuine chart targets. -/
theorem exists_finite_compact_chart_refinement (A : Set M) (hA : IsCompact A) :
    ∃ J : Finset M, ∃ K : M → Set E,
      (∀ j ∈ J, IsCompact (K j) ∧ K j ⊆ (extChartAt 𝓘(ℝ, E) j).target ∧
        (extChartAt 𝓘(ℝ, E) j).symm '' K j ⊆ A) ∧
      (⋃ j ∈ J, (extChartAt 𝓘(ℝ, E) j).symm '' K j) = A := by
  classical
  have hradius : ∀ j : M, ∃ r : ℝ, 0 < r ∧
      closedBall j r ⊆ (extChartAt 𝓘(ℝ, E) j).source := by
    intro j
    exact nhds_basis_closedBall.mem_iff.mp
      ((isOpen_extChartAt_source j).mem_nhds (mem_extChartAt_source j))
  choose r hr hsource using hradius
  obtain ⟨J, hcover⟩ := hA.elim_finite_subcover (fun j ↦ ball j (r j))
    (fun _ ↦ isOpen_ball) (fun x _ ↦ mem_iUnion.mpr ⟨x, mem_ball_self (hr x)⟩)
  let S : M → Set M := fun j ↦ A ∩ closedBall j (r j)
  let K : M → Set E := fun j ↦ (extChartAt 𝓘(ℝ, E) j) '' S j
  have hS (j : M) : S j ⊆ (extChartAt 𝓘(ℝ, E) j).source :=
    fun _ hx ↦ hsource j hx.2
  have hinverse (j : M) : (extChartAt 𝓘(ℝ, E) j).symm '' K j = S j := by
    apply Subset.antisymm
    · rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      simpa only [(extChartAt 𝓘(ℝ, E) j).left_inv (hS j hx)] using hx
    · intro x hx
      refine ⟨extChartAt 𝓘(ℝ, E) j x, ⟨x, hx, rfl⟩, ?_⟩
      exact (extChartAt 𝓘(ℝ, E) j).left_inv (hS j hx)
  refine ⟨J, K, ?_, ?_⟩
  · intro j _
    refine ⟨(hA.inter_right isClosed_closedBall).image_of_continuousOn
      ((continuousOn_extChartAt j).mono (hS j)), ?_, ?_⟩
    · rintro _ ⟨x, hx, rfl⟩
      exact (extChartAt 𝓘(ℝ, E) j).map_source (hS j hx)
    · rw [hinverse]
      exact inter_subset_left
  · apply Subset.antisymm
    · intro x hx
      obtain ⟨j, _, hj⟩ := mem_iUnion₂.mp hx
      rw [hinverse] at hj
      exact hj.1
    · intro x hx
      obtain ⟨j, hjJ, hj⟩ := mem_iUnion₂.mp (hcover hx)
      apply mem_iUnion₂.mpr
      refine ⟨j, hjJ, ?_⟩
      rw [hinverse]
      exact ⟨hx, ball_subset_closedBall hj⟩

end OTSelector.Geometry
