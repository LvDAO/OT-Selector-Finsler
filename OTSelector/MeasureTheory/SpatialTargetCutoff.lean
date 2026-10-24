import OTSelector.MeasureTheory.SpatialLongEdgeWindow
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Probability.CavitySemidiscreteSpatialCutoff.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Probability.CavitySemidiscreteSpatialCutoff`; the selected original proof blocks follow. -/
section

/-!
# MeasureTheory.SpatialTargetCutoff

## Lemma skeleton

* **Conditions:** Finite-dimensional spatial coordinates with compact target marks and a bounded source spatial window.
* **Objects:** Actual compact target exhaustion and comparison of target escape with long-edge mass.
* **Proof detail:** Choose growing spatial balls times the compact mark carrier. Reverse-triangle bounds show escape forces displacement at least the corresponding radius; apply measure monotonicity.

## Mathematical sources

- [Terence Tao, An Epsilon of Room, I: Real Analysis (author preliminary version)](https://terrytao.wordpress.com/wp-content/uploads/2012/12/gsm-117-tao3-epsilon1.pdf#page=110): Sections 1.6.2 and 1.8.1, compactness by finite subcovers, pp. 78 and 101–102; Section 1.8.3, Proposition 1.8.10, pp. 107–108 (finite products).
- [Sheldon Axler, Measure, Integration & Real Analysis (author PDF, 12 June 2026)](https://measure.axler.net/MIRA.pdf#page=93): Section 3A, Theorem 3.11, p. 78 (Monotone Convergence).

Source relation (composition): Explicit compact exhaustion and geometric inclusion; no properness of an endpoint projection is assumed.
-/

/-!
# Actual compact target cutoffs and spatial escape

For compact mark carriers, spatial balls give genuine compact target tests.
Leaving such a ball from a bounded source window forces a long original edge.
-/

open MeasureTheory Set Filter Topology TopologicalSpace
open scoped ENNReal CompactlySupported
noncomputable section
namespace OTSelector.Probability

variable {ι A B : Type*} [Fintype ι]
  [TopologicalSpace B] [CompactSpace B]

/-- Spatial target balls with the original compact mark carrier. The source
radius shifts only the cutoff, without altering any source or target law. -/
def cavitySpatialTargetExhaustion (R₀ : ℝ) : CompactExhaustion ((ι → ℝ) × B) where
  toFun n := Metric.closedBall 0 (R₀ + n + 1) ×ˢ univ
  isCompact' n := (isCompact_closedBall _ _).prod isCompact_univ
  subset_interior_succ' n := by
    rw [interior_prod_eq, interior_univ]
    intro y hy
    refine ⟨Metric.ball_subset_interior_closedBall ?_, mem_univ _⟩
    exact Metric.closedBall_subset_ball (by push_cast; linarith) hy.1
  iUnion_eq' := by
    apply eq_univ_of_forall
    intro y
    obtain ⟨n, hn⟩ := exists_nat_gt (‖y.1‖ - R₀ - 1)
    apply mem_iUnion.mpr
    refine ⟨n, ?_, mem_univ _⟩
    rw [Metric.mem_closedBall, dist_zero_right]
    linarith

variable [MeasurableSpace A] [MeasurableSpace B]

omit [MeasurableSpace A] [MeasurableSpace B] in
/-- Escape from the compact target cutoff is contained in the actual long-edge
window. The marks have no ordering or separation requirement. -/
theorem source_tail_subset_longEdgeWindow
    (S : Set ((ι → ℝ) × A)) (U : Set (ι → ℝ)) (R₀ : ℝ)
    (hS : ∀ x ∈ S, x.1 ∈ U) (hR₀ : ∀ x ∈ S, ‖x.1‖ ≤ R₀) (n : ℕ) :
    S ×ˢ (cavitySpatialTargetExhaustion (B := B) R₀ n)ᶜ ⊆
      cavityLongEdgeWindow U (ENNReal.ofReal (((n : ℝ) + 1) ^ 2)) := by
  intro e he
  have hy : R₀ + (n : ℝ) + 1 < ‖e.2.1‖ := by
    apply lt_of_not_ge
    intro hy
    apply he.2
    exact ⟨by simpa only [Metric.mem_closedBall, dist_zero_right] using hy, mem_univ _⟩
  have hd : (n : ℝ) + 1 ≤ ‖e.2.1 - e.1.1‖ := by
    have hnorm : ‖e.2.1‖ ≤ ‖e.2.1 - e.1.1‖ + ‖e.1.1‖ := by
      simpa only [sub_add_cancel] using norm_add_le (e.2.1 - e.1.1) e.1.1
    linarith [hR₀ e.1 he.1]
  refine ⟨hS e.1 he.1, ENNReal.ofReal_le_ofReal ?_⟩
  gcongr

/-- The actual full plan's target-cutoff error is bounded by its actual long-edge
mass, including diffuse plans and repeated target locations. -/
theorem measure_source_tail_le_longEdgeWindow
    (π : Measure (((ι → ℝ) × A) × ((ι → ℝ) × B)))
    (S : Set ((ι → ℝ) × A)) (U : Set (ι → ℝ)) (R₀ : ℝ)
    (hS : ∀ x ∈ S, x.1 ∈ U) (hR₀ : ∀ x ∈ S, ‖x.1‖ ≤ R₀) (n : ℕ) :
    π (S ×ˢ (cavitySpatialTargetExhaustion (B := B) R₀ n)ᶜ) ≤
      π (cavityLongEdgeWindow U (ENNReal.ofReal (((n : ℝ) + 1) ^ 2))) :=
  measure_mono (source_tail_subset_longEdgeWindow S U R₀ hS hR₀ n)

end OTSelector.Probability

end
end
