import Mathlib.Tactic.Linarith
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Topology.MetricSpace.Thickening

/-!
## Lemma skeleton

* **Conditions:** A metric space with approximate splitting at every intermediate radius; completeness to close limiting balls and local compactness to enlarge a compact ball.
* **Objects:** The MetricApproximateSplit property, compactness at a limiting radius, larger compact balls and properness.
* **Proof detail:** Approximate splitting produces finite epsilon-nets from smaller compact balls. Compact thickenings enlarge existing balls. The supremum of compact-ball radii cannot be finite.

## Mathematical sources

* Anton Petrunin, *Lectures on metric geometry*, Lecture 1, Section L, Theorem 1.30 (Hopf–Rinow), Exercise 1.31 and proof, pp. 18–19.
  https://anton-petrunin.github.io/metric-geometry/tex/lectures.pdf#page=18
* Anton Petrunin, *Lectures on metric geometry*, Lecture 1, Section G, Definition 1.11(c) and Exercise 1.13, p. 12.
  https://anton-petrunin.github.io/metric-geometry/tex/lectures.pdf#page=12
* Anton Petrunin, *Lectures on metric geometry (author lecture notes, course Spring 2020)*, Lecture 1, Section L, pp. 16–17: length spaces, induced length metric and approximate midpoints.
  https://anton-petrunin.github.io/metric-geometry/tex/lectures.pdf#page=16

**Relationship to the sources:** Direct metric Hopf–Rinow proof with the length-space assumption replaced by its approximate-splitting consequence; the compact-ball proof is split into reusable lemmas.
-/

/-!
# Properness from approximate length splitting

A complete locally compact metric space is proper when distances admit approximate
splitting at every prescribed intermediate radius. The proof uses compact thickenings
to extend compact balls and total boundedness to close the limiting radius. Neither a
uniform local compactness radius nor existence of minimizing curves is assumed.
-/

open Set Metric

namespace OTSelector.Geometry

/-- Distances can be split, up to arbitrary positive error, at any intermediate radius.
This property follows from genuine length distance and does not posit a minimizing curve. -/
def MetricApproximateSplit (X : Type*) [MetricSpace X] : Prop :=
  ∀ x y : X, ∀ r : ℝ, 0 ≤ r → r ≤ dist x y → ∀ ε > 0,
    ∃ z, dist x z < r + ε ∧ dist z y < dist x y - r + ε

namespace MetricApproximateSplit

variable {X : Type*} [MetricSpace X] (h : MetricApproximateSplit X)

include h

/-- Compactness of every smaller concentric ball implies compactness at the limiting
radius in a complete space with approximate length splitting. -/
theorem isCompact_closedBall_of_lt [CompleteSpace X] (x : X) {r : ℝ}
    (hc : ∀ s < r, IsCompact (closedBall x s)) : IsCompact (closedBall x r) := by
  apply TotallyBounded.isCompact_of_isClosed _ isClosed_closedBall
  apply Metric.totallyBounded_iff.mpr
  intro ε hε
  by_cases hr : r ≤ ε / 4
  · refine ⟨{x}, finite_singleton x, ?_⟩
    intro y hy
    simp only [mem_iUnion, mem_singleton_iff, exists_prop, exists_eq_left]
    exact (mem_closedBall.mp hy).trans_lt (by linarith)
  · have hrε : ε / 4 < r := lt_of_not_ge hr
    obtain ⟨t, ht, hcover⟩ := Metric.totallyBounded_iff.mp
      (hc (r - ε / 8) (by linarith)).totallyBounded (ε / 2) (by linarith)
    refine ⟨t, ht, ?_⟩
    intro y hy
    have hy' : dist x y ≤ r := by simpa [dist_comm] using hy
    have hnear : ∃ z ∈ closedBall x (r - ε / 8), dist y z < ε / 2 := by
      by_cases hxy : dist x y ≤ r - ε / 4
      · exact ⟨y, by simp only [mem_closedBall]; rw [dist_comm]; linarith,
          by simpa using (half_pos hε)⟩
      · obtain ⟨z, hxz, hzy⟩ := h x y (r - ε / 4) (by linarith)
          (by linarith) (ε / 8) (by linarith)
        refine ⟨z, ?_, ?_⟩
        · simp only [mem_closedBall]
          rw [dist_comm]
          linarith
        · rw [dist_comm]
          linarith
    obtain ⟨z, hz, hyz⟩ := hnear
    obtain ⟨a, hat, hza⟩ := mem_iUnion₂.mp (hcover hz)
    apply mem_iUnion₂.mpr
    refine ⟨a, hat, ?_⟩
    have hza' : dist z a < ε / 2 := hza
    exact (dist_triangle y z a).trans_lt (by linarith)

/-- A compact positive-radius ball can be extended to a larger compact ball.
The extension radius is obtained from local compactness along the existing compact ball. -/
theorem exists_gt_isCompact_closedBall [LocallyCompactSpace X] (x : X) {r : ℝ}
    (hr : 0 < r) (hc : IsCompact (closedBall x r)) :
    ∃ s > r, IsCompact (closedBall x s) := by
  obtain ⟨δ, hδ, hcompact⟩ := hc.exists_isCompact_cthickening
  let η := min δ r / 4
  have hη : 0 < η := by dsimp [η]; positivity
  have hηδ : η ≤ δ / 4 := by
    dsimp [η]
    exact div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num)
  have hηr : η ≤ r / 4 := by
    dsimp [η]
    exact div_le_div_of_nonneg_right (min_le_right _ _) (by norm_num)
  refine ⟨r + η, by linarith, hcompact.of_isClosed_subset isClosed_closedBall ?_⟩
  intro y hy
  have hy' : dist x y ≤ r + η := by simpa [dist_comm] using hy
  by_cases hxy : dist x y ≤ r
  · apply self_subset_cthickening _
    simpa [dist_comm] using hxy
  · obtain ⟨z, hxz, hzy⟩ := h x y (r - η) (by linarith)
      (by linarith) (η / 2) (by linarith)
    apply mem_cthickening_of_dist_le y z δ (closedBall x r)
    · simp only [mem_closedBall]
      rw [dist_comm]
      linarith
    · rw [dist_comm]
      linarith

/-- The metric Hopf--Rinow properness conclusion follows from completeness, local
compactness and approximate length splitting alone. -/
theorem properSpace [CompleteSpace X] [LocallyCompactSpace X] : ProperSpace X := by
  constructor
  intro x r
  let S : Set ℝ := {s | 0 < s ∧ IsCompact (closedBall x s)}
  obtain ⟨a, ha, hac⟩ := Metric.exists_isCompact_closedBall x
  have haS : a ∈ S := ⟨ha, hac⟩
  have hSne : S.Nonempty := ⟨a, haS⟩
  have hunbounded : ¬ BddAbove S := by
    intro hb
    let R := sSup S
    have haR : a ≤ R := le_csSup hb haS
    have hR : 0 < R := ha.trans_le haR
    have hRc : IsCompact (closedBall x R) := h.isCompact_closedBall_of_lt x fun s hs ↦ by
      obtain ⟨t, ht, hst⟩ := exists_lt_of_lt_csSup hSne hs
      exact ht.2.of_isClosed_subset isClosed_closedBall (closedBall_subset_closedBall hst.le)
    obtain ⟨s, hRs, hsc⟩ := h.exists_gt_isCompact_closedBall x hR hRc
    have hsR : s ≤ R := le_csSup hb (show s ∈ S from ⟨hR.trans hRs, hsc⟩)
    exact (not_lt_of_ge hsR) hRs
  obtain ⟨s, hs, hrs⟩ := not_bddAbove_iff.mp hunbounded r
  exact hs.2.of_isClosed_subset isClosed_closedBall (closedBall_subset_closedBall hrs.le)

end MetricApproximateSplit
end OTSelector.Geometry
