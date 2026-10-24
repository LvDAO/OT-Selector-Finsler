import Mathlib.Tactic.Linarith
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Topology.Order.Compact

/-!
## Lemma skeleton

* **Conditions:** A proper pseudometric space; one pair admits approximate subdivisions at a fixed real radius for every positive error.
* **Objects:** An exact prescribed-radius subdivision, and in particular an exact midpoint.
* **Proof detail:** Minimize the maximum of the two distance errors on a compact closed ball. Approximate witnesses force the minimum to zero; the triangle inequality forces both equalities.

## Mathematical sources

* Anton Petrunin, *Lectures on metric geometry*, Lecture 1, Section L, Proposition 1.29 and its preceding compact approximate-midpoint argument, p. 18; Section I, p. 13, defines a geodesic as an isometric interval.
  https://anton-petrunin.github.io/metric-geometry/tex/lectures.pdf#page=18
* Jiří Lebl, *Basic Analysis I: Introduction to Real Analysis, Volume I*, Section 7.5, Lemma 7.5.5 (compact continuous images), Theorem 7.5.6 (extreme values), and Exercise 7.5.6 (intermediate value theorem).
  https://www.jirka.org/ra/html/sec_metcont.html

**Relationship to the sources:** Arbitrary-radius and pseudometric extension of the compact approximate-midpoint limit argument preceding Petrunin Proposition 1.29; the proof uses a minimizer instead of a subsequence.
-/

/-!
# Exact metric subdivisions from approximate subdivisions

In a proper metric space, approximate subdivisions of a fixed pair produce an exact
subdivision. The proof minimizes the maximum of the two distance errors on a compact
closed ball. Midpoints follow without choosing a convergent subsequence or constructing
a geodesic in advance. The result applies to the genuine Finsler length metric once
properness and the approximate subdivision property have been derived from the geometry.
-/

open Set Metric

namespace OTSelector.Geometry

variable {X : Type*} [PseudoMetricSpace X] [ProperSpace X]

/-- Approximate subdivisions of one pair in a proper space yield an exact subdivision.
The hypotheses themselves force `0 ≤ r ≤ dist x y`, so these bounds need not be supplied. -/
theorem exists_dist_eq_of_approximate_split (x y : X) (r : ℝ)
    (hsplit : ∀ ε > (0 : ℝ), ∃ z : X,
      dist x z < r + ε ∧ dist z y < dist x y - r + ε) :
    ∃ z : X, dist x z = r ∧ dist z y = dist x y - r := by
  let f : X → ℝ := fun z ↦ max (dist x z - r) (dist z y - (dist x y - r))
  have hf : Continuous f :=
    ((continuous_const.dist continuous_id).sub continuous_const).max
      ((continuous_id.dist continuous_const).sub continuous_const)
  obtain ⟨w, hw, _⟩ := hsplit 1 zero_lt_one
  have hwball : w ∈ closedBall x (r + 1) := by
    rw [mem_closedBall, dist_comm]
    exact hw.le
  obtain ⟨z, _, hz⟩ := (isCompact_closedBall x (r + 1)).exists_isMinOn
    ⟨w, hwball⟩ hf.continuousOn
  have hz0 : f z ≤ 0 := by
    by_contra h
    have hpos : 0 < f z := lt_of_not_ge h
    obtain ⟨a, hax, hay⟩ := hsplit (min 1 (f z)) (lt_min zero_lt_one hpos)
    have haball : a ∈ closedBall x (r + 1) := by
      rw [mem_closedBall, dist_comm]
      exact hax.le.trans (add_le_add_right (min_le_left _ _) _)
    have haf : f a < min 1 (f z) := by
      dsimp [f]
      exact max_lt (by linarith) (by linarith)
    exact (not_lt_of_ge (hz haball)) (haf.trans_le (min_le_right _ _))
  have hxz : dist x z ≤ r := by
    have := (le_max_left (dist x z - r) (dist z y - (dist x y - r))).trans hz0
    linarith
  have hzy : dist z y ≤ dist x y - r := by
    have := (le_max_right (dist x z - r) (dist z y - (dist x y - r))).trans hz0
    linarith
  have htriangle := dist_triangle x z y
  exact ⟨z, by linarith, by linarith⟩

/-- Approximate midpoints in a proper space yield an exact midpoint for the given pair. -/
theorem exists_midpoint_of_approximate_midpoint (x y : X)
    (hmid : ∀ ε > (0 : ℝ), ∃ z : X,
      dist x z < dist x y / 2 + ε ∧ dist z y < dist x y / 2 + ε) :
    ∃ z : X, dist x z = dist x y / 2 ∧ dist z y = dist x y / 2 := by
  have hhalf : dist x y - dist x y / 2 = dist x y / 2 := by linarith
  simpa only [hhalf] using exists_dist_eq_of_approximate_split x y (dist x y / 2)
    (by simpa only [hhalf] using hmid)

end OTSelector.Geometry
