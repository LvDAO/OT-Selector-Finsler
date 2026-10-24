import Mathlib.Analysis.Normed.Group.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.ContinuousOn
import Mathlib.Topology.MetricSpace.Pseudo.Defs

/-!
# Topology.UniformContinuousApproximation

Conditions: A real-valued function on an arbitrary topological carrier admits continuous approximants with arbitrarily small uniform absolute error there.

Objects: Continuity on that same carrier.

Proof detail: Choose an epsilon/3 approximant and combine its continuity with the two uniform approximation errors.

## Mathematical sources

- [Jiří Lebl, Basic Analysis I](https://www.jirka.org/ra/realanal.pdf#page=235): Section 6.2.1, Theorem 6.2.2, p. 235.

Source relation: The standard uniform-limit proof stated directly for accuracy-indexed approximants and an arbitrary topological source.
-/

/-! Uniform real continuous approximations transfer continuity on the same carrier. -/
open Set Filter
open scoped Topology
namespace OTSelector.Reconstruction

/-- Uniform approximation on a fixed carrier suffices for continuity there;
no regularity of the limiting function outside that carrier is required. -/
theorem continuousOn_of_uniform_real_continuous_approx
    {Z : Type*} [TopologicalSpace Z] (f : Z → ℝ) (C : Set Z)
    (happrox : ∀ ε > 0, ∃ g : Z → ℝ, ContinuousOn g C ∧
      ∀ x ∈ C, |f x - g x| ≤ ε) : ContinuousOn f C := by
  intro x hx
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨g, hg, hfg⟩ := happrox (ε / 3) (by positivity)
  have hgg := Metric.tendsto_nhds.mp (hg x hx) (ε / 3) (by positivity)
  filter_upwards [self_mem_nhdsWithin, hgg] with y hy hdist
  rw [Real.dist_eq] at hdist ⊢
  have hyBound := hfg y hy
  have hxBound := hfg x hx
  calc
    |f y - f x| = |(f y - g y) + (g y - g x) + (g x - f x)| := by congr 1; ring
    _ ≤ |f y - g y| + |g y - g x| + |g x - f x| :=
      (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ < ε := by rw [abs_sub_comm (g x) (f x)]; linarith

end OTSelector.Reconstruction
