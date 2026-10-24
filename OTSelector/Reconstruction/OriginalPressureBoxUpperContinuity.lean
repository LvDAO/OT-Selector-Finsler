import OTSelector.Probability.GridRepairError
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Tactic

/-! The fixed-box route from actual original law convergence and a uniform
legal parent repair to the thermodynamic upper limit. -/
open Set Function Filter
open scoped Topology
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false

/-- True finite-box convergence and one uniform vanishing parent repair give
the required thermodynamic upper continuity. No lower continuity is inferred
from a one-sided parent estimate. -/
theorem eventually_pressure_lt_of_fixed_box_upper
    {J : Type*} (l : Filter J) (P : J → ℝ) (F : J → ℝ → ℝ)
    (reference error : ℝ → ℝ) (p : ℝ)
    (hupper : ∀ j L, 0 < L → P j ≤ F j L + error L)
    (hfixed : ∀ L, 0 < L → Tendsto (fun j ↦ F j L) l (𝓝 (reference L)))
    (hreference : Tendsto reference atTop (𝓝 p))
    (herror : Tendsto error atTop (𝓝 0)) :
    ∀ ε > 0, ∀ᶠ j in l, P j < p + ε := by
  intro ε hε
  have hsum := hreference.add herror
  change Tendsto (fun L ↦ reference L + error L) atTop (𝓝 (p + 0)) at hsum
  simp only [add_zero] at hsum
  have hlarge : ∀ᶠ L in atTop, reference L + error L < p + ε / 2 :=
    hsum.eventually (eventually_lt_nhds (by linarith : p < p + ε / 2))
  obtain ⟨L,hL,happrox⟩ := ((eventually_gt_atTop (0 : ℝ)).and hlarge).exists
  have hfinite : ∀ᶠ j in l, F j L < reference L + ε / 2 :=
    (hfixed L hL).eventually (eventually_lt_nhds (by linarith : reference L < reference L + ε / 2))
  filter_upwards [hfinite] with j hj
  have h := hupper j L hL
  linarith

end OTSelector.Reconstruction
