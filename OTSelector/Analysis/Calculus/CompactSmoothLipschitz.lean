import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.MetricSpace.Thickening

/-!
# Analysis.Calculus.CompactSmoothLipschitz

Conditions: A finite-dimensional real normed domain, a C1 map on an open set and a compact subset of that domain.

Objects: A common compact thickening on which the map is Lipschitz.

Proof detail: Bound the derivative uniformly on a compact neighborhood. For near pairs use a small convex ball; for far pairs use compact boundedness and a positive separation cutoff.

## Mathematical sources

- [Jiří Lebl, Basic Analysis II](https://www.jirka.org/ra/realanal2.pdf#page=46): Section 8.4.1, Lemma 8.4.1 and Proposition 8.4.2, pp. 46–47.
- [Terence Tao, An Epsilon of Room, I](https://terrytao.wordpress.com/wp-content/uploads/2012/12/gsm-117-tao3-epsilon1.pdf#page=110): Sections 1.6.2 and 1.8.1, compactness by finite subcovers, pp. 78 and 101–102; Section 1.8.3, Proposition 1.8.10, pp. 107–108 (finite products).

Source relation: Compact-set mean-value corollary; the compact set itself need not be convex.
-/

/-!
# One Lipschitz bound around a compact set of smooth states

A C1 map on an open finite-dimensional domain is Lipschitz on one closed
neighborhood of any compact subset. The compact set need not be convex. This
allows the same smooth inverse or normalization map to transport uniform small
seed errors, without choosing a Lipschitz constant separately at each seed.
-/

open Set Filter Metric
open scoped Topology ContDiff NNReal

namespace OTSelector.Geometry

variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- A compact family of legal states admits one legal compact thickening and one
Lipschitz constant for the given C1 map, including a disconnected compact family. -/
theorem exists_lipschitzOnWith_cthickening_of_contDiffOn
    {f : E → V} {K U : Set E} (hK : IsCompact K) (hU : IsOpen U)
    (hKU : K ⊆ U) (hf : ContDiffOn ℝ 1 f U) :
    ∃ r > 0, IsCompact (cthickening r K) ∧ cthickening r K ⊆ U ∧
      ∃ L : ℝ≥0, LipschitzOnWith L f (cthickening r K) := by
  obtain ⟨δ, hδ, hδU⟩ := hK.exists_cthickening_subset_open hU hKU
  obtain ⟨η, hη, hηK⟩ := hK.exists_isCompact_cthickening
  let r := min δ η
  have hr : 0 < r := lt_min hδ hη
  have hTU : cthickening r K ⊆ U :=
    (cthickening_mono (min_le_left δ η) K).trans hδU
  have hT : IsCompact (cthickening r K) :=
    hηK.of_isClosed_subset isClosed_cthickening (cthickening_mono (min_le_right δ η) K)
  have hlocal : LocallyLipschitzOn (cthickening r K) f := by
    intro x hx
    obtain ⟨L, t, ht, hLt⟩ :=
      (hf.contDiffAt (hU.mem_nhds (hTU hx))).exists_lipschitzOnWith
    exact ⟨L, t, nhdsWithin_le_nhds ht, hLt⟩
  exact ⟨r, hr, hT, hTU, LocallyLipschitzOn.exists_lipschitzOnWith_of_compact hT hlocal⟩

end OTSelector.Geometry
