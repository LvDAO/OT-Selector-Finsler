import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.Normed.Module.Dual
import Mathlib.Analysis.ODE.Basic
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.Riemannian.Basic
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Geometry.FinslerComparisonGraphDomain; OTSelector.Geometry.FinslerSeedEndpointIntervals.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Geometry.FinslerComparisonGraphDomain`; the selected original proof blocks follow. -/
section

/-!
Conditions: An open product set contains the given parameter/time point.

Objects: A nontrivial closed time interval centered around that actual point and contained in the same open set.

Proof detail: Take a product neighborhood, shrink its time radius and choose two interior endpoints.

Sources: D. H. Fremlin, Section 4A2A–4A2B, pp. 6–10 (closures, Hausdorff spaces, continuity and products) (https://www1.essex.ac.uk/maths/people/fremlin/chap4a.pdf#page=6).
Relation: Elementary product-topology corollary; only the selected interval lemma is covered from the original file.
-/

/-!
# Constructed regular domains for the comparison's same graph coordinates

The complete comparison supplies the required C² position germ. Its actual positive
adapted velocity then constructs an open domain in the chosen graph chart, retaining
that chart and any prescribed graph-phase domain. Closed time neighborhoods lie inside
this domain, so the same geometric data remain valid at both endpoints.
-/

open Set Filter Manifold
open scoped Topology ContDiff

noncomputable section
namespace OTSelector.Geometry

variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]

omit [NormedSpace ℝ W] in
/-- An open time-label neighborhood contains a genuine closed time interval about its anchor. -/
theorem exists_closedTime_interval_in_open_domain {U : Set (W × ℝ)} (hU : IsOpen U)
    {w : W} {t₀ : ℝ} (ht₀ : (w, t₀) ∈ U) :
    ∃ a b : ℝ, a < t₀ ∧ t₀ < b ∧ ∀ t ∈ Icc a b, (w, t) ∈ U := by
  have hn : {t : ℝ | (w, t) ∈ U} ∈ 𝓝 t₀ :=
    (continuous_const.prodMk continuous_id).continuousAt.preimage_mem_nhds (hU.mem_nhds ht₀)
  obtain ⟨a, b, _, hab, hsub⟩ := exists_Icc_mem_subset_of_mem_nhds hn
  have ht : t₀ ∈ Ioo a b := by
    rw [← interior_Icc]
    exact mem_interior_iff_mem_nhds.mpr hab
  exact ⟨a, b, ht.1, ht.2, hsub⟩


end OTSelector.Geometry

end
end

/-! Original source unit: `OTSelector.Geometry.FinslerSeedEndpointIntervals`; the selected original proof blocks follow. -/
section

/-!
Conditions: An open subset of a product contains the indicated parameter/time point and the original time span has the stated ordering.

Objects: A nontrivial closed one-sided time interval ending at that point inside the open set and span.

Proof detail: Choose a product neighborhood at the point and shrink the time radius below the available endpoint gap.

Sources: D. H. Fremlin, Section 4A2A–4A2B, pp. 6–10 (closures, Hausdorff spaces, continuity and products) (https://www1.essex.ac.uk/maths/people/fremlin/chap4a.pdf#page=6).
Relation: Elementary product-topology/order lemma, proved locally.
-/

/-!
# Closed physical intervals reaching actual support endpoints

An open time-label domain containing a true endpoint contains a nontrivial closed
one-sided interval reaching that endpoint. The other endpoint remains strictly
inside the prescribed finite support span.
-/

open Set Filter
open scoped Topology

namespace OTSelector.Geometry

variable {W : Type*} [NormedAddCommGroup W]

/-- A true left endpoint has a closed right neighborhood inside the same open
geometric domain, with its other endpoint strictly before the support's right end. -/
theorem exists_left_endpoint_interval_in_open_domain {U : Set (W × ℝ)}
    (hU : IsOpen U) {w : W} {a b : ℝ} (ha : (w, a) ∈ U) (hab : a < b) :
    ∃ l : ℝ, a < l ∧ l < b ∧ ∀ t ∈ Icc a l, (w, t) ∈ U := by
  obtain ⟨L, H, hL, hH, hspan⟩ := exists_closedTime_interval_in_open_domain hU ha
  obtain ⟨l, hal, hl⟩ := exists_between (lt_min hab hH)
  refine ⟨l, hal, hl.trans_le (min_le_left _ _), ?_⟩
  intro t ht
  exact hspan t ⟨hL.le.trans ht.1, ht.2.trans (hl.trans_le (min_le_right _ _)).le⟩

/-- A true right endpoint has a closed left neighborhood inside the same open
geometric domain, with its other endpoint strictly after the support's left end. -/
theorem exists_right_endpoint_interval_in_open_domain {U : Set (W × ℝ)}
    (hU : IsOpen U) {w : W} {a b : ℝ} (hb : (w, b) ∈ U) (hab : a < b) :
    ∃ h : ℝ, a < h ∧ h < b ∧ ∀ t ∈ Icc h b, (w, t) ∈ U := by
  obtain ⟨L, H, hL, hH, hspan⟩ := exists_closedTime_interval_in_open_domain hU hb
  obtain ⟨h, hh, hhb⟩ := exists_between (max_lt hab hL)
  refine ⟨h, (le_max_left _ _).trans_lt hh, hhb, ?_⟩
  intro t ht
  exact hspan t ⟨((le_max_right _ _).trans_lt hh).le.trans ht.1, ht.2.trans hH.le⟩

end OTSelector.Geometry

end
