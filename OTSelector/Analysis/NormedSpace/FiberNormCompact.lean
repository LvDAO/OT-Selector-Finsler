import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Module.RCLike.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.ContinuousOn
import Mathlib.Topology.Order.Compact

/-!
## Lemma skeleton

* **Conditions:** A compact base set, continuous positive absolutely homogeneous fiber lengths and finite-dimensional fibers.
* **Objects:** Uniform coercivity and compact sets with bounded fiber length.
* **Proof detail:** Minimize on base×unit sphere, bound the ambient fiber norm, and take a closed subset of a compact product.

## Mathematical sources

* Matias Dahl, *An brief introduction to Finsler geometry (12 July 2006 author manuscript)*, Section 1.1, Remarks 1.3(6)–(9), pp. 4–5.
  https://math.aalto.fi/~fdahl/finsler/finsler.pdf#page=4

**Relationship to the sources:** The parameter-dependent compact slab is derived from the same sphere compactness method; it also covers nonconvex lengths.
-/

/-!
# Compact speed ranges for continuous finite-dimensional fiber norms

On a compact base set, positivity and homogeneity yield a uniform lower bound by the
reference norm. Consequently, bounded original fiber length confines velocities to a
compact ball. Closed speed ranges are compact, including ranges bounded away from zero.
The bounds are derived from the original continuous family, not supplied separately.
-/

open Set Metric

namespace OTSelector.Geometry

variable {B E : Type*} [TopologicalSpace B]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- Positive homogeneous fiber lengths have a uniform positive norm bound on a compact base. -/
theorem exists_fiberNorm_lower_bound_on_compact {K : Set B} (hK : IsCompact K)
    {F : B → E → ℝ} (hcont : ContinuousOn (Function.uncurry F) (K ×ˢ univ))
    (hsmul : ∀ x ∈ K, ∀ (r : ℝ) (v : E), F x (r • v) = |r| * F x v)
    (hpos : ∀ x ∈ K, ∀ v : E, v ≠ 0 → 0 < F x v) :
    ∃ c > (0 : ℝ), ∀ x ∈ K, ∀ v : E, c * ‖v‖ ≤ F x v := by
  have hcompact := hK.prod (isCompact_sphere (0 : E) 1)
  obtain ⟨c, hc, hbound⟩ := hcompact.exists_forall_le'
    (hcont.mono (prod_mono Subset.rfl (subset_univ _))) (a := 0) (by
      intro p hp
      apply hpos p.1 hp.1 p.2
      intro heq
      simpa [heq] using hp.2)
  refine ⟨c, hc, fun x hx v ↦ ?_⟩
  by_cases hv : v = 0
  · subst v
    have hz : F x 0 = 0 := by simpa using hsmul x hx 0 0
    simp [hz]
  · have hw : ‖(‖v‖⁻¹ : ℝ) • v‖ = 1 := norm_smul_inv_norm hv
    have hb := hbound (x, (‖v‖⁻¹ : ℝ) • v) ⟨hx, by simpa using hw⟩
    change c ≤ F x ((‖v‖⁻¹ : ℝ) • v) at hb
    have hn : 0 < ‖v‖ := norm_pos_iff.mpr hv
    rw [hsmul x hx, abs_of_pos (inv_pos.mpr hn)] at hb
    calc
      c * ‖v‖ ≤ (‖v‖⁻¹ * F x v) * ‖v‖ := mul_le_mul_of_nonneg_right hb hn.le
      _ = F x v := by field_simp

/-- A closed range of original speeds over a compact base is compact. -/
theorem isCompact_fiberNorm_closed_range [T2Space B] {K : Set B} (hK : IsCompact K)
    {F : B → E → ℝ} (hcont : ContinuousOn (Function.uncurry F) (K ×ˢ univ))
    (hsmul : ∀ x ∈ K, ∀ (r : ℝ) (v : E), F x (r • v) = |r| * F x v)
    (hpos : ∀ x ∈ K, ∀ v : E, v ≠ 0 → 0 < F x v) (a b : ℝ) :
    IsCompact {p : B × E | p.1 ∈ K ∧ F p.1 p.2 ∈ Icc a b} := by
  obtain ⟨c, hc, hbound⟩ := exists_fiberNorm_lower_bound_on_compact hK hcont hsmul hpos
  have hclosed : IsClosed ((K ×ˢ (univ : Set E)) ∩ Function.uncurry F ⁻¹' Icc a b) :=
    hcont.preimage_isClosed_of_isClosed (hK.isClosed.prod isClosed_univ) isClosed_Icc
  apply (hK.prod (isCompact_closedBall (0 : E) (b / c))).of_isClosed_subset
    (by convert hclosed using 1; ext p; simp [Function.uncurry])
  intro p hp
  refine ⟨hp.1, ?_⟩
  rw [mem_closedBall, dist_zero_right]
  exact (le_div_iff₀ hc).2 (by nlinarith [hbound p.1 hp.1 p.2, hp.2.2])

end OTSelector.Geometry
