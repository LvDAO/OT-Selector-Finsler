import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Topology.Algebra.Ring.Real
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Topology.Order.Compact

/-!
# Transport.CompactCalibrationSlack

## Lemma skeleton

* **Conditions:** Continuous parameterized endpoints on a compact parameter set; a one-Lipschitz potential and continuous separation coordinate whose nonzero values exclude zero distance slack.

* **Objects:** A positive calibration-slack gap away from the zero-separation locus, and a distant-edge mass bound for nonnegative finite plans.

* **Proof detail:** On the compact closed subset where separation≥r, the nonnegative slack has no zero; take its positive minimum. Multiply the lower cost gap by each far-edge weight and sum, then divide by the gap.

## Mathematical sources

- [Jiří Lebl, Basic Analysis I: Introduction to Real Analysis, Volume I](https://www.jirka.org/ra/html/sec_metcont.html): Section 7.5, Lemma 7.5.5 (compact continuous images), Theorem 7.5.6 (extreme values), and Exercise 7.5.6 (intermediate value theorem).
- [Rick Durrett, Probability: Theory and Examples, 5th edition (11 January 2019)](https://sites.math.duke.edu/~rtd/PTE/PTE5_011119.pdf#page=37): Section 1.6.1, Theorem 1.6.4 and equation (1.6.1), pp. 29–30.
- [J. C. Álvarez Paiva; A. C. Thompson, Volumes on Normed and Finsler Spaces, MSRI Publications 50 (2004)](https://library.slmath.org/books/Book50/files/02AT.pdf#page=22): Section 4.2, Definition 4.11 and Proposition 4.12, p. 22.

Source relation (corollary): Compact-minimum localization plus a finite weighted Markov bound; no rate of differentiability is assumed.
-/

/-!
# Compact distance slack localization

A continuous separation coordinate which vanishes on calibrated pairs has a
strictly positive distance slack away from zero on compact parameter sets.
The same gap controls the mass of distant edges in any nonnegative finite plan.
-/

open Set Metric
open scoped Topology BigOperators

namespace OTSelector.Geometry

/-- Compactness turns the actual zero-slack relation into a uniform positive
cost gap for a fixed positive continuous separation threshold. -/
theorem exists_distance_slack_gap_of_compact
    {α M : Type*} [TopologicalSpace α] [PseudoMetricSpace M]
    {K : Set α} (hK : IsCompact K) {X Y : α → M} {u : M → ℝ} {s : α → ℝ}
    (hX : ContinuousOn X K) (hY : ContinuousOn Y K) (hu : LipschitzWith 1 u)
    (hs : ContinuousOn s K)
    (hzero : ∀ p ∈ K, dist (X p) (Y p) - u (Y p) + u (X p) = 0 → s p = 0)
    {r : ℝ} (hr : 0 < r) :
    ∃ δ > 0, ∀ p ∈ K, r ≤ s p → δ ≤ dist (X p) (Y p) - u (Y p) + u (X p) := by
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let C : Set K := {p | r ≤ s p}
  have hc : IsCompact C :=
    (isClosed_le continuous_const (continuousOn_iff_continuous_domRestrict.mp hs)).isCompact
  have hf : Continuous (fun p : K ↦ dist (X p) (Y p) - u (Y p) + u (X p)) :=
    ((continuousOn_iff_continuous_domRestrict.mp hX).dist
      (continuousOn_iff_continuous_domRestrict.mp hY)).sub
        (hu.continuous.comp (continuousOn_iff_continuous_domRestrict.mp hY)) |>.add
        (hu.continuous.comp (continuousOn_iff_continuous_domRestrict.mp hX))
  obtain ⟨δ, hδ, hbound⟩ := hc.exists_forall_le' hf.continuousOn (a := 0) (by
    intro p hp
    have hnonneg := hu.le_add_mul (Y p) (X p)
    simp only [NNReal.coe_one, one_mul, dist_comm (Y p) (X p)] at hnonneg
    have hn : dist (X p) (Y p) - u (Y p) + u (X p) ≠ 0 := by
      intro heq
      have hz := hzero p p.property heq
      change r ≤ s p at hp
      rw [hz] at hp
      exact (not_le_of_gt hr) hp
    exact lt_of_le_of_ne (by linarith) hn.symm)
  exact ⟨δ, hδ, fun p hp hpr ↦ hbound ⟨p, hp⟩ hpr⟩

/-- A positive cost gap bounds the total weight of distant edges by the full
nonnegative cost, without requiring an optimizer or a particular tie-breaking rule. -/
theorem distant_edge_weight_le_cost_div_gap
    {ι : Type*} (I : Finset ι) (far : ι → Prop) [DecidablePred far]
    (weight cost : ι → ℝ) (hw : ∀ i ∈ I, 0 ≤ weight i) (hc : ∀ i ∈ I, 0 ≤ cost i)
    {δ : ℝ} (hδ : 0 < δ) (hgap : ∀ i ∈ I, far i → δ ≤ cost i) :
    (∑ i ∈ I with far i, weight i) ≤ (∑ i ∈ I, weight i * cost i) / δ := by
  apply (le_div_iff₀ hδ).mpr
  rw [Finset.sum_mul]
  calc
    ∑ i ∈ I with far i, weight i * δ ≤
        ∑ i ∈ I with far i, weight i * cost i := by
      apply Finset.sum_le_sum
      intro i hi
      obtain ⟨hi, hfar⟩ := Finset.mem_filter.mp hi
      exact mul_le_mul_of_nonneg_left (hgap i hi hfar) (hw i hi)
    _ ≤ ∑ i ∈ I, weight i * cost i :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun i hi _ ↦ mul_nonneg (hw i hi) (hc i hi))

end OTSelector.Geometry
