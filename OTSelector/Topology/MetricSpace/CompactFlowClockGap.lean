import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Topology.MetricSpace.Pseudo.Constructions
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import Mathlib.Topology.UniformSpace.HeineCantor

/-!
# Topology.MetricSpace.CompactFlowClockGap

## Lemma skeleton

* **Conditions:** A continuous clock flow on a compact label×time set, a same-label length upper bound, and a positive metric separation between the two target supports.

* **Objects:** A common label radius that forces a uniform clock gap for separated-support endpoints.

* **Proof detail:** Uniform continuity on the compact product bounds the change caused by a nearby label at fixed time. Combine it with the same-label clock estimate and the metric triangle inequality, taking the error below half the support gap.

## Mathematical sources

- [Terence Tao, An Epsilon of Room, I: Real Analysis (author preliminary version)](https://terrytao.wordpress.com/wp-content/uploads/2012/12/gsm-117-tao3-epsilon1.pdf#page=110): Sections 1.6.2 and 1.8.1, compactness by finite subcovers, pp. 78 and 101–102; Section 1.8.3, Proposition 1.8.10, pp. 107–108 (finite products).
- [Jiří Lebl, Basic Analysis I: Introduction to Real Analysis, Volume I](https://www.jirka.org/ra/html/sec_metcont.html): Section 7.5, Lemma 7.5.5 (compact continuous images), Theorem 7.5.6 (extreme values), and Exercise 7.5.6 (intermediate value theorem).

Source relation (corollary): Local compact-flow estimate. Continuity of conditional supports is not required or silently inserted.
-/

/-!
# Original support separation in continuous compact clock coordinates

A true metric support gap and the actual same-label length bound imply a
uniform clock gap for close labels. No continuity of conditional supports is
required. The flow is used only on its given compact set.
-/
open Set Function Metric
noncomputable section
namespace OTSelector.Geometry
variable {Z M : Type*} [PseudoMetricSpace Z] [PseudoMetricSpace M]

omit [PseudoMetricSpace Z] in
/-- True metric separation controls clock separation through one original
same-label path and one same-clock change of label. -/
theorem clock_gap_of_support_separation
    (b : Z → ℝ → M) {z z' : Z} {s t gap error : ℝ}
    (hgap : gap ≤ dist (b z s) (b z' t))
    (hclock : dist (b z s) (b z t) ≤ |t - s|)
    (hlabel : dist (b z t) (b z' t) ≤ error) :
    gap - error ≤ |t - s| := by
  have htri := dist_triangle (b z s) (b z t) (b z' t)
  linarith

/-- Compact continuity supplies a common label scale for all clocks in the
original compact clock range. The gap is the original metric support gap. -/
theorem exists_uniform_clock_gap_of_compact_flow
    {K : Set Z} {T : Set ℝ} (hK : IsCompact K) (hT : IsCompact T)
    (b : Z → ℝ → M) (hb : ContinuousOn (Function.uncurry b) (K ×ˢ T))
    (hclock : ∀ z ∈ K, ∀ s ∈ T, ∀ t ∈ T,
      dist (b z s) (b z t) ≤ |t - s|)
    {A B : Set M} {gap : ℝ} (hgap : 0 < gap)
    (hsep : ∀ x ∈ A, ∀ y ∈ B, gap ≤ dist x y) :
    ∃ radius : ℝ, 0 < radius ∧ ∀ z ∈ K, ∀ z' ∈ K, ∀ s ∈ T, ∀ t ∈ T,
      dist z z' < radius → b z s ∈ A → b z' t ∈ B →
      gap / 2 ≤ |t - s| := by
  have huc := (hK.prod hT).uniformContinuousOn_of_continuous hb
  obtain ⟨radius, hradius, hclose⟩ := Metric.uniformContinuousOn_iff.mp huc
    (gap / 2) (half_pos hgap)
  refine ⟨radius, hradius, fun z hz z' hz' s hs t ht hzz hx hy ↦ ?_⟩
  have hdist : dist (z, t) (z', t) < radius := by
    simpa only [Prod.dist_eq, dist_self, max_eq_left (dist_nonneg)] using hzz
  have hlabel : dist (b z t) (b z' t) ≤ gap / 2 :=
    (hclose (z, t) ⟨hz, ht⟩ (z', t) ⟨hz', ht⟩ hdist).le
  have h := clock_gap_of_support_separation b (hsep _ hx _ hy)
    (hclock z hz s hs t ht) hlabel
  linarith

end OTSelector.Geometry
