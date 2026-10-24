import OTSelector.Geometry.Finsler.Basic
import OTSelector.Geometry.Finsler.HopfRinow
import OTSelector.Geometry.Finsler.LengthMetric
import OTSelector.Transport.Kantorovich.CalibratedReach

/-!
# Geometry.Finsler.CalibratedReach

* **Conditions:** Complete original Finsler length metric and a 1-Lipschitz potential.
* **Objects:** Closed positive reach sets, Borel two-sided calibrated interior and a countable compact trimmed contact cover with fixed positive reaches/compact partner carriers.
* **Proof detail:** Use properness to extract calibrated endpoint limits, trim minimizing curves to exact reaches and combine compact exhaustions with countable positive levels.

Mathematical sources:
- [Anton Petrunin, Lectures on metric geometry](https://anton-petrunin.github.io/metric-geometry/tex/lectures.pdf#page=18): Lecture 1, Section L, Theorem 1.30 (Hopf–Rinow), Exercise 1.31 and proof, pp. 18–19.
- [Rotem Assouline, Curvature-Dimension for Autonomous Lagrangians, arXiv:2409.08001v6 (10 February 2026)](https://arxiv.org/pdf/2409.08001v6#page=33): Section 4.2, Lemmas 4.9–4.10, p. 33 (Borel strain/end times and closed trimmed strain sets).
- [D. H. Fremlin, Measure Theory, Volume 4, Appendix](https://www1.essex.ac.uk/maths/people/fremlin/chap4a.pdf#page=24): Sections 4A2G(e), pp. 15–16; 4A2N(b), p. 22; 4A2Q(h) and proof, pp. 24–25.

Source relation (derived): The generic closed-reach/compact-cover argument is derived with actual metric hypotheses, without a prescribed ray atlas or differentiability assumption.
-/

/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Geometry.FinslerCalibratedReach.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Geometry.FinslerCalibratedReach`; the selected original proof blocks follow. -/
section

/-!
# Compact trimmed contact covers for the original Finsler distance

Completeness of the original Finsler length metric supplies properness and genuine
minimizing intervals. An original one-Lipschitz potential therefore has closed positive
reach superlevels and a Borel two-sided calibrated interior, covered by countably many
compact sets with compact endpoint carriers and a common positive reach on each piece.
Neither differentiability of the potential nor a prescribed ray atlas is assumed.
-/

open Set Metric Manifold
open scoped ContDiff

noncomputable section
namespace OTSelector.Geometry.ContinuousFinslerNorm

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) 1 M] [T2Space M] [PreconnectedSpace M]
  (F : ContinuousFinslerNorm E M)

/-- Fixed-distance original calibrated reach levels are closed under original completeness. -/
theorem isClosed_calibratedReachLevel
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace) {u : M → ℝ}
    (hu : let _instFinslerReachLevelMetric : MetricSpace M := F.metricSpace;
      LipschitzWith 1 u) (r : ℝ) :
    let _instFinslerReachLevelMetric : MetricSpace M := F.metricSpace
    IsClosed (OTSelector.Geometry.calibratedReachLevel u r) := by
  let _instFinslerReachLevelMetric : MetricSpace M := F.metricSpace
  let _instFinslerReachLevelProper : ProperSpace M := F.properSpace_of_complete hcomplete
  exact OTSelector.Geometry.isClosed_calibratedReachLevel hu.continuous r

/-- Original calibrated reach of at least r is closed: actual minimizing intervals shorten
any longer calibrated endpoint to the fixed radius, and properness gives closedness. -/
theorem isClosed_calibratedReach_ge
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace) {u : M → ℝ}
    (hu : let _instFinslerReachGeMetric : MetricSpace M := F.metricSpace;
      LipschitzWith 1 u) {r : ℝ} (hr : 0 ≤ r) :
    let _instFinslerReachGeMetric : MetricSpace M := F.metricSpace
    IsClosed {x | ∃ y, r ≤ dist x y ∧ u y - u x = dist x y} := by
  let _instFinslerReachGeMetric : MetricSpace M := F.metricSpace
  have heq : {x | ∃ y, r ≤ dist x y ∧ u y - u x = dist x y} =
      OTSelector.Geometry.calibratedReachLevel u r := by
    ext x
    exact (calibratedReachLevel_iff_exists_ge hu
      (F.exists_lengthMetric_isometric_interval hcomplete) hr).symm
  change IsClosed {x | ∃ y, r ≤ dist x y ∧ u y - u x = dist x y}
  rw [heq]
  exact F.isClosed_calibratedReachLevel hcomplete hu r

/-- The actual two-sided positive-reach set is Borel for the original Finsler potential. -/
theorem measurableSet_calibratedInterior [MeasurableSpace M] [BorelSpace M]
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace) {u : M → ℝ}
    (hu : let _instFinslerReachBorelMetric : MetricSpace M := F.metricSpace;
      LipschitzWith 1 u) :
    let _instFinslerReachBorelMetric : MetricSpace M := F.metricSpace
    MeasurableSet (OTSelector.Geometry.calibratedInterior u) := by
  let _instFinslerReachBorelMetric : MetricSpace M := F.metricSpace
  let _instFinslerReachBorelProper : ProperSpace M := F.properSpace_of_complete hcomplete
  exact OTSelector.Geometry.measurableSet_calibratedInterior hu
    (F.exists_lengthMetric_isometric_interval hcomplete)

/-- The original two-sided calibrated interior has a countable compact trimmed cover,
with compact original endpoint carriers and strictly positive reach on every piece.
No full-volume assertion, smooth potential or transport atlas is an input or conclusion. -/
theorem exists_compact_trimmed_contact_cover
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace) {u : M → ℝ}
    (hu : let _instFinslerTrimmedContactMetric : MetricSpace M := F.metricSpace;
      LipschitzWith 1 u) :
    let _instFinslerTrimmedContactMetric : MetricSpace M := F.metricSpace
    ∃ K A : ℕ × ℕ → Set M,
      (∀ i, IsCompact (K i) ∧ IsCompact (A i)) ∧
      (⋃ i, K i) = OTSelector.Geometry.calibratedInterior u ∧
      ∀ i x, x ∈ K i → ∃ a ∈ A i, ∃ b ∈ A i,
        dist a x = 1 / (i.1 + 1 : ℝ) ∧ u x - u a = 1 / (i.1 + 1 : ℝ) ∧
        dist x b = 1 / (i.1 + 1 : ℝ) ∧ u b - u x = 1 / (i.1 + 1 : ℝ) := by
  let _instFinslerTrimmedContactMetric : MetricSpace M := F.metricSpace
  let _instFinslerTrimmedContactProper : ProperSpace M := F.properSpace_of_complete hcomplete
  exact OTSelector.Geometry.exists_compact_trimmed_contact_cover hu
    (F.exists_lengthMetric_isometric_interval hcomplete)

end OTSelector.Geometry.ContinuousFinslerNorm

end
end
