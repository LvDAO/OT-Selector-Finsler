import OTSelector.Geometry.Finsler.Basic
import OTSelector.Geometry.Finsler.CalibratedLevelSeedPatch
import OTSelector.Geometry.Finsler.CalibratedSeedWindow
import OTSelector.Geometry.Finsler.Energy.Basic
import OTSelector.Geometry.Finsler.Geodesic.Basic
import OTSelector.Geometry.Finsler.LengthMetric
import OTSelector.Geometry.Finsler.SeedCalibrationSpan
import OTSelector.MeasureTheory.CompactAtomlessSupportSpan
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Geometry.FinslerSeedSupportEndpoints.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Geometry.FinslerSeedSupportEndpoints`; the selected original proof blocks follow. -/
section

/-!
# Geometry.Finsler.SeedSupportEndpoints

* **Conditions:** A compact scalar support calibrated along the same complete seed, with the stated nondegeneracy/atomlessness hypotheses.
* **Objects:** Attained finite physical time endpoints, full-measure open support span and rational windows covering that span.
* **Proof detail:** Take compact extrema, extend actual calibration to them by continuity, remove null singleton endpoints and apply the same seed span-cover theorem.

Mathematical sources:
- [Terence Tao, An Epsilon of Room, I: Real Analysis (author preliminary version)](https://terrytao.wordpress.com/wp-content/uploads/2012/12/gsm-117-tao3-epsilon1.pdf#page=110): Sections 1.6.2 and 1.8.1, compactness by finite subcovers, pp. 78 and 101–102; Section 1.8.3, Proposition 1.8.10, pp. 107–108 (finite products).
- [Rick Durrett, Probability: Theory and Examples, 5th edition (11 January 2019)](https://sites.math.duke.edu/~rtd/PTE/PTE5_011119.pdf#page=19): Section 1.2, Theorem 1.2.1(iii)–(v), p. 11.
- [Rotem Assouline, Curvature-Dimension for Autonomous Lagrangians, arXiv:2409.08001v6 (10 February 2026)](https://arxiv.org/pdf/2409.08001v6#page=29): Sections 4–4.1, Definition 4.2 and Proposition 4.3, p. 29; Lemma 4.5, pp. 30–31; Definition 4.6 and Lemma 4.8, pp. 31–32.

Source relation (derived): Atomlessness removes only endpoints; it is an explicit hypothesis, not inferred from scalar compactness.
-/

/-!
# Actual finite support endpoints on the same complete seed curve

Compact scalar support and its original potential offset determine attained physical
time endpoints. Calibration extends to them by continuity of the original complete
curve. Atomlessness removes only the endpoints, and the same countable seed windows
cover the full open span.
-/

open Set Filter MeasureTheory Manifold
open scoped Topology ContDiff

noncomputable section
namespace OTSelector.Geometry.ContinuousFinslerNorm.CalibratedLevelSeedPatch

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] {F : ContinuousFinslerNorm E M} {u : M → ℝ}

omit [BorelSpace E] in
/-- The actual compact scalar law supplies finite calibrated endpoints for the same
complete original curve and loses no mass on passing to their open physical span. -/
theorem exists_compact_support_calibrated_span (S : CalibratedLevelSeedPatch F u)
    (hF : F.IsSmoothStronglyConvex)
    (hu : let _instSupportClockLip : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    {w : S.covector.ker} (hw : w ∈ S.labels)
    (μ : Measure ℝ) [NullSingletonClass μ] (hμ : μ ≠ 0)
    (hcompact : IsCompact μ.support) (u₀ : ℝ)
    (hclock : ∀ᵐ x ∂μ, x - u₀ ∈ S.calibrationTimes w) :
    ∃ a b : ℝ, a < b ∧ u₀ + a ∈ μ.support ∧ u₀ + b ∈ μ.support ∧
      (∀ x ∈ μ.support, x - u₀ ∈ Icc a b) ∧
      (∀ᵐ x ∂μ, x - u₀ ∈ Ioo a b) ∧
      Icc a b ⊆ S.calibrationTimes w ∧
      (∀ t ∈ Ioo a b, ∃ k : S.RationalWindowIndex,
        (t, w) ∈ (S.rationalWindow k).domain) ∧
      Continuous (S.curve w) := by
  obtain ⟨a, b, ha, hb, hab, hbound, hinside⟩ :=
    exists_compact_measure_clock_span μ hμ hcompact
  have hclosed : IsClosed {x : ℝ | x - u₀ ∈ S.calibrationTimes w} :=
    (S.isClosed_calibrationTimes hF hu hw).preimage (continuous_id.sub continuous_const)
  have hsupport : μ.support ⊆ {x : ℝ | x - u₀ ∈ S.calibrationTimes w} :=
    Measure.support_subset_of_isClosed hclosed hclock
  have hleft : a - u₀ ∈ S.calibrationTimes w := hsupport ha
  have hright : b - u₀ ∈ S.calibrationTimes w := hsupport hb
  refine ⟨a - u₀, b - u₀, sub_lt_sub_right hab u₀, ?_, ?_, ?_, ?_,
    S.Icc_subset_calibrationTimes hF hu hw hleft hright, ?_, ?_⟩
  · rwa [show u₀ + (a - u₀) = a by ring]
  · rwa [show u₀ + (b - u₀) = b by ring]
  · intro x hx
    exact ⟨sub_le_sub_right (hbound hx).1 u₀, sub_le_sub_right (hbound hx).2 u₀⟩
  · exact hinside.mono fun x hx ↦
      ⟨sub_lt_sub_right hx.1 u₀, sub_lt_sub_right hx.2 u₀⟩
  · intro t ht
    exact S.exists_rationalWindow_of_calibrated_span hF hu hw hleft hright ht
  · exact continuous_iff_continuousAt.mpr fun t ↦
      (hF.contMDiffAt_of_isEulerLagrangeAt (S.complete w hw t (mem_univ _))).continuousAt

end OTSelector.Geometry.ContinuousFinslerNorm.CalibratedLevelSeedPatch

end
end
