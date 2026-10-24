import OTSelector.Geometry.Finsler.Basic
import OTSelector.Geometry.Finsler.DistanceGradientLine
import OTSelector.Geometry.Finsler.Energy.Basic
import OTSelector.Geometry.Finsler.Geodesic.Defs
import OTSelector.Geometry.Finsler.LengthMetric
import OTSelector.MeasureTheory.SmoothCurveVolumeNull

/-!
# Geometry.Finsler.DistanceGradientNull

* **Conditions:** Original chartwise absolutely continuous measure and dimension at least two, with complete Finsler geometry for alignment containment.
* **Objects:** Null singletons and zero measure of the actual equal-distance-differential set.
* **Proof detail:** Cover smooth curve traces by countably many local Lipschitz images, use lower-dimensional Haar nullity and apply the two-fixed-curve containment.

Mathematical sources:
- [D. H. Fremlin, Measure Theory, Volume 2, Chapter 26](https://www1.essex.ac.uk/maths/people/fremlin/chap26.pdf#page=36): Section 264A, p. 36 (Hausdorff covering definition); Proposition 264G, pp. 38–39 (Lipschitz maps); Theorem 264I, pp. 40–41 (top-dimensional Lebesgue comparison).
- [D. H. Fremlin, Measure Theory, Volume 2](https://www1.essex.ac.uk/maths/people/fremlin/chap26.pdf#page=38): Proposition 262D, p. 11; Corollary 262N, p. 17; Proposition 264G, pp. 38–39; Theorem 264I, pp. 40–41.

Source relation (derived): The dimension condition is essential to the curve-null argument and retained explicitly.
-/

/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Geometry.FinslerDistanceGradientNull.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Geometry.FinslerDistanceGradientNull`; the selected original proof blocks follow. -/
section

/-!
# Null sets of coincident original distance differentials

Chartwise absolute continuity makes every actual smooth curve null in dimension at
least two. The proved containment in two fixed complete geodesics then makes the
actual original-distance differential alignment set null. Constant curves also give
null singletons for the same original measure.
-/

open Set MeasureTheory MeasureTheory.Measure Manifold
open scoped Topology ContDiff ENNReal

noncomputable section
namespace OTSelector.Geometry

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [MeasurableSpace M] [OpensMeasurableSpace M] [ChartedSpace E M]

/-- Constant actual curves show that the original chartwise absolutely continuous
measure vanishes on singletons; no nonatomicity assumption is needed. -/
theorem nullSingletonClass_of_chartwise_ac [IsManifold 𝓘(ℝ, E) 1 M]
    (m : Measure E) [IsAddHaarMeasure m] (μ : Measure M)
    (hdim : 2 ≤ Module.finrank ℝ E)
    (hchart : ∀ old : M, (μ.restrict (extChartAt 𝓘(ℝ, E) old).source).map
      (extChartAt 𝓘(ℝ, E) old) ≪ m) : NullSingletonClass μ := by
  constructor
  intro x
  simpa only [range_const] using
    measure_curve_range_eq_zero_of_chartwise_ac m μ hdim hchart
      (contMDiff_const : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) 1 (fun _ : ℝ ↦ x))

namespace ContinuousFinslerNorm.IsSmoothStronglyConvex

variable [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [PreconnectedSpace M]
  {F : ContinuousFinslerNorm E M} (hF : F.IsSmoothStronglyConvex)

include hF

/-- For distinct targets, equality of the two actual original-distance differentials
holds only on a null set for the original chartwise absolutely continuous measure.
The covering geodesics and their nullity are both derived. -/
theorem measure_distanceDifferentialAlignmentSet_eq_zero
    (m : Measure E) [IsAddHaarMeasure m] (μ : Measure M)
    (hdim : 2 ≤ Module.finrank ℝ E)
    (hchart : ∀ old : M, (μ.restrict (extChartAt 𝓘(ℝ, E) old).source).map
      (extChartAt 𝓘(ℝ, E) old) ≪ m)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    {y z : M} (hyz : y ≠ z) : μ (F.distanceDifferentialAlignmentSet y z) = 0 := by
  obtain ⟨c, d, _, _, hc, hd, hsub⟩ :=
    hF.distance_alignment_subset_two_complete_curves hcomplete hyz
  have hcnull := measure_curve_range_eq_zero_of_chartwise_ac m μ hdim hchart
    (hc.of_le (by simp) : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) 1 c)
  have hdnull := measure_curve_range_eq_zero_of_chartwise_ac m μ hdim hchart
    (hd.of_le (by simp) : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) 1 d)
  exact measure_mono_null hsub (measure_union_null hcnull hdnull)

end ContinuousFinslerNorm.IsSmoothStronglyConvex
end OTSelector.Geometry

end
end
