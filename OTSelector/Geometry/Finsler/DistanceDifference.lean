import OTSelector.Geometry.Finsler.Basic
import OTSelector.Geometry.Finsler.DistanceGradientLine
import OTSelector.Geometry.Finsler.DistanceGradientNull
import OTSelector.Geometry.Finsler.Energy.Basic
import OTSelector.Geometry.Finsler.HopfRinow
import OTSelector.Geometry.Finsler.LengthMetric
import OTSelector.Geometry.Finsler.Rademacher
import OTSelector.Geometry.Manifold.ManifoldNonatomicDifferential

/-!
# Geometry.Finsler.DistanceDifference

* **Conditions:** Dimension at least two, a chartwise absolutely continuous original measure and two distinct targets in complete Finsler geometry.
* **Objects:** Nonzero actual distance-difference derivative almost everywhere and nullity of every level, hence an atomless difference law.
* **Proof detail:** Remove the null covector-alignment set and nondifferentiability exceptions; a density point of a positive-measure level would force its derivative to vanish.

Mathematical sources:
- [D. H. Fremlin, Measure Theory, Volume 2, Chapter 26](https://www1.essex.ac.uk/maths/people/fremlin/chap26.pdf#page=36): Section 264A, p. 36 (Hausdorff covering definition); Proposition 264G, pp. 38–39 (Lipschitz maps); Theorem 264I, pp. 40–41 (top-dimensional Lebesgue comparison).
- [D. H. Fremlin, Measure Theory, Volume 2, Chapter 26](https://www1.essex.ac.uk/maths/people/fremlin/chap26.pdf#page=18): Section 262Q, Rademacher theorem and proof, pp. 18–20; Section 262B(c), p. 10 (Lipschitz implies absolutely continuous on bounded intervals).
- [D. H. Fremlin, Measure Theory, Volume 4](https://www1.essex.ac.uk/maths/people/fremlin/chap47.pdf#page=22): Theorem 472D, pp. 22–23 (Besicovitch Density Theorem).
- [Zhongmin Shen, Landsberg Curvature, S-Curvature and Riemann Curvature, MSRI Publications 50 (2004)](https://library.slmath.org/books/Book50/files/08Sh.pdf#page=11): Section 4, Definition 4.1 and Lemma 4.2, pp. 313–314; equations (4–1), (4–2) and the canonical-lift spray interpretation.

Source relation (derived): Derived from the cited geometric/analytic principles with the exact actual source hypotheses. The local construction and its original phase/covector data are retained, rather than asserted as a verbatim source statement.
-/

/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Geometry.FinslerDistanceDifference.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Geometry.FinslerDistanceDifference`; the selected original proof blocks follow. -/
section

/-!
# Atomless differences of the original Finsler distance

For distinct targets, equality of the two distance differentials confines a point
to two complete smooth curves. These curves have zero chartwise absolutely
continuous volume in dimension at least two. Rademacher differentiability and
the manifold density theorem then show that every distance-difference level is null.
-/

open Set Filter Metric MeasureTheory Manifold
open scoped Topology NNReal ContDiff

noncomputable section
namespace OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [OpensMeasurableSpace M]
  {F : ContinuousFinslerNorm E M} (hF : F.IsSmoothStronglyConvex)
  (m : Measure E) [m.IsAddHaarMeasure] (μ : Measure M)

include hF

/-- Distances to distinct targets have different differentials almost everywhere. -/
theorem ae_mfderiv_distance_sub_ne_zero
    (hdim : 2 ≤ Module.finrank ℝ E)
    (hchart : ∀ old : M, (μ.restrict (extChartAt 𝓘(ℝ, E) old).source).map
      (extChartAt 𝓘(ℝ, E) old) ≪ m)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    {y z : M} (hyz : y ≠ z) :
    let _instDistanceDifferenceDerivativeMetric : MetricSpace M := F.metricSpace
    ∀ᵐ x ∂μ, mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) (fun p ↦ dist p y - dist p z) x ≠ 0 := by
  let _instDistanceDifferenceDerivativeProofMetric : MetricSpace M := F.metricSpace
  let _instDistanceDifferenceDerivativeNull : NullSingletonClass μ :=
    nullSingletonClass_of_chartwise_ac m μ hdim hchart
  have hdy := F.ae_mdifferentiableAt_distance_of_complete m μ hcomplete hchart y
  have hdz := F.ae_mdifferentiableAt_distance_of_complete m μ hcomplete hchart z
  have hbad : ∀ᵐ x ∂μ, x ∉ F.distanceDifferentialAlignmentSet y z := by
    simpa only [ae_iff, not_not, Set.ofPred_mem_eq] using
      hF.measure_distanceDifferentialAlignmentSet_eq_zero m μ hdim hchart hcomplete hyz
  filter_upwards [hdy, hdz, hbad, μ.ae_ne y, μ.ae_ne z] with x hx hy hn hxy hxz
  intro hz
  apply hn
  change x ≠ y ∧ x ≠ z ∧ _ ∧ _ ∧ _
  refine ⟨hxy, hxz, hx, hy, ?_⟩
  change mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ)
    ((fun p ↦ dist p y) - fun p ↦ dist p z) x = 0 at hz
  rw [mfderiv_sub hx hy] at hz
  exact sub_eq_zero.mp hz

/-- Every difference of distances to distinct targets has an atomless original law. -/
theorem nullSingletonClass_map_distance_sub
    (hdim : 2 ≤ Module.finrank ℝ E)
    (hchart : ∀ old : M, (μ.restrict (extChartAt 𝓘(ℝ, E) old).source).map
      (extChartAt 𝓘(ℝ, E) old) ≪ m)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    {y z : M} (hyz : y ≠ z) :
    let _instDistanceDifferenceLawMetric : MetricSpace M := F.metricSpace
    NullSingletonClass (μ.map (fun x ↦ dist x y - dist x z)) := by
  let _instDistanceDifferenceLawProofMetric : MetricSpace M := F.metricSpace
  let _instDistanceDifferenceLawProper : ProperSpace M := F.properSpace_of_complete hcomplete
  apply nullSingletonClass_map_of_ae_mfderiv_ne_zero m μ hchart
    ((continuous_id.dist continuous_const).sub (continuous_id.dist continuous_const))
  · filter_upwards [F.ae_mdifferentiableAt_distance_of_complete m μ hcomplete hchart y,
      F.ae_mdifferentiableAt_distance_of_complete m μ hcomplete hchart z] with x hx hy
    exact hx.sub hy
  · exact hF.ae_mfderiv_distance_sub_ne_zero m μ hdim hchart hcomplete hyz

/-- Each level of the difference of two original distances has zero original measure. -/
theorem measure_distance_sub_eq_zero
    (hdim : 2 ≤ Module.finrank ℝ E)
    (hchart : ∀ old : M, (μ.restrict (extChartAt 𝓘(ℝ, E) old).source).map
      (extChartAt 𝓘(ℝ, E) old) ≪ m)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    {y z : M} (hyz : y ≠ z) (c : ℝ) :
    let _instDistanceDifferenceFiberMetric : MetricSpace M := F.metricSpace
    μ {x | dist x y - dist x z = c} = 0 := by
  let _instDistanceDifferenceFiberProofMetric : MetricSpace M := F.metricSpace
  let _instDistanceDifferenceFiberNull :
      NullSingletonClass (μ.map (fun x ↦ dist x y - dist x z)) :=
    hF.nullSingletonClass_map_distance_sub m μ hdim hchart hcomplete hyz
  have hc := measure_singleton (μ := μ.map (fun x ↦ dist x y - dist x z)) c
  have hmeas : Measurable (fun x : M ↦ dist x y - dist x z) :=
    ((continuous_id.dist continuous_const).sub (continuous_id.dist continuous_const)).measurable
  rw [Measure.map_apply hmeas (measurableSet_singleton c)] at hc
  exact hc

end OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

end
end
