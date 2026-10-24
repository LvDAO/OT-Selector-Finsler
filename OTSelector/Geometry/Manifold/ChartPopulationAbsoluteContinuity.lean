import OTSelector.Geometry.Manifold.ChartPopulationDensity
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Geometry.ChartPopulationAbsoluteContinuity.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Geometry.ChartPopulationAbsoluteContinuity`; the selected original proof blocks follow. -/
section

/-!
Conditions: A chart volume density and a nonnegative population density with the stated measurability assumptions.

Objects: Absolute continuity of the chart-pushed population law and its density formula.

Proof detail: Combine the reference chart density with the population withDensity identity and use transitivity of absolute continuity.

Sources: D. H. Fremlin, Sections 232E–232I, Radon–Nikodym and Lebesgue decomposition; Section 235K, change of measure (https://www1.essex.ac.uk/maths/people/fremlin/chap23.pdf); D. H. Fremlin, Section 235G, integration along an inverse-measure-preserving map (https://www1.essex.ac.uk/maths/people/fremlin/chap23.pdf).
Relation: A chart adapter for density transport; it contains no independence or iid assertion.
-/

/-!
# Chartwise absolute continuity of original physical populations

A physical density with respect to the original smooth volume has an absolutely
continuous chart law whenever that volume has its actual coordinate density.
Continuity of the volume density is needed only on the chart target. This
reuses the exact density pushforward and supplies the geometric iid hypotheses.
-/

open MeasureTheory Set Manifold
open scoped Topology ENNReal

namespace OTSelector.Geometry

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [MeasurableSpace M] [BorelSpace M]

/-- Original volume densities imply chartwise absolute continuity of a physical population. -/
theorem chartwise_ac_withDensity_of_volume_density
    (ω : Measure M) (m : Measure E) {ρ : M → ℝ}
    (hρ : Measurable ρ) (hρ0 : ∀ x, 0 ≤ ρ x)
    (v : M → E → ℝ)
    (hv : ∀ old, ContinuousOn (v old) (extChartAt 𝓘(ℝ, E) old).target)
    (hvolume : ∀ old : M, let χ := extChartAt 𝓘(ℝ, E) old
      (ω.restrict χ.source).map χ = (m.restrict χ.target).withDensity
        (fun y ↦ ENNReal.ofReal (v old y))) (old : M) :
    ((ω.withDensity (fun x ↦ ENNReal.ofReal (ρ x))).restrict
      (extChartAt 𝓘(ℝ, E) old).source).map (extChartAt 𝓘(ℝ, E) old) ≪ m := by
  rw [map_extChartAt_withDensity_of_volume_density old ω m hρ hρ0
    ((hv old).aemeasurable (isOpen_extChartAt_target old).measurableSet) (hvolume old)]
  exact (withDensity_absolutelyContinuous _ _).trans Measure.absolutelyContinuous_restrict

end OTSelector.Geometry

end
