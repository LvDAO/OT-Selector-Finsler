import Mathlib.Geometry.Manifold.IsManifold.ExtChartAt
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Reconstruction.FinslerPopulationChartVolume.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Reconstruction.FinslerPopulationChartVolume`; the selected original proof blocks follow. -/
section

/-!
# Geometry.Manifold.ChartVolumeDensityExtension

* **Conditions:** An original chart-volume density is continuous and nonnegative on its chart target; an exact chart pushforward-volume formula is supplied.
* **Objects:** A globally measurable zero extension retaining every target value and the exact physical chart-volume formula.
* **Proof detail:** Use the open chart target for piecewise Borel measurability and replace densities equal on the restricted reference domain.

Mathematical sources:
- [D. H. Fremlin, Measure Theory, Volume 4, Appendix](https://www1.essex.ac.uk/maths/people/fremlin/chap4a.pdf#page=32): Sections 4A3B(a)–(c), p. 32; 4A3C(a)–(f), pp. 32–33.
- [D. H. Fremlin, Measure Theory, Volume 2](https://www1.essex.ac.uk/maths/people/fremlin/chap23.pdf#page=27): Sections 234I–234L, pp. 27–29; especially 234L(c); Section 235K, p. 40.

Source relation (adapter): A generic manifold chart-density extension adapter, independent of transport or Finsler dynamics.
-/

/-!
# Measurable representatives of the original chart volume densities

An actual chart density need only be continuous on its chart target. Extending it
by zero provides a globally measurable representative while retaining the exact
physical volume formula and every value used by an actual chart readout.
-/

open Set MeasureTheory Manifold
open scoped Topology ENNReal

noncomputable section
namespace OTSelector.Reconstruction

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [MeasurableSpace M]

/-- The original coordinate volume density, extended by zero outside its actual chart. -/
def populationChartVolumeExtension (v : M → E → ℝ) (old : M) : E → ℝ :=
  (extChartAt 𝓘(ℝ, E) old).target.indicator (v old)

omit [MeasurableSpace E] [BorelSpace E] [MeasurableSpace M] in
/-- Actual chart coordinates retain the original physical volume factor exactly. -/
theorem populationChartVolumeExtension_eq {v : M → E → ℝ} {old : M} {y : E}
    (hy : y ∈ (extChartAt 𝓘(ℝ, E) old).target) :
    populationChartVolumeExtension v old y = v old y :=
  indicator_of_mem hy _

omit [MeasurableSpace M] in
/-- Continuity only on the original target already supplies a measurable representative. -/
theorem measurable_populationChartVolumeExtension {v : M → E → ℝ} {old : M}
    (hv : ContinuousOn (v old) (extChartAt 𝓘(ℝ, E) old).target) :
    Measurable (populationChartVolumeExtension v old) := by
  classical
  exact hv.measurable_piecewise continuousOn_const (isOpen_extChartAt_target old).measurableSet

omit [MeasurableSpace E] [BorelSpace E] [MeasurableSpace M] in
/-- The measurable representative is continuous on the original chart target. -/
theorem continuousOn_populationChartVolumeExtension {v : M → E → ℝ} {old : M}
    (hv : ContinuousOn (v old) (extChartAt 𝓘(ℝ, E) old).target) :
    ContinuousOn (populationChartVolumeExtension v old) (extChartAt 𝓘(ℝ, E) old).target := by
  apply hv.congr
  intro y hy
  exact populationChartVolumeExtension_eq hy

omit [MeasurableSpace E] [BorelSpace E] [MeasurableSpace M] in
/-- A nonnegative original volume density has a nonnegative representative everywhere. -/
theorem nonneg_populationChartVolumeExtension {v : M → E → ℝ} {old : M}
    (hv : ∀ y ∈ (extChartAt 𝓘(ℝ, E) old).target, 0 ≤ v old y) (y : E) :
    0 ≤ populationChartVolumeExtension v old y := by
  classical
  exact indicator_nonneg (fun y hy ↦ hv y hy) y

/-- Zero extension leaves the original restricted chart-volume identity unchanged. -/
theorem map_extChartAt_eq_withDensity_volumeExtension (ωM : Measure M) (m : Measure E)
    {v : M → E → ℝ} (old : M)
    (hvolume : (ωM.restrict (extChartAt 𝓘(ℝ, E) old).source).map
      (extChartAt 𝓘(ℝ, E) old) =
        (m.restrict (extChartAt 𝓘(ℝ, E) old).target).withDensity
          (fun y ↦ ENNReal.ofReal (v old y))) :
    (ωM.restrict (extChartAt 𝓘(ℝ, E) old).source).map (extChartAt 𝓘(ℝ, E) old) =
      (m.restrict (extChartAt 𝓘(ℝ, E) old).target).withDensity
        (fun y ↦ ENNReal.ofReal (populationChartVolumeExtension v old y)) := by
  rw [hvolume]
  apply withDensity_congr_ae
  filter_upwards [ae_restrict_mem (isOpen_extChartAt_target old).measurableSet] with y hy
  rw [populationChartVolumeExtension_eq hy]

end OTSelector.Reconstruction

end
end
