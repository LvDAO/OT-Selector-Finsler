import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.GroupTheory.Perm.ViaEmbedding
import Mathlib.MeasureTheory.Measure.FiniteMeasureExt
import Mathlib.MeasureTheory.Measure.SeparableMeasure
import Mathlib.MeasureTheory.Measure.Support
import Mathlib.MeasureTheory.Measure.WithDensityFinite
import Mathlib.MeasureTheory.VectorMeasure.Variation.SignedMeasure
import Mathlib.MeasureTheory.VectorMeasure.WithDensityVec
import Mathlib.Probability.Distributions.Beta
import Mathlib.Probability.Kernel.CompProdEqIff
import Mathlib.Topology.Algebra.Module.Cardinality
import Mathlib.Topology.ContinuousMap.SecondCountableSpace
import OTSelector.Geometry.Finsler.Basic
import OTSelector.Geometry.Finsler.CalibratedLevelSeedPatch
import OTSelector.Geometry.Finsler.SeedKernelMeasurability
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Reconstruction.FinslerPopulationSeedPhysicalRecovery.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Reconstruction.FinslerPopulationSeedPhysicalRecovery`; the selected original proof blocks follow. -/
section

/-!
# Geometry.Finsler.Calibration.SeedPhysicalMap

* **Conditions:** An actual complete calibrated seed curve with its Borel label subtype.
* **Objects:** A globally measurable physical label–clock map agreeing with that same complete curve at every actual seed label.
* **Proof detail:** Extend the time-shifted actual seed map from the measurable subtype embedding and evaluate it on that image.

Mathematical sources:
- [D. H. Fremlin, Measure Theory, Volume 4, Appendix](https://www1.essex.ac.uk/maths/people/fremlin/chap4a.pdf#page=32): Sections 4A3B(a)–(c), p. 32; 4A3C(a)–(f), pp. 32–33.
- [D. H. Fremlin, Measure Theory, Volume 4](https://www1.essex.ac.uk/maths/people/fremlin/chap42.pdf#page=22): Theorem 423I(a)–(b), pp. 22–23; Proposition 424G, p. 31.

Source relation (adapter): The selected three commands define/read the actual physical map; statements identifying supplied conditional inverses are outside this extraction.
-/

/-!
# The original physical inverse is the actual complete seed curve

The stored common calibrated support span identifies the original inverse of the
label-clock map with the same complete seed curve under both original conditional
laws. This supplies the physical positions for the retained Haar-clock populations.
-/

open Set Function MeasureTheory ProbabilityTheory Manifold OTSelector.Geometry
open scoped Topology ContDiff ENNReal

noncomputable section
namespace OTSelector.Reconstruction

set_option backward.isDefEq.respectTransparency false

variable {E M Z : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}





variable [MeasurableSpace M] [BorelSpace M]

/-- The actual complete seed positions in the original potential clock, measurably
extended outside the actual seed labels by the fixed seed position at zero. -/
def populationSeedPhysicalMap (S : F.CalibratedLevelSeedPatch u) :
    S.covector.ker × ℝ → M :=
  extend (Prod.map ((↑) : S.labels → S.covector.ker) id)
    (fun q ↦ S.curve q.1 (q.2 - S.level)) (fun _ ↦ S.curve 0 0)

omit [FiniteDimensional ℝ E] [T2Space M] [PreconnectedSpace M] in
/-- The exact seed position map is globally measurable after its irrelevant
completion outside the actual seed labels. -/
theorem measurable_populationSeedPhysicalMap (S : F.CalibratedLevelSeedPatch u) :
    Measurable (populationSeedPhysicalMap S) := by
  have he : MeasurableEmbedding (Prod.map ((↑) : S.labels → S.covector.ker) (id : ℝ → ℝ)) :=
    (MeasurableEmbedding.subtype_coe S.labels_measurable).prodMap
    MeasurableEmbedding.id
  apply he.measurable_extend _ measurable_const
  have hc : Continuous (fun q : S.labels × ℝ ↦ S.curve q.1 (q.2 - S.level)) := by
    apply continuous_iff_continuousAt.mpr
    intro q
    exact (S.continuousAt_joint_curve
      (q := ((q.1 : S.covector.ker), q.2 - S.level))
      (S.labels_subset q.1.property)).comp
        (f := fun p : S.labels × ℝ ↦ ((p.1 : S.covector.ker), p.2 - S.level))
        (show ContinuousAt
          (fun p : S.labels × ℝ ↦ ((p.1 : S.covector.ker), p.2 - S.level)) q by fun_prop)
  exact hc.measurable

omit [FiniteDimensional ℝ E] [BorelSpace E] [T2Space M] [PreconnectedSpace M]
  [MeasurableSpace M] [BorelSpace M] in
/-- At actual labels the measurable physical map is the original complete curve
with the original potential level subtracted from its scalar clock. -/
theorem populationSeedPhysicalMap_at_label (S : F.CalibratedLevelSeedPatch u)
    (w : S.labels) (t : ℝ) :
    populationSeedPhysicalMap S (w, t) = S.curve w (t - S.level) := by
  have he : MeasurableEmbedding (Prod.map ((↑) : S.labels → S.covector.ker) (id : ℝ → ℝ)) :=
    (MeasurableEmbedding.subtype_coe S.labels_measurable).prodMap
    MeasurableEmbedding.id
  exact he.injective.extend_apply _ _ (w, t)








end OTSelector.Reconstruction

end
end
