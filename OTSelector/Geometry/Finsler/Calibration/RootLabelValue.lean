import Mathlib.MeasureTheory.Measure.SeparableMeasure
import Mathlib.MeasureTheory.Measure.Support
import Mathlib.MeasureTheory.VectorMeasure.Variation.SignedMeasure
import Mathlib.MeasureTheory.VectorMeasure.WithDensityVec
import Mathlib.Topology.ContinuousMap.SecondCountableSpace
import OTSelector.Geometry.Finsler.Basic
import OTSelector.Geometry.Finsler.CalibratedLevelSeedPatch
import OTSelector.Geometry.Finsler.CalibratedSeedWindow
import OTSelector.Geometry.Finsler.Calibration.SeedLabelReference
import OTSelector.Geometry.Finsler.Calibration.SeedRootPartition
import OTSelector.Geometry.Finsler.Energy.Basic
import OTSelector.Geometry.Finsler.LengthMetric
import OTSelector.Geometry.Finsler.PotentialGlobalFamily
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Reconstruction.FinslerCoefficientCoreLabel.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Reconstruction.FinslerCoefficientCoreLabel`; the selected original proof blocks follow. -/
section

/-!
# Geometry.Finsler.Calibration.RootLabelValue

* **Conditions:** The actual seed-to-population label embedding with the stated inherited calibration, measurability and regular-domain injectivity hypotheses.
* **Objects:** A globally defined zero-extended original inverse seed label and its exact values on genuine roots and selected pieces.
* **Proof detail:** Extend the inverse of the Borel seed label embedding by zero, then evaluate the extension on its actual image.

Mathematical sources:
- [D. H. Fremlin, Measure Theory, Volume 4](https://www1.essex.ac.uk/maths/people/fremlin/chap42.pdf#page=22): Theorem 423I(a)–(b), pp. 22–23; Proposition 424G, p. 31.
- [D. H. Fremlin, Measure Theory, Volume 4, Appendix](https://www1.essex.ac.uk/maths/people/fremlin/chap4a.pdf#page=32): Sections 4A3B(a)–(c), p. 32; 4A3C(a)–(f), pp. 32–33.

Source relation (adapter): Only the inverse-label definition and its three elementary readout/measurability statements are selected; compact coefficient-core refinements are outside scope.
-/

/-!
# Continuous original labels on coefficient cores

The measurable inverse of the original population root map admits compact
continuity refinements. These refinements retain the same seed, scalar window,
actual coefficient and conditional laws, and their actual labels form compact sets.
-/

open Set Function MeasureTheory ProbabilityTheory Manifold OTSelector.Geometry
open scoped Topology ContDiff ENNReal Matrix.Norms.Operator

noncomputable section
namespace OTSelector.Reconstruction

set_option backward.isDefEq.respectTransparency false

variable {E M Z : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}

/-- The actual label vector over the original seed image, extended by zero outside it. -/
def populationSeedRootLabelValue (S : F.CalibratedLevelSeedPatch u) (a : M → Z) :
    Z → S.covector.ker :=
  extend (fun w : S.labels ↦ a (S.curve w 0)) (fun w ↦ w.val) (fun _ ↦ 0)

variable [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  [MeasurableSpace Z] [MeasurableSpace.CountablySeparated Z]
  (S : F.CalibratedLevelSeedPatch u) (hF : F.IsSmoothStronglyConvex)
  (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
  (hu : let _instLabelCoreMetric : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
  {a : M → Z} (ha : Measurable a)
  (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))

include hF hcomplete hu ha hinj

/-- The extended actual inverse label is measurable without selecting a comparison family. -/
theorem measurable_populationSeedRootLabelValue : Measurable (populationSeedRootLabelValue S a) :=
  (measurableEmbedding_populationSeedLabel S hF hcomplete hu ha hinj).measurable_extend
    measurable_subtype_coe measurable_const

/-- Over an actual original root, the label vector is the original label exactly. -/
theorem populationSeedRootLabelValue_at_label (w : S.labels) :
    populationSeedRootLabelValue S a (a (S.curve w 0)) = w.val :=
  (measurableEmbedding_populationSeedLabel S hF hcomplete hu ha hinj).injective.extend_apply
    (fun w ↦ w.val) (fun _ ↦ 0) w

variable {P : ℕ → F.CalibratedSeedWindow u}
  {κ : ∀ j, Measure (P j).seed.covector.ker} {lambda : Measure Z}

/-- The measurable root inverse agrees with the label already retained on the selected piece. -/
theorem populationSeedRootLabelValue_on_piece (j : ℕ)
    (z : populationSeedRootPiece P a κ lambda j) :
    populationSeedRootLabelValue (P j).seed a z.val =
      (populationSeedPieceLabel P a κ lambda j z).val := by
  have h := populationSeedRootLabelValue_at_label (P j).seed hF hcomplete hu ha hinj
    (populationSeedPieceLabel P a κ lambda j z)
  rw [populationSeedPieceLabel_root P a κ lambda j z] at h
  exact h


end OTSelector.Reconstruction

end
end
