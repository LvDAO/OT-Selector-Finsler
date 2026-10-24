import OTSelector.Reconstruction.FinslerOriginalSeedChartIdentification
import OTSelector.Reconstruction.FinslerCoefficientCoreLabel

/-!
# Label readout on the label section: the actually-true linearity

Inspecting `populationSeedRootLabelValue` (`FinslerCoefficientCoreLabel`, line 25) shows
it is DEFINED by `extend (fun w : S.labels => a (S.curve w 0)) (fun w => w.val)
(fun _ => 0)`.  So the concrete label readout is NOT a linear coordinate map of an
arbitrary chart parameter `Φ`: it is a nonlinear extension of the inverse label map.
`LabelReadoutChartLinear C Φ` is therefore false for a general `Φ`.

The actually-true linearity is on the LABEL section: for the parameter
`Φ w := a (S.curve w 0)` (the label section map), the label readout is exactly the
seed-basis coordinate readout of the label vector `w.val`.  The theorem below proves
that identity; it is the structural fact the lane uses at retained roots
(`populationSeedRootLabelValue_on_piece` gives the retained piece label).

Residual inputs are listed in the report: the lane's pointwise identifications, and
the (true) linearity statement on the label section, which is proved here.
-/

open Set Function Matrix MeasureTheory Module Manifold OTSelector.Geometry
open scoped Topology ContDiff ENNReal Matrix.Norms.Operator NNReal

noncomputable section
namespace OTSelector.Reconstruction

variable {E M Z : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  [MeasurableSpace M] [TopologicalSpace Z] [MeasurableSpace Z]
  [T2Space M] [PreconnectedSpace M] [BorelSpace M] [MeasurableSpace.CountablySeparated Z]

/-- **Label readout on the label section is the seed-basis coordinate readout of the
label.**  For the label-section parameter `Φ w = a (S.curve w 0)`, the concrete
readout of the population seed root label value is exactly the label vector `w.val`
in seed basis coordinates. -/
theorem labelReadout_populationSeedRootLabelValue_at_label
    (S : F.CalibratedLevelSeedPatch u) (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _m : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    {a : M → Z} (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))
    (w : S.labels) :
    (Module.finBasis ℝ S.covector.ker).equivFun
      (populationSeedRootLabelValue S a (a (S.curve w 0))) =
    (Module.finBasis ℝ S.covector.ker).equivFun w.val := by
  rw [populationSeedRootLabelValue_at_label S hF hcomplete hu ha hinj w]

end OTSelector.Reconstruction