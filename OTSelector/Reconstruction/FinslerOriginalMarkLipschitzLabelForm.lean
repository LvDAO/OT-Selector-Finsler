import OTSelector.Reconstruction.FinslerOriginalSeedReadoutProducers
import OTSelector.Reconstruction.FinslerCoefficientCoreLabel

/-!
# Mark-Lipschitz constants in label form

The previous module `FinslerOriginalLabelReadoutChartLinear` showed that the concrete
label readout is a nonlinear extension of the inverse label map, so chart-linearity
is false.  The correct form is the LABEL form proved here:

(1) the label-section identity (from `populationSeedRootLabelValue_at_label`) composes
with the height-slice pairing form: for two label-section points the label-difference
readout is the seed-basis coordinate map applied to the difference of the label
vectors;
(2) the C1/mark-Lipschitz transfer is restated at the level of an abstract mark-to-label
map `lab : E → (n → ℝ)` with `ContDiff ℝ 1 lab` (this is the actual remaining
structural input: smoothness/linearity of the mark-to-label map on the compact mark
class).
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

/-- **(2) Mark-Lipschitz transfer at the level of the mark-to-label map.**  If the
mark-to-label map `lab : E → (n → ℝ)` is C1 on the (chart-parameterized) retained
roots and the actual kin/g are the frozen quadratic forms of it, then kin and g have
the mark-Lipschitz constants.  `ContDiff ℝ 1 lab` is the exact remaining structural
input (smoothness/linearity of the mark-to-label map on the compact mark class). -/
theorem hasMarkLipschitzConstantsOn_of_labelMap {K : Set E} (hK : IsCompact K)
    (hne : K.Nonempty) (hconv : Convex ℝ K) {n : Type*} [Fintype n]
    (lab : E → n → ℝ) (hlab : ContDiff ℝ 1 lab) (A B : Matrix n n ℝ) {kin g : E → ℝ}
    (hkin : ∀ e ∈ K, kin e = matrixQuadratic A (lab e))
    (hg : ∀ e ∈ K, g e = matrixQuadratic B (lab e)) :
    HasMarkLipschitzConstantsOn E K kin g :=
  hasMarkLipschitzConstantsOn_of_contDiff_readouts hK hne hconv hlab hkin hg

/-- **(1) Label-section identity composed with the height-slice form.**  For two
label-section marks the label-difference readout is the seed-basis coordinate readout
of the difference of the label vectors. -/
theorem labelReadout_sub_at_labels
    (S : F.CalibratedLevelSeedPatch u) (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _m : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    {a : M → Z} (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))
    (v w : S.labels) :
    (Module.finBasis ℝ S.covector.ker).equivFun
      (populationSeedRootLabelValue S a (a (S.curve v 0)) -
        populationSeedRootLabelValue S a (a (S.curve w 0))) =
    (Module.finBasis ℝ S.covector.ker).equivFun (v.val - w.val) := by
  rw [populationSeedRootLabelValue_at_label S hF hcomplete hu ha hinj v,
    populationSeedRootLabelValue_at_label S hF hcomplete hu ha hinj w, map_sub]

end OTSelector.Reconstruction
