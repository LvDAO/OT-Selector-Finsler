import OTSelector.Reconstruction.FinslerOriginalEllipticSeedProducer

/-!
# The four geometric seed inputs and automatic measurability

`PaperSeedPatchBundle` retains the calibrated level-seed patch, openness of its
tube image, and atomlessness of the two population clock laws.
`paperGeometricSeedDatum_of_bundle` combines those four inputs with measurability
of the potential through the existing `paperGeometricSeedDatum_mk` constructor.

`paperGeometricSeedDatum_of_oneLipschitzBundle` derives that measurability from
`LipschitzWith 1 u` in the original Finsler length metric. The local metric instance
preserves the manifold topology and its Borel measurable space. No geometric or
population input is added or discharged by packaging it into the bundle.
-/

open Set Function Filter MeasureTheory
open OTSelector.Geometry OTSelector.Probability Manifold
open scoped Topology ContDiff ENNReal NNReal

noncomputable section

namespace OTSelector.Reconstruction

set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 400000

/-- **(1) A one-Lipschitz map between measurable metric spaces is measurable.** -/
theorem measurable_of_oneLipschitz {M N : Type*}
    [MetricSpace M] [MeasurableSpace M] [BorelSpace M]
    [MetricSpace N] [MeasurableSpace N] [BorelSpace N]
    {u : M → N} (hu : LipschitzWith 1 u) : Measurable u :=
  hu.continuous.measurable

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [IsManifold 𝓘(ℝ, E) ⊤ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]

/-- The four seed inputs remaining after measurability of the potential is derived. -/
structure PaperSeedPatchBundle (F : ContinuousFinslerNorm E M) (u : M → ℝ)
    (μ ν : ProbabilityMeasure M) where
  /-- The original calibrated level-seed patch. -/
  patch : F.CalibratedLevelSeedPatch u
  /-- Openness of the patch's tube image in the manifold topology. -/
  tube_open : IsOpen (seedTubeImage patch)
  /-- Atomlessness of the source population's potential law. -/
  muatom : NullSingletonClass ((μ : Measure M).map u)
  /-- Atomlessness of the target population's potential law. -/
  nuatom : NullSingletonClass ((ν : Measure M).map u)

/-- Assemble the existing seed datum from its four geometric inputs and measurability. -/
def paperGeometricSeedDatum_of_bundle {F : ContinuousFinslerNorm E M} {u : M → ℝ}
    {μ ν : ProbabilityMeasure M} (bundle : PaperSeedPatchBundle F u μ ν)
    (humeas : Measurable u) : PaperGeometricSeedDatum F u μ ν :=
  paperGeometricSeedDatum_mk bundle.patch bundle.tube_open humeas bundle.muatom bundle.nuatom

/-- A one-Lipschitz potential supplies measurability for the four-input seed bundle. -/
def paperGeometricSeedDatum_of_oneLipschitzBundle {F : ContinuousFinslerNorm E M}
    {u : M → ℝ} {μ ν : ProbabilityMeasure M}
    (hu : letI : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (bundle : PaperSeedPatchBundle F u μ ν) : PaperGeometricSeedDatum F u μ ν := by
  have humeas : Measurable u := by
    let : MetricSpace M := F.metricSpace
    exact measurable_of_oneLipschitz hu
  exact paperGeometricSeedDatum_of_bundle bundle humeas

end OTSelector.Reconstruction
