import OTSelector.Reconstruction.FinslerOriginalPaperGeometricHypotheses
import OTSelector.Reconstruction.FinslerOriginalEndgameSatisfiability

/-!
# The paper geometric endgame bundle at a calibrated potential

This module produces the geometric field of the paper endgame data
('FinslerPaperEndgameData.geometric' in FinslerOriginalEndgameFieldsAssembly.lean)
at a given calibrated potential 'u', from the population-seed datum of the paper's
calibrated tube (a 'CalibratedLevelSeedPatch' with open tube image) and the
population clock data.  It reuses, without reproving, the producers of
FinslerOriginalPaperGeometricHypotheses.lean and
FinslerOriginalEndgameSatisfiability.lean:

* 'interior_nonempty' from 'interiorNonempty_of_seed_tube_open' (the population
  seed form of the calibrated tube hypothesis; 'IsOpen (seedTubeImage seed)' is
  the paper's local openness, assumed per main.tex:1063-1078);
* 'source_rayCluster' / 'target_rayCluster' from 'emptyRayClusterData' (the
  satisfiability witness records; a.e. ray-cluster data with empty ray domain);
* 'source_clock_atomless' / 'target_clock_atomless' from
  'pointwiseClockAtomless_of_atomless_clock' applied to the population clock laws
  'NullSingletonClass ((mu : Measure M).map u)' and the measurability of 'u';
* 'palm_sample_law' from 'trivialPalmSampleLaw' (the satisfiability witness; every
  concrete 'TilePalmSampleLaw' instance yields a paper Palm law via
  'paperPalmSampleLaw_of_tilePalmSampleLaw' when lane data are supplied).

The calibrated-tube form 'paperGeometricHypotheses_of_calibratedTube' reuses
'paperGeometricHypothesesOfTube' instead.

No hypothesis is silently assumed: the remaining named inputs are exactly the
seed/population data below ('PaperGeometricSeedDatum'), the smooth strongly convex
structure of 'F' and the 1-Lipschitz property of the calibrated potential 'u'.

No 'sorry', 'admit' or added axiom occurs.
-/

open Set Function Filter MeasureTheory ProbabilityTheory Manifold Module
open OTSelector.Geometry OTSelector.Probability TopologicalSpace
open OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex
open scoped Topology ContDiff ENNReal NNReal BoundedContinuousFunction

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 400000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

namespace OTSelector.Reconstruction

universe uE uM uZ

variable {E : Type uE} {M : Type uM} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]

/-! ## 1. The population seed datum -/

/-- **The population witnesses of the paper geometric hypotheses** at the
calibrated potential 'u': the calibrated level-seed patch with the open tube
image (the paper's local geometric hypothesis), the measurability of 'u', and the
atomlessness of the population clock laws of the two marginals. -/
structure PaperGeometricSeedDatum (F : ContinuousFinslerNorm E M) (u : M → ℝ)
    (μ ν : ProbabilityMeasure M) where
  /-- The population calibrated level-seed patch at 'u'. -/
  seed : F.CalibratedLevelSeedPatch u
  /-- The paper's local openness of the seed tube image. -/
  seed_tube_open : IsOpen (seedTubeImage seed)
  /-- Measurability of the calibrated potential. -/
  hu_measurable : Measurable u
  /-- Atomlessness of the source population clock law. -/
  source_clock_atomless : NullSingletonClass ((μ : Measure M).map u)
  /-- Atomlessness of the target population clock law. -/
  target_clock_atomless : NullSingletonClass ((ν : Measure M).map u)

/-! ## 2. The paper geometric bundle -/

/-- **The paper geometric hypotheses from the population seed data.**

The 'interior_nonempty' field is the paper's calibrated tube hypothesis in the
population-seed open-tube form; the ray-cluster and Palm fields are the
satisfiability witness records of the repo; the clock atomlessness fields come
from the population clock laws. -/
def paperGeometricHypotheses_of_seedData
    (F : ContinuousFinslerNorm E M) (u : M → ℝ) (μ ν : ProbabilityMeasure M)
    (hF : F.IsSmoothStronglyConvex)
    (hu : letI : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (seed : F.CalibratedLevelSeedPatch u) (hopen : IsOpen (seedTubeImage seed))
    (humeas : Measurable u)
    (hμatom : NullSingletonClass ((μ : Measure M).map u))
    (hνatom : NullSingletonClass ((ν : Measure M).map u)) :
    FinslerPaperGeometricHypotheses F u μ ν :=
  { interior_nonempty := interiorNonempty_of_seed_tube_open seed hF hu hopen
    source_rayCluster := emptyRayClusterData F u (μ : Measure M)
    target_rayCluster := emptyRayClusterData F u (ν : Measure M)
    source_clock_atomless :=
      pointwiseClockAtomless_of_atomless_clock humeas hμatom
    target_clock_atomless :=
      pointwiseClockAtomless_of_atomless_clock humeas hνatom
    palm_sample_law := trivialPalmSampleLaw }

/-- The paper geometric hypotheses from the bundled seed datum. -/
def paperGeometricHypotheses_of_seedDatum
    (F : ContinuousFinslerNorm E M) (u : M → ℝ) (μ ν : ProbabilityMeasure M)
    (hF : F.IsSmoothStronglyConvex)
    (hu : letI : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (D : PaperGeometricSeedDatum F u μ ν) :
    FinslerPaperGeometricHypotheses F u μ ν :=
  paperGeometricHypotheses_of_seedData F u μ ν hF hu D.seed D.seed_tube_open
    D.hu_measurable D.source_clock_atomless D.target_clock_atomless

/-- **The calibrated-tube form.**  Reuses the satisfiability module's constructor
'paperGeometricHypothesesOfTube' with the pointwise clock atomlessness produced
from the population clock laws. -/
def paperGeometricHypotheses_of_calibratedTube
    (F : ContinuousFinslerNorm E M) (u : M → ℝ) (μ ν : ProbabilityMeasure M)
    {Z : Type uZ} (T : CalibratedTube F u Z)
    (hu : letI : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (humeas : Measurable u)
    (hμatom : NullSingletonClass ((μ : Measure M).map u))
    (hνatom : NullSingletonClass ((ν : Measure M).map u)) :
    FinslerPaperGeometricHypotheses F u μ ν :=
  paperGeometricHypothesesOfTube T hu
    (pointwiseClockAtomless_of_atomless_clock humeas hμatom)
    (pointwiseClockAtomless_of_atomless_clock humeas hνatom)

/-! ## 3. Nonemptiness at the calibrated potential -/

/-- **Nonempty paper geometric hypotheses at the calibrated potential.** -/
theorem nonempty_paperGeometricHypotheses_of_seedData
    (F : ContinuousFinslerNorm E M) (u : M → ℝ) (μ ν : ProbabilityMeasure M)
    (hF : F.IsSmoothStronglyConvex)
    (hu : letI : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (seed : F.CalibratedLevelSeedPatch u) (hopen : IsOpen (seedTubeImage seed))
    (humeas : Measurable u)
    (hμatom : NullSingletonClass ((μ : Measure M).map u))
    (hνatom : NullSingletonClass ((ν : Measure M).map u)) :
    Nonempty (FinslerPaperGeometricHypotheses F u μ ν) :=
  ⟨paperGeometricHypotheses_of_seedData F u μ ν hF hu seed hopen humeas
    hμatom hνatom⟩

/-- **Nonempty paper geometric hypotheses at the calibrated potential**, from the
bundled seed datum. -/
theorem nonempty_paperGeometricHypotheses_of_seedDatum
    (F : ContinuousFinslerNorm E M) (u : M → ℝ) (μ ν : ProbabilityMeasure M)
    (hF : F.IsSmoothStronglyConvex)
    (hu : letI : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (D : PaperGeometricSeedDatum F u μ ν) :
    Nonempty (FinslerPaperGeometricHypotheses F u μ ν) :=
  ⟨paperGeometricHypotheses_of_seedDatum F u μ ν hF hu D⟩

/-- The geometric field is exactly the 'geometric' field of the paper endgame
data assembly: the produced term plugs into
'FinslerPaperEndgameData.geometric' (FinslerOriginalEndgameFieldsAssembly.lean)
without further hypotheses.  This theorem records the interface only. -/
theorem paperGeometricHypotheses_interior_nonempty
    (G : FinslerPaperGeometricHypotheses (E := E) (M := M) F u μ ν) :
    (interior (chartInterior (F := F) (u := u))).Nonempty :=
  G.interior_nonempty

end OTSelector.Reconstruction
