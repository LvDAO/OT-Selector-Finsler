import OTSelector.Reconstruction.FinslerOriginalPopulationCalibratedTube
import OTSelector.Reconstruction.FinslerOriginalTilePalmSampleLaw
import OTSelector.Reconstruction.FinslerPopulationCommonSupport

/-!
# The paper-side hypotheses of the general Finsler selector, in minimal honest form

The selector theorem is conditional on exactly one geometric hypothesis plus the
paper's analytic Palm/rate data.  This module packages those hypotheses once, as
|FinslerPaperGeometricHypotheses|, and assembles their consequences from the
modules that already prove them.

## The hypotheses

1. **The calibrated tube (the single geometric hypothesis).**  The local
   calibrated ray tube of main.tex:1063-1078 is assumed open-nonempty in the
   consumer form |(interior (chartInterior F u)).Nonempty|; the smooth tube form
   |CalibratedTube| and the population-lane seed form
   (|interior_nonempty_of_seed_tube_open|) are both supplied as constructors.
   main.tex:1076-1078 states verbatim that this is a local geometric hypothesis,
   not a consequence of arbitrary marginals.

2. **The a.e. Borel ray-cluster data** (main.tex:1173-1185): for each population
   marginal, an |AeRayClusterData|, i.e. a Borel ray domain, a full-measure
   subset carrying complete unit-speed calibrated Euler--Lagrange curves and the
   clock, with no open set asserted.

3. **Pointwise clock atomlessness** (the no-tie/Palm rate condition): for a.e.
   base point the law of the clock difference |u . - u x| has no atoms
   (|PointwiseClockAtomless|).  The population lane's compact atomless clock law
   |CompactAtomlessClockSupport| implies it.

4. **The Palm sample law** (|PaperPalmSampleLaw|), in the exact shape of the
   tile-lane |TilePalmSampleLaw| fields: the sample mean of the masked frozen
   cost is the population Palm readout, and the normalized readout converges to
   the population value.  Every concrete |TilePalmSampleLaw| instance yields it
   (|paperPalmSampleLaw_of_tilePalmSampleLaw|).

## The consequences (all assembled, none reproved)

From (1): the exact open chart datum (|nonempty_chartData|), the a.e. window
producer whose full-measure set is open in every window
(|exists_openGood_windowChartDataAe|), and the calibrated level-seed patches
(|exists_levelSeedPatches|).

From (2): the calibrated interior is a.e. full on each ray domain and every good
ray-cluster point is calibrated interior (|chartInterior_ae_full_source|,
|chartInterior_ae_full_target|, |good_subset_chartInterior_source|,
|good_subset_chartInterior_target|).

From (4): the Palm readout identification (|palmReadout_tendsto|), the readout
content of the pressure lane.

The capstone |windowSide_endgame| packages, from one structure, the window side
of the selector: the open-domain window data, the level-seed patches and the Palm
readout identification.  No |sorry|, |admit| or added axiom occurs.
-/
open Set Function Metric Manifold OTSelector.Geometry MeasureTheory Filter
open scoped Topology ContDiff ENNReal NNReal BoundedContinuousFunction

noncomputable section
namespace OTSelector.Reconstruction

set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

/-! ## 1. The Palm sample law (the |TilePalmSampleLaw| fields) -/

/-- **The paper's Palm sample law** for the retained tile lane, carrying exactly
the fields of the tile-lane |TilePalmSampleLaw|:

* |maskedMean| — the sample mean of the masked frozen cost (a lane quantity);
* |normalization| — the tile normalization (a lane quantity);
* |populationValue| — the population tile value (a lane quantity);
* |palmReadout| — the population Palm readout of the masked frozen cost (paper
  data: the definition of the readout);
* |maskedMean_eq| — the sample law of the lane is the scene Palm law, so the
  sample mean of the masked frozen cost is the population readout;
* |readout_tendsto| — the sample-level Campbell bridge with the tile
  normalization: the normalized readout converges to the population value. -/
structure PaperPalmSampleLaw where
  /-- The sample mean of the masked frozen cost (lane data). -/
  maskedMean : ℕ → ℝ
  /-- The tile normalization (lane data). -/
  normalization : ℕ → ℝ
  /-- The population tile value (lane data). -/
  populationValue : ℕ → ℝ
  /-- The population Palm readout of the masked frozen cost (paper data). -/
  palmReadout : ℕ → ℝ
  /-- The sample mean of the masked frozen cost is the population Palm readout. -/
  maskedMean_eq : ∀ n, maskedMean n = palmReadout n
  /-- The normalized Palm readout converges to the population tile value. -/
  readout_tendsto :
    Tendsto (fun n => normalization n * palmReadout n - populationValue n) atTop (𝓝 0)

/-- The Palm readout identification carried by the paper's Palm sample law. -/
theorem PaperPalmSampleLaw.readout_identification (h : PaperPalmSampleLaw) :
    Tendsto (fun n => h.normalization n * h.maskedMean n - h.populationValue n)
      atTop (𝓝 0) := by
  have heq : (fun n => h.normalization n * h.maskedMean n - h.populationValue n) =
      (fun n => h.normalization n * h.palmReadout n - h.populationValue n) := by
    funext n
    rw [h.maskedMean_eq n]
  rw [heq]
  exact h.readout_tendsto

/-! ## 2. The concrete tile-lane Palm structure implies the paper Palm law -/

section PaperPalmTileBridge

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  [MeasurableSpace.CountablySeparated (ℚ → M)]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {P : ℕ → F.CalibratedSeedWindow u} {a : M → (ℚ → M)}
  {κ : ∀ j, Measure (P j).seed.covector.ker} {lambda : Measure (ℚ → M)}
  [IsFiniteMeasure lambda]
  {η₀ η₁ : Measure M} [IsFiniteMeasure η₀] [IsFiniteMeasure η₁]
  {ρ₀ ρ₁ : M → ℝ} {v : ℕ → E → ℝ} {b : (ℚ → M) × ℝ → M}
  {Good : (ℚ → M) → Prop} {r : ℝ} {δ loss : ℝ≥0∞}
  {D : PopulationLocalPressureCore P a κ lambda η₀ η₁ ρ₀ ρ₁ v b Good r δ loss}
  {ε : ℝ} (T : D.TaylorTiles ε)
  {K : Set M} {q : ℝ}
  {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]

/-- **Every concrete tile-lane |TilePalmSampleLaw| instance yields the paper Palm
sample law** for the corresponding masked mean, normalization and population
value.  This is the bridge that justifies the abstract interface of
|PaperPalmSampleLaw|: it is not a new hypothesis but exactly the fields already
identified in the tile lane. -/
def paperPalmSampleLaw_of_tilePalmSampleLaw
    (f : (K × K) →ᵇ ℝ) (t : ℝ) (sample : ∀ n, Measure (Ω n))
    (X Y : ∀ n, Fin (n + 1) → Ω n → M) (scale : ℕ → ℝ) (c : T.Index)
    (popVal : ℕ → ℝ)
    (h : T.TilePalmSampleLaw f t sample X Y scale c popVal) :
    PaperPalmSampleLaw where
  maskedMean := fun n => T.tileMaskedFrozenCostMean sample X Y n c
  normalization := fun n => (1 - 2 * ε) * scale n
  populationValue := popVal
  palmReadout := h.palmCostMean
  maskedMean_eq := fun n => h.maskedMean_eq n
  readout_tendsto := by
    simpa only [mul_assoc] using h.palm_readout

end PaperPalmTileBridge

/-! ## 3. Pointwise clock atomlessness -/

universe uE uM uZ

variable {E : Type uE} {M : Type uM} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}

/-- **Pointwise clock atomlessness** (the paper's no-tie/Palm rate condition):
for almost every base point the law of the clock difference |u . - u x| under the
population marginal has no atoms. -/
def PointwiseClockAtomless (ν : Measure M) (u : M → ℝ) : Prop :=
  ∀ᵐ x ∂ν, NullSingletonClass ((ν).map (fun y => u y - u x))

/-- An atomless scalar clock law gives pointwise clock atomlessness. -/
theorem pointwiseClockAtomless_of_atomless_clock {ν : Measure M}
    (hmeas : Measurable u) (h : NullSingletonClass (ν.map u)) :
    PointwiseClockAtomless ν u := by
  refine Filter.Eventually.of_forall fun x => ⟨fun t => ?_⟩
  have hsub : Measurable fun y : M => u y - u x := hmeas.sub measurable_const
  have hset : (fun y : M => u y - u x) ⁻¹' ({t} : Set ℝ) =
      u ⁻¹' ({t + u x} : Set ℝ) := by
    ext y
    simp only [mem_preimage, mem_singleton_iff]
    constructor <;> intro h <;> linarith
  rw [Measure.map_apply hsub (measurableSet_singleton t), hset,
    ← Measure.map_apply hmeas (measurableSet_singleton (t + u x))]
  exact h.measure_singleton (t + u x)

/-- **The population lane's compact atomless clock law is pointwise atomless.** -/
theorem pointwiseClockAtomless_of_compactAtomlessClock {ν : Measure M}
    {offset lo hi : ℝ} (hmeas : Measurable u)
    (h : CompactAtomlessClockSupport ((ν).map u) offset lo hi) :
    PointwiseClockAtomless ν u :=
  pointwiseClockAtomless_of_atomless_clock hmeas h.atomless

/-! ## 4. The single geometric hypothesis in its supplied forms -/

/-- The paper's calibrated tube (the smooth tube form of main.tex:1063-1078)
supplies the endgame input. -/
theorem interiorNonempty_of_calibratedTube {Z : Type uZ} (T : CalibratedTube F u Z)
    (hu : letI : MetricSpace M := F.metricSpace; LipschitzWith 1 u) :
    (interior (chartInterior F u)).Nonempty :=
  T.interior_nonempty hu

/-- The population-lane seed with an open tube image supplies the endgame input. -/
theorem interiorNonempty_of_seed_tube_open (A : F.CalibratedLevelSeedPatch u)
    (hF : F.IsSmoothStronglyConvex)
    (hu : letI : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (himg : IsOpen (seedTubeImage A)) :
    (interior (chartInterior F u)).Nonempty :=
  interior_nonempty_of_seed_tube_open A hF hu himg

/-- The population-lane window seed with an open tube image supplies the endgame
input. -/
theorem interiorNonempty_of_window_tube_open (P : F.CalibratedSeedWindow u)
    (hF : F.IsSmoothStronglyConvex)
    (hu : letI : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (himg : IsOpen (windowSeedTubeImage P)) :
    (interior (chartInterior F u)).Nonempty :=
  interior_nonempty_of_window_tube_open P hF hu himg

/-- The weakest explicit form of the geometric hypothesis: a nonempty open piece
of one population seed's tube image. -/
theorem interiorNonempty_of_seed_open_piece (A : F.CalibratedLevelSeedPatch u)
    (hF : F.IsSmoothStronglyConvex)
    (hu : letI : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    {O : Set M} (hO : IsOpen O) (hOne : O.Nonempty) (hOsub : O ⊆ seedTubeImage A) :
    (interior (chartInterior F u)).Nonempty :=
  interior_nonempty_of_seed_open_piece A hF hu hO hOne hOsub

/-! ## 5. The paper-side hypothesis structure -/

/-- **The paper-side hypotheses of the general Finsler selector**, in minimal
honest form: the single geometric hypothesis (1), the a.e. Borel ray-cluster data
(2), the pointwise clock atomlessness (3), and the Palm sample law (4).  No
hypothesis is silently weakened or strengthened; see the module documentation. -/
structure FinslerPaperGeometricHypotheses
    (F : ContinuousFinslerNorm E M) (u : M → ℝ)
    (μ ν : ProbabilityMeasure M) where
  /-- (1) The paper's calibrated tube hypothesis, in the consumer form of
  |FinslerOriginalAeOpenChartData|: the calibrated interior has nonempty manifold
  interior.  This is the single geometric hypothesis of the selector. -/
  interior_nonempty : (interior (chartInterior F u)).Nonempty
  /-- (2) The a.e. Borel ray-cluster data for the source marginal. -/
  source_rayCluster : AeRayClusterData F u (μ : Measure M)
  /-- (2) The a.e. Borel ray-cluster data for the target marginal. -/
  target_rayCluster : AeRayClusterData F u (ν : Measure M)
  /-- (3) Pointwise clock atomlessness for the source marginal. -/
  source_clock_atomless : PointwiseClockAtomless (μ : Measure M) u
  /-- (3) Pointwise clock atomlessness for the target marginal. -/
  target_clock_atomless : PointwiseClockAtomless (ν : Measure M) u
  /-- (4) The paper's Palm sample law of the retained tile lane. -/
  palm_sample_law : PaperPalmSampleLaw

namespace FinslerPaperGeometricHypotheses

variable {F : ContinuousFinslerNorm E M} {u : M → ℝ} {μ ν : ProbabilityMeasure M}

/-- The paper hypotheses supply the nonempty exact chart datum. -/
theorem nonempty_chartData (H : FinslerPaperGeometricHypotheses F u μ ν)
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : letI : MetricSpace M := F.metricSpace; LipschitzWith 1 u) :
    Nonempty (CoreSectionChartData F u) :=
  nonempty_chartData_of_interior_nonempty hF hcomplete hu H.interior_nonempty

/-- The paper hypotheses supply the a.e. window producer with open full-measure
sets: the open-domain |WindowChartDataAe|. -/
theorem exists_openGood_windowChartDataAe (H : FinslerPaperGeometricHypotheses F u μ ν)
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : letI : MetricSpace M := F.metricSpace; LipschitzWith 1 u) (μchart : Measure E) :
    ∃ (P : ℕ → F.CalibratedSeedWindow u)
      (κ : ∀ j, Measure (P j).seed.covector.ker)
      (W : WindowChartDataAe (F := F) (u := u) κ μchart),
      (∀ j, IsOpen ((W.chartData j).good)) ∧
        (∀ j, (W.chartData j).σ 0 ∈ (W.chartData j).good) :=
  exists_openGood_windowChartDataAe_of_interior_nonempty hF hcomplete hu
    H.interior_nonempty μchart

/-- The paper hypotheses supply a calibrated level-seed patch for every window:
the input of the pointwise reconstruction consumers. -/
theorem exists_levelSeedPatches (H : FinslerPaperGeometricHypotheses F u μ ν)
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : letI : MetricSpace M := F.metricSpace; LipschitzWith 1 u) :
    ∃ (P : ℕ → F.CalibratedSeedWindow u) (W : WindowChartData P),
      ∀ j, ∃ (A : F.CalibratedLevelSeedPatch u)
          (e : A.covector.ker ≃L[ℝ] (W.chartData j).p.ker),
        A.openLabels = e ⁻¹' (W.chartData j).V ∧
          A.labels = e ⁻¹' ((W.chartData j).V ∩
            (W.chartData j).σ ⁻¹' (W.parentCore j)) ∧
            (∀ w t, A.curve w t =
              (W.chartData j).Γ ((W.chartData j).σ (e w)) t) ∧
              A.level = (W.chartData j).q :=
  exists_levelSeedPatches_of_interior_nonempty hF hcomplete hu H.interior_nonempty

/-- (2) The calibrated interior is a.e. full on the source ray domain. -/
theorem chartInterior_ae_full_source (H : FinslerPaperGeometricHypotheses F u μ ν) :
    (μ : Measure M) (H.source_rayCluster.domain \ chartInterior F u) = 0 :=
  H.source_rayCluster.chartInterior_ae_full

/-- (2) The calibrated interior is a.e. full on the target ray domain. -/
theorem chartInterior_ae_full_target (H : FinslerPaperGeometricHypotheses F u μ ν) :
    (ν : Measure M) (H.target_rayCluster.domain \ chartInterior F u) = 0 :=
  H.target_rayCluster.chartInterior_ae_full

/-- (2) Every good source ray-cluster point is a calibrated interior point. -/
theorem good_subset_chartInterior_source (H : FinslerPaperGeometricHypotheses F u μ ν) :
    H.source_rayCluster.good ⊆ chartInterior F u :=
  H.source_rayCluster.good_subset_chartInterior

/-- (2) Every good target ray-cluster point is a calibrated interior point. -/
theorem good_subset_chartInterior_target (H : FinslerPaperGeometricHypotheses F u μ ν) :
    H.target_rayCluster.good ⊆ chartInterior F u :=
  H.target_rayCluster.good_subset_chartInterior

/-- (4) The Palm readout identification: the normalized sample mean of the masked
frozen cost converges to the population tile value. -/
theorem palmReadout_tendsto (H : FinslerPaperGeometricHypotheses F u μ ν) :
    Tendsto (fun n => H.palm_sample_law.normalization n * H.palm_sample_law.maskedMean n
      - H.palm_sample_law.populationValue n) atTop (𝓝 0) :=
  H.palm_sample_law.readout_identification

/-- **The window side of the selector from the paper hypotheses.**  One structure
yields the open-domain window data, the calibrated level-seed patches, and the
Palm readout identification simultaneously. -/
theorem windowSide_endgame (H : FinslerPaperGeometricHypotheses F u μ ν)
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : letI : MetricSpace M := F.metricSpace; LipschitzWith 1 u) (μchart : Measure E) :
    (∃ (P : ℕ → F.CalibratedSeedWindow u)
      (κ : ∀ j, Measure (P j).seed.covector.ker)
      (W : WindowChartDataAe (F := F) (u := u) κ μchart),
      (∀ j, IsOpen ((W.chartData j).good)) ∧
        (∀ j, (W.chartData j).σ 0 ∈ (W.chartData j).good)) ∧
    (∃ (P : ℕ → F.CalibratedSeedWindow u) (W : WindowChartData P),
      ∀ j, ∃ (A : F.CalibratedLevelSeedPatch u)
          (e : A.covector.ker ≃L[ℝ] (W.chartData j).p.ker),
        A.openLabels = e ⁻¹' (W.chartData j).V ∧
          A.labels = e ⁻¹' ((W.chartData j).V ∩
            (W.chartData j).σ ⁻¹' (W.parentCore j)) ∧
            (∀ w t, A.curve w t =
              (W.chartData j).Γ ((W.chartData j).σ (e w)) t) ∧
              A.level = (W.chartData j).q) ∧
    Tendsto (fun n => H.palm_sample_law.normalization n * H.palm_sample_law.maskedMean n
      - H.palm_sample_law.populationValue n) atTop (𝓝 0) :=
  ⟨exists_openGood_windowChartDataAe H hF hcomplete hu μchart,
    exists_levelSeedPatches H hF hcomplete hu,
    palmReadout_tendsto H⟩

/-! ## 6. Constructors: the geometric hypothesis in its supplied forms -/

/-- **The smooth calibrated tube form** of main.tex:1063-1078 yields the paper
hypotheses. -/
def ofCalibratedTube {Z : Type uZ} (T : CalibratedTube F u Z)
    (hu : letI : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (source_rayCluster : AeRayClusterData F u (μ : Measure M))
    (target_rayCluster : AeRayClusterData F u (ν : Measure M))
    (source_clock_atomless : PointwiseClockAtomless (μ : Measure M) u)
    (target_clock_atomless : PointwiseClockAtomless (ν : Measure M) u)
    (palm_sample_law : PaperPalmSampleLaw) :
    FinslerPaperGeometricHypotheses F u μ ν where
  interior_nonempty := T.interior_nonempty hu
  source_rayCluster := source_rayCluster
  target_rayCluster := target_rayCluster
  source_clock_atomless := source_clock_atomless
  target_clock_atomless := target_clock_atomless
  palm_sample_law := palm_sample_law

/-- **The population-lane seed-tube form** yields the paper hypotheses. -/
def ofSeedTubeOpen (A : F.CalibratedLevelSeedPatch u)
    (hF : F.IsSmoothStronglyConvex)
    (hu : letI : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (himg : IsOpen (seedTubeImage A))
    (source_rayCluster : AeRayClusterData F u (μ : Measure M))
    (target_rayCluster : AeRayClusterData F u (ν : Measure M))
    (source_clock_atomless : PointwiseClockAtomless (μ : Measure M) u)
    (target_clock_atomless : PointwiseClockAtomless (ν : Measure M) u)
    (palm_sample_law : PaperPalmSampleLaw) :
    FinslerPaperGeometricHypotheses F u μ ν where
  interior_nonempty := interiorNonempty_of_seed_tube_open A hF hu himg
  source_rayCluster := source_rayCluster
  target_rayCluster := target_rayCluster
  source_clock_atomless := source_clock_atomless
  target_clock_atomless := target_clock_atomless
  palm_sample_law := palm_sample_law

/-- **The population-lane window-tube form** yields the paper hypotheses. -/
def ofWindowTubeOpen (P : F.CalibratedSeedWindow u)
    (hF : F.IsSmoothStronglyConvex)
    (hu : letI : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (himg : IsOpen (windowSeedTubeImage P))
    (source_rayCluster : AeRayClusterData F u (μ : Measure M))
    (target_rayCluster : AeRayClusterData F u (ν : Measure M))
    (source_clock_atomless : PointwiseClockAtomless (μ : Measure M) u)
    (target_clock_atomless : PointwiseClockAtomless (ν : Measure M) u)
    (palm_sample_law : PaperPalmSampleLaw) :
    FinslerPaperGeometricHypotheses F u μ ν where
  interior_nonempty := interiorNonempty_of_window_tube_open P hF hu himg
  source_rayCluster := source_rayCluster
  target_rayCluster := target_rayCluster
  source_clock_atomless := source_clock_atomless
  target_clock_atomless := target_clock_atomless
  palm_sample_law := palm_sample_law

end FinslerPaperGeometricHypotheses

end OTSelector.Reconstruction
