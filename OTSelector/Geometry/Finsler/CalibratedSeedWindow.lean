import OTSelector.Geometry.Finsler.Basic
import OTSelector.Geometry.Finsler.CalibratedCompleteCylinder
import OTSelector.Geometry.Finsler.CalibratedLevelSeedPatch
import OTSelector.Geometry.Finsler.Energy.Basic
import OTSelector.Geometry.Finsler.LengthMetric
import OTSelector.Geometry.Manifold.ManifoldTubeJacobian
import OTSelector.MeasureTheory.AreaFormula.ParameterizedLipschitzJacobian
import OTSelector.Transport.Kantorovich.CalibratedReach
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Geometry.CalibratedSeedWindow.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Geometry.CalibratedSeedWindow`; the selected original proof blocks follow. -/
section

/-!
# Geometry.Finsler.CalibratedSeedWindow

* **Conditions:** A constructed level seed, rational calibration endpoints and one of its legal local chart balls; original strong convexity/completeness are used where injectivity is required.
* **Objects:** A Borel product window, actual manifold/readout maps, injectivity, measurable embedding and exact normalized chart area formula.
* **Proof detail:** Intersect actual endpoint calibration with the seed ball, use the original clock and curve uniqueness for injectivity, then apply the relative-domain Lipschitz area formula.

Mathematical sources:
- [Rotem Assouline, Curvature-Dimension for Autonomous Lagrangians, arXiv:2409.08001v6 (10 February 2026)](https://arxiv.org/pdf/2409.08001v6#page=38): Section 4.3, Proposition 4.18(i)–(iv), pp. 38–39, especially change of variables (4.13); Lemma 4.23 and proof, pp. 46–47.
- [D. H. Fremlin, Measure Theory, Volume 2](https://www1.essex.ac.uk/maths/people/fremlin/chap26.pdf#page=26): Theorem 263D(i)–(v), pp. 26–28; Lemma 263C, p. 25; decomposition Lemma 262M, pp. 15–17.
- [D. H. Fremlin, Measure Theory, Volume 4](https://www1.essex.ac.uk/maths/people/fremlin/chap42.pdf#page=22): Theorem 423I(a)–(b), pp. 22–23; Proposition 424G, p. 31.

Source relation (derived): The window and normalization are explicit local implementations; the Jacobian formula retains the actual original map and can include zero-measure labels.
-/

/-!
# Measurable original calibrated windows

Each window uses a constructed level seed, rational calibration endpoints, and one
of its actual local chart balls. Its measured domain remains a product of a time
interval and a Borel label set. The original curve map is injective there, and its
actual normalized derivative gives exact chart-volume change of variables.
-/

open Set Metric Manifold MeasureTheory
open scoped Topology ContDiff NNReal ENNReal

noncomputable section
namespace OTSelector.Geometry.ContinuousFinslerNorm

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

/-- A rational calibrated interval and one of the seed's local coordinate balls. -/
structure CalibratedSeedWindow (F : ContinuousFinslerNorm E M) (u : M → ℝ) where
  seed : CalibratedLevelSeedPatch F u
  left : ℚ
  right : ℚ
  left_neg : left < 0
  right_pos : 0 < right
  center : ℝ × seed.covector.ker
  center_mem : center ∈ seed.centers

namespace CalibratedSeedWindow

variable {F : ContinuousFinslerNorm E M} {u : M → ℝ}

/-- Retained original seeds whose curves calibrate both rational endpoint times. -/
def labels (P : CalibratedSeedWindow F u) : Set P.seed.covector.ker :=
  P.seed.labels ∩ {w | u (P.seed.curve w P.left) = (P.seed.level : ℝ) + P.left ∧
    u (P.seed.curve w P.right) = (P.seed.level : ℝ) + P.right}

/-- The actual map from time and original seed label to the manifold. -/
def toManifold (P : CalibratedSeedWindow F u) (z : ℝ × P.seed.covector.ker) : M :=
  P.seed.curve z.2 z.1

/-- The measurable calibrated portion of the selected local parameter ball. -/
def domain (P : CalibratedSeedWindow F u) : Set (ℝ × P.seed.covector.ker) :=
  ball P.center (P.seed.radius P.center) ∩ (Ioo (P.left : ℝ) P.right ×ˢ P.labels)

/-- The same actual map read in the chart selected at the center. -/
def readout (P : CalibratedSeedWindow F u) : (ℝ × P.seed.covector.ker) → E :=
  extChartAt 𝓘(ℝ, E) (P.toManifold P.center) ∘ P.toManifold

omit [FiniteDimensional ℝ E] [BorelSpace E] in
/-- Product-norm localization preserves the time and label product domain exactly. -/
theorem domain_eq_prod (P : CalibratedSeedWindow F u) :
    P.domain = (Ioo (P.left : ℝ) P.right ∩ ball P.center.1 (P.seed.radius P.center)) ×ˢ
      (P.labels ∩ ball P.center.2 (P.seed.radius P.center)) := by
  rw [domain, ← ball_prod_same P.center.1 P.center.2]
  ext z
  simp only [mem_inter_iff, mem_prod]
  tauto

omit [FiniteDimensional ℝ E] [BorelSpace E] in
/-- The actual readout is Lipschitz on the open coordinate ball. -/
theorem lipschitzOn_readout (P : CalibratedSeedWindow F u) :
    LipschitzOnWith (P.seed.constant P.center) P.readout
      (ball P.center (P.seed.radius P.center)) :=
  (P.seed.local_data P.center P.center_mem).2.2.2.mono ball_subset_closedBall

omit [FiniteDimensional ℝ E] [BorelSpace E] in
/-- The entire coordinate ball stays in the selected chart. -/
theorem mapsTo_chart (P : CalibratedSeedWindow F u) :
    MapsTo P.toManifold (ball P.center (P.seed.radius P.center))
      (extChartAt 𝓘(ℝ, E) (P.toManifold P.center)).source :=
  (P.seed.local_data P.center P.center_mem).2.2.1.mono_left ball_subset_closedBall

omit [FiniteDimensional ℝ E] [BorelSpace E] in
/-- The chart inverse recovers continuity of the actual manifold-valued map. -/
theorem continuousOn_toManifold (P : CalibratedSeedWindow F u) :
    ContinuousOn P.toManifold (ball P.center (P.seed.radius P.center)) := by
  let χ := extChartAt 𝓘(ℝ, E) (P.toManifold P.center)
  have hcomp := (continuousOn_extChartAt_symm (P.toManifold P.center)).comp P.lipschitzOn_readout.continuousOn
    (fun z hz ↦ χ.map_source (P.mapsTo_chart hz))
  apply hcomp.congr
  intro z hz
  exact (χ.left_inv (P.mapsTo_chart hz)).symm

variable [T2Space M] [PreconnectedSpace M]

/-- Calibration screens are Borel because endpoint readouts are continuous on the
original measurable seed set. No regularity of extensions outside that set is used. -/
theorem measurableSet_labels (P : CalibratedSeedWindow F u)
    (hu : let _instWindowLabelsLip : MetricSpace M := F.metricSpace
      LipschitzWith 1 u) : MeasurableSet P.labels := by
  let _instWindowLabelsMetric : MetricSpace M := F.metricSpace
  have hc (t : ℝ) : Continuous (fun w : P.seed.labels ↦ u (P.seed.curve w t)) :=
    continuousOn_iff_continuous_domRestrict.mp
      ((hu.continuous.comp_continuousOn (P.seed.continuous_at_time t)).mono P.seed.labels_subset)
  have hclosed : IsClosed {w : P.seed.labels |
      u (P.seed.curve w P.left) = (P.seed.level : ℝ) + P.left ∧
      u (P.seed.curve w P.right) = (P.seed.level : ℝ) + P.right} :=
    (isClosed_eq (hc P.left) continuous_const).inter
      (isClosed_eq (hc P.right) continuous_const)
  have heq : P.labels = ((↑) : P.seed.labels → P.seed.covector.ker) ''
      {w : P.seed.labels | u (P.seed.curve w P.left) = (P.seed.level : ℝ) + P.left ∧
        u (P.seed.curve w P.right) = (P.seed.level : ℝ) + P.right} := by
    ext w
    simp only [labels, mem_inter_iff, mem_ofPred_eq, mem_image, Subtype.exists]
    aesop
  rw [heq]
  exact (MeasurableEmbedding.subtype_coe P.seed.labels_measurable).measurableSet_image.mpr
    hclosed.measurableSet

/-- Every local calibrated window has a Borel parameter domain. -/
theorem measurableSet_domain (P : CalibratedSeedWindow F u)
    (hu : let _instWindowDomainLip : MetricSpace M := F.metricSpace
      LipschitzWith 1 u) : MeasurableSet P.domain :=
  isOpen_ball.measurableSet.inter (isOpen_Ioo.measurableSet.prod (P.measurableSet_labels hu))

omit [BorelSpace E] in
/-- Endpoint calibration and complete-curve uniqueness separate both time and label. -/
theorem injOn_toManifold (P : CalibratedSeedWindow F u) (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _instWindowInjLip : MetricSpace M := F.metricSpace
      LipschitzWith 1 u) : InjOn P.toManifold P.domain := by
  have hi := hF.injOn_timeLabel_of_complete_unit_calibrated_endpoints hcomplete hu
    (S := P.labels) (a := (P.left : ℝ)) (b := (P.right : ℝ)) (q := (P.seed.level : ℝ))
    (fun w hw ↦ P.seed.complete w hw.1) (fun w hw ↦ P.seed.unit w hw.1)
    (fun w hw ↦ hw.2) (P.seed.initial_injective.mono (inter_subset_left (s := P.seed.labels)))
  exact hi.mono inter_subset_right

omit [BorelSpace E] in
/-- Every point in a calibrated window belongs to the original two-sided interior. -/
theorem mapsTo_calibratedInterior (P : CalibratedSeedWindow F u)
    (hF : F.IsSmoothStronglyConvex)
    (hu : let _instWindowInteriorLip : MetricSpace M := F.metricSpace
      LipschitzWith 1 u) :
    let _instWindowInteriorMetric : MetricSpace M := F.metricSpace
    MapsTo P.toManifold P.domain (OTSelector.Geometry.calibratedInterior u) := by
  let _instWindowInteriorMetric : MetricSpace M := F.metricSpace
  dsimp only
  intro z hz
  exact (hF.calibrated_window_of_complete_unit_endpoints hu
    (P.seed.complete z.2 hz.2.2.1) (P.seed.unit z.2 hz.2.2.1)
    hz.2.2.2.1 hz.2.2.2.2).2.2 z.1 hz.2.1

omit [BorelSpace E] in
/-- Injectivity of the actual readout on the measured window. -/
theorem injOn_readout (P : CalibratedSeedWindow F u) (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _instWindowReadoutLip : MetricSpace M := F.metricSpace
      LipschitzWith 1 u) : InjOn P.readout P.domain := by
  intro z hz q hq heq
  apply P.injOn_toManifold hF hcomplete hu hz hq
  exact (extChartAt 𝓘(ℝ, E) (P.toManifold P.center)).injOn
    (P.mapsTo_chart hz.1) (P.mapsTo_chart hq.1) heq

/-- Exact chart-volume transfer on every measurable subpiece, with the actual
parameter derivative and its retained Haar normalization. -/
theorem lintegral_image_readout (P : CalibratedSeedWindow F u) (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _instWindowVolumeLip : MetricSpace M := F.metricSpace
      LipschitzWith 1 u) (m : Measure E) [m.IsAddHaarMeasure]
    {s : Set (ℝ × P.seed.covector.ker)} (hs : MeasurableSet s) (hsD : s ⊆ P.domain)
    (g : E → ℝ≥0∞) :
    (∫⁻ y in P.readout '' s, g y ∂m) =
      ∫⁻ z in s, ENNReal.ofReal (parameterizedJacobian P.readout P.seed.normalization z) *
        g (P.readout z) ∂(tubeParameterMeasure P.seed.normalization m) :=
  lintegral_image_parameterizedJacobian m P.seed.normalization isOpen_ball
    P.lipschitzOn_readout ((P.injOn_readout hF hcomplete hu).mono hsD) hs
    (hsD.trans inter_subset_left) g

/-- The image of the actual window is Borel in the original manifold. -/
theorem measurableSet_image [MeasurableSpace M] [BorelSpace M]
    (P : CalibratedSeedWindow F u) (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _instWindowImageLip : MetricSpace M := F.metricSpace
      LipschitzWith 1 u) : MeasurableSet (P.toManifold '' P.domain) :=
  (P.measurableSet_domain hu).image_of_continuousOn_injOn
    (P.continuousOn_toManifold.mono inter_subset_left) (P.injOn_toManifold hF hcomplete hu)

/-- The actual curve map restricted to its measured window is a measurable embedding. -/
theorem measurableEmbedding_toManifold [MeasurableSpace M] [BorelSpace M]
    (P : CalibratedSeedWindow F u) (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _instWindowEmbeddingLip : MetricSpace M := F.metricSpace
      LipschitzWith 1 u) :
    MeasurableEmbedding (fun z : P.domain ↦ P.toManifold z) :=
  (P.continuousOn_toManifold.mono inter_subset_left).measurableEmbedding
    (P.measurableSet_domain hu) (P.injOn_toManifold hF hcomplete hu)

end CalibratedSeedWindow
end OTSelector.Geometry.ContinuousFinslerNorm

end
end
