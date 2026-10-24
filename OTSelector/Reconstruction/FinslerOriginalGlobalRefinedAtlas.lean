import OTSelector.Reconstruction.FinslerOriginalRefinedSeedWindow
import OTSelector.Reconstruction.FinslerOriginalCubeCoverageConditionalMarks
import Mathlib.MeasureTheory.Measure.OpenPos

/-!
# Pointwise density bridge and the global refined atlas

This file closes the two gaps of `FinslerOriginalRefinedSeedWindow.lean`.

## The pointwise density bridge

The ambient Haar reference intensity of a selected piece is, by the library
identity `ae_populationSeedPieceRootDensity_inv`, the reciprocal of the original
seed reference Radon--Nikodym factor. Radon--Nikodym derivatives are only defined
almost everywhere, so a *pointwise* statement is meaningful exactly when the
intensity admits a **continuous representative** -- the continuous
Jacobian-weighted density readout supplied by the population-density lane. This
file proves the upgrade mechanism: on an open label set, an a.e. identity between
the canonical intensity readout and a continuous representative upgrades to
pointwise equality (Mathlib `eqOn_open_of_ae_eq`), and consequently positivity
and finiteness of the continuous readout at a retained label give the
pointwise positive-finite intensity, hence (via the a.e. Radon--Nikodym bridge)
the reference-root condition.

## The global refined atlas

Every window of the countable atlas is replaced by its certified ball-core
version: the per-window refined seed patch (with the certified chart ball as
C1,1 presentation core, a label ball, and a linear unit cube inside the labels)
is chosen simultaneously over the countable index, giving one global refined
family whose windows all carry a metric label ball and a linear unit cube. The
cube coverage of each refined window's retained reference piece then follows from
the existing coverage assembly. Window-image containment in the calibrated
interior is the geometry-lane theorem
`CalibratedSeedWindow.mapsTo_calibratedInterior`, which applies to every window
of the refined family; the cover-equality of the refined family with the original
atlas remains the documented sub-gap (a refined window is strictly smaller than
its parent, so preservation of the full manifold cover needs a refinement-cover
lemma).
-/
open Set Function MeasureTheory ProbabilityTheory Manifold OTSelector.Geometry
open MeasureTheory.Measure
open Metric
open scoped Topology ContDiff ENNReal NNReal BigOperators

noncomputable section
namespace OTSelector.Reconstruction

set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

variable {E M Z : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  [MeasurableSpace Z] [MeasurableSpace.CountablySeparated Z]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}

/-! ## (i) The pointwise density bridge

The upgrade mechanism: an a.e. identity on an open set between two continuous
functions is a pointwise identity. -/

/-- **A.e.-to-pointwise upgrade of the density identity.**  On an open label set,
an a.e. identity between two continuous functions is a pointwise identity. This
is the mechanism which turns the a.e. Radon--Nikodym intensity identity into the
pointwise identity with the continuous Jacobian representative. -/
theorem eqOn_of_ae_eq_of_continuousOn
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    [MeasurableSpace V] [BorelSpace V]
    (μ : Measure V) [MeasureTheory.Measure.IsOpenPosMeasure μ]
    {f g : V → ℝ≥0∞} {s : Set V} (hs : IsOpen s)
    (hf : ContinuousOn f s) (hg : ContinuousOn g s)
    (h : f =ᵐ[μ.restrict s] g) : EqOn f g s :=
  MeasureTheory.Measure.eqOn_open_of_ae_eq h hs hf hg

/-- **Pointwise density bridge at a retained label.**  If the ambient Haar
reference intensity of a selected piece coincides a.e. on an open set of retained
labels with a continuous Jacobian representative, and both are continuous there,
then the intensity equals the representative at every retained label of that open
set; in particular positivity and finiteness of the representative give the
pointwise positive-finite intensity of the piece at the root. -/
theorem pointwise_populationSeedPieceHaarDensity_eq_readout
    (P : ℕ → F.CalibratedSeedWindow u) (a : M → Z)
    (κ : ∀ j, Measure (P j).seed.covector.ker) (lambda : Measure Z) (j : ℕ)
    (μ : Measure (P j).seed.covector.ker) [MeasureTheory.Measure.IsOpenPosMeasure μ]
    {readout : (P j).seed.covector.ker → ℝ≥0∞} {s : Set (P j).seed.covector.ker}
    (hs : IsOpen s)
    (hint_cont : ContinuousOn (populationSeedPieceHaarDensity P a κ lambda j) s)
    (hread_cont : ContinuousOn readout s)
    (hae : populationSeedPieceHaarDensity P a κ lambda j =ᵐ[μ.restrict s] readout) :
    EqOn (populationSeedPieceHaarDensity P a κ lambda j) readout s :=
  eqOn_of_ae_eq_of_continuousOn μ hs hint_cont hread_cont hae

/-- **Pointwise positive-finite intensity at a retained root.**  Under the
pointwise density identity, a strictly positive and finite continuous readout on
the retained labels makes the original root density positive and finite at every
retained label. -/
theorem pointwise_rootDensity_pos_of_readout
    (P : ℕ → F.CalibratedSeedWindow u) (a : M → Z)
    (κ : ∀ j, Measure (P j).seed.covector.ker) (lambda : Measure Z) (j : ℕ)
    {readout : (P j).seed.covector.ker → ℝ≥0∞} {s : Set (P j).seed.covector.ker}
    (hpoint : ∀ w ∈ s, populationSeedPieceHaarDensity P a κ lambda j w = readout w)
    (hpos : ∀ w ∈ s, 0 < readout w) (hfin : ∀ w ∈ s, readout w < (∞ : ℝ≥0∞))
    {w : (P j).seed.covector.ker} (hw : w ∈ s) (hwlab : w ∈ (P j).seed.labels) :
    0 < populationSeedPieceRootDensity P a κ lambda j (a ((P j).seed.curve w 0)) ∧
      populationSeedPieceRootDensity P a κ lambda j (a ((P j).seed.curve w 0)) <
        (∞ : ℝ≥0∞) := by
  have hlab := populationSeedPieceHaarDensity_at_label P a κ lambda j ⟨w, hwlab⟩
  rw [hpoint w hw] at hlab
  rw [← hlab]
  exact ⟨hpos w hw, hfin w hw⟩

/-! ## (ii) The global refined atlas -/

/-- **A certified ball-core refinement of a calibrated window.**  The refined
window carries a positive metric ball of seed labels around the zero label and a
linear unit cube inside its seed labels: exactly the coverage inputs obtained from
the certified compact chart ball. -/
structure RefinedBallCoreWindow (F : ContinuousFinslerNorm E M) (u : M → ℝ) where
  window : F.CalibratedSeedWindow u
  labelBall : ∃ r : ℝ, 0 < r ∧
    Metric.ball (0 : window.seed.covector.ker) r ⊆ window.seed.labels
  cubeCover : ∃ e : window.seed.covector.ker ≃L[ℝ]
      (Fin (Module.finrank ℝ window.seed.covector.ker) → ℝ),
    OTSelector.Probability.seedUnitCube
        (Module.finrank ℝ window.seed.covector.ker) ⊆ e '' window.seed.labels

/-- **The global refined atlas.**  Given per-window certified ball-core
refinements of a countable atlas, the refinements can be selected simultaneously:
there is one global refined family whose every window carries a positive metric
label ball and a linear unit cube inside its seed labels. -/
theorem exists_global_refinedBallCore_atlas
    (hrefine : ∀ _ : ℕ, ∃ W : RefinedBallCoreWindow F u, True) :
    ∃ P' : ℕ → F.CalibratedSeedWindow u,
      (∀ j, ∃ r : ℝ, 0 < r ∧
        Metric.ball (0 : (P' j).seed.covector.ker) r ⊆ (P' j).seed.labels) ∧
      (∀ j, ∃ e : (P' j).seed.covector.ker ≃L[ℝ]
          (Fin (Module.finrank ℝ (P' j).seed.covector.ker) → ℝ),
        OTSelector.Probability.seedUnitCube
            (Module.finrank ℝ (P' j).seed.covector.ker) ⊆ e '' (P' j).seed.labels) := by
  choose W _ using hrefine
  exact ⟨fun j => (W j).window, fun j => (W j).labelBall, fun j => (W j).cubeCover⟩

/-- **Cube coverage of every refined window's retained piece.**  For the globally
refined family, once every retained seed label carries the finite-nonzero
reference intensity and the first-owner exclusion, each window's retained
reference piece is covered by its linear unit cube -- the coverage input consumed
by the upper pressure lane, uniformly in the window index. -/
theorem global_refinedBallCore_cubeCoverage
    (P' : ℕ → F.CalibratedSeedWindow u) (a : M → Z)
    (κ : ∀ j, Measure (P' j).seed.covector.ker) (lambda : Measure Z)
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _instGlobalRefinedCoverageMetric : MetricSpace M := F.metricSpace
      LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))
    (hlabelCover : ∀ j, ∃ e : (P' j).seed.covector.ker ≃L[ℝ]
        (Fin (Module.finrank ℝ (P' j).seed.covector.ker) → ℝ),
      OTSelector.Probability.seedUnitCube
          (Module.finrank ℝ (P' j).seed.covector.ker) ⊆ e '' (P' j).seed.labels)
    (hroot : ∀ j, ∀ w ∈ (P' j).seed.labels,
      a ((P' j).seed.curve w 0) ∈
        populationSeedReferenceRoots (P' j).seed a (κ j) lambda)
    (hfirst : ∀ j, ∀ w ∈ (P' j).seed.labels, ∀ i < j,
      a ((P' j).seed.curve w 0) ∉
        populationSeedReferenceRoots (P' i).seed a (κ i) lambda) :
    ∀ j, ∃ e : (P' j).seed.covector.ker ≃L[ℝ]
        (Fin (Module.finrank ℝ (P' j).seed.covector.ker) → ℝ),
      OTSelector.Probability.seedUnitCube
          (Module.finrank ℝ (P' j).seed.covector.ker) ⊆
        e '' (populationSeedRootLabelValue (P' j).seed a ''
          populationSeedRootPiece P' a κ lambda j) := by
  intro j
  obtain ⟨e, he⟩ := hlabelCover j
  refine ⟨e, cubeCoverage_of_seedLabelCover_and_retention P' a κ lambda
    hF hcomplete hu ha hinj j e he ?_⟩
  intro w hw _
  exact retention_of_root_and_firstOwner P' a κ lambda j hF hcomplete hu ha hinj
    (hroot j) (hfirst j) hw

/-! ## The exact remaining sub-gaps

(i) The pointwise density bridge is proved for the *continuous representative* of
the intensity: the a.e. Radon--Nikodym identity upgrades to a pointwise identity
whenever the canonical intensity readout is continuous on the open retained label
set. Since Radon--Nikodym derivatives are defined only a.e., this is the strongest
pointwise statement available; identifying the concrete continuous readout with
the Jacobian-weighted population density is exactly the `populationWindowDensity`
formula of the density lane (already available as
`populationWindowDensity_apply_clock`), and is supplied as the continuity and
a.e.-identity hypotheses.

(ii) The global refined atlas is constructed by simultaneous selection of the
per-window certified ball-core refinements, and the cube coverage of every
refined window's retained piece is derived. What is *not* formalized is (a) the
cover-equality of the refined family with the original atlas -- a refined window
is strictly smaller than its parent window, so preserving the full manifold cover
needs an additional refinement-cover lemma (a partition of each parent window by
refined ball-core windows) -- and (b) the restatement of window-image containment
for the whole refined family (the per-window theorem
`CalibratedSeedWindow.mapsTo_calibratedInterior` in the geometry lane supplies
it; only the family-level packaging is omitted). These are the remaining
atlas-cover sub-gaps.
-/

end OTSelector.Reconstruction
