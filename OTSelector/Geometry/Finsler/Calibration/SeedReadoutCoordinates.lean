import OTSelector.Analysis.Normed.BallCubeEmbedding
import OTSelector.Geometry.Finsler.Basic
import OTSelector.Geometry.Finsler.CalibratedLevelSeedPatch
import OTSelector.Geometry.Finsler.CalibratedSeedWindow
import OTSelector.Geometry.Finsler.Calibration.ReadoutAmplitude
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Reconstruction.FinslerOriginalNodePositionIdentification.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Reconstruction.FinslerOriginalNodePositionIdentification`; the selected original proof blocks follow. -/
section

/-!
# Geometry.Finsler.Calibration.SeedReadoutCoordinates

* **Conditions:** A C1,1 presentation of an actual calibrated seed; finite-dimensional basis coordinates and a positive cube radius for the quantitative inequalities.
* **Objects:** Exact initial-clock chart readout, explicit two-sided norm comparison for affine cube labels, and a window-readout amplitude bound.
* **Proof detail:** Use the presentation initial-value identity and inverse-chart cancellation; subtract affine cube coordinates, apply the operator norms of the basis equivalence and its inverse, then the actual window Lipschitz bound.

Mathematical sources:
- [Jiří Lebl, Basic Analysis II: Introduction to Real Analysis, Volume II](https://www.jirka.org/ra/realanal2.pdf): Sections 8.3–8.4, total derivative, chain rule and mean-value bounds; Section 8.6, higher derivatives.
- [Jiří Lebl, Basic Analysis II: Introduction to Real Analysis, Volume II (version 6.3, 15 May 2026)](https://www.jirka.org/ra/realanal2.pdf#page=38): Section 8.3, Theorem 8.3.7, p. 38; Exercise 8.3.7, p. 45 (differentiate the inverse identity).

Source relation (derived): Elementary initial-chart and finite-dimensional linear-coordinate identities. These statements do not identify a separate model ODE with actual flow at nonzero clock.
-/

/-!
# Node position, label coordinate and chart readout identity

This file closes gap (a') of FinslerOriginalNodePositionReadoutBridge.lean.

Two identifications are supplied with explicit constants.

1. Actual chart readout at the initial clock.  The C1,1 presentation of a seed
   patch has ambient_initial: the ambient curve at time zero is the inverse
   initial chart of its position.  Hence the actual chart readout of the window
   point at clock zero in the initial chart is exactly the label position:
   extChartAt initialChart (curve w 0) = position w.

2. Explicit comparability between the finBasis label coordinates and the
   inherited ambient norm on the label subspace.  The affine cube coordinates
   labelCubeCoordinates b R encode the basis coordinates of a label.  Both
   directions are bounded with explicit constants:
   ||w - z|| <= ||b.equivFunL.symm|| (2R) ||Q w - Q z|| and
   ||Q w - Q z|| <= (||b.equivFunL|| / (2R)) ||w - z||.

These convert a bound on the basis coordinate amplitude of a node position into
an ambient label amplitude with an explicit constant, and hence -- through the
window readout Lipschitz estimate of the previous file -- into a window readout
amplitude bound.

The remaining gap is the model-versus-actual comparison at nonzero clock: the
literal node position is a completePath value of the model ODE, while the actual
chart flow of the calibrated curve is not identified with it in the existing
modules.
-/
open Set Function Filter MeasureTheory Matrix Module Manifold Metric
open OTSelector.Geometry ContinuousFinslerNorm
open scoped ENNReal NNReal ContDiff Matrix.Norms.Operator Classical Topology BigOperators

noncomputable section
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace OTSelector.Reconstruction

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}

/-! ## The actual chart readout at the initial clock -/

/-- **Chart readout identity at clock zero.**  For a retained label of the seed
patch, the actual initial-chart readout of the calibrated curve at time zero is
exactly the label position of the C1,1 presentation.  This is the actual
chart-readout side of the identification: no model ODE is involved. -/
theorem curve_chart_readout_initial (S : CalibratedLevelSeedPatch F u)
    (P : C11LevelSeedPresentation F u S.covector S.level S.openLabels S.labels S.curve)
    {w : S.covector.ker} (hw : w ∈ S.labels) :
    extChartAt 𝓘(ℝ, E) P.initialChart (S.curve w 0) = P.position w := by
  have hwV : w ∈ S.openLabels := S.labels_subset hw
  have hposdom : P.position w ∈ P.domain := P.position_domain hwV
  have htarget : P.position w ∈ (extChartAt 𝓘(ℝ, E) P.initialChart).target :=
    P.domain_target hposdom
  have hcurve : S.curve w 0 = P.ambient (P.position w) 0 :=
    congrFun (congrFun P.curve_eq w) 0
  rw [hcurve, P.ambient_initial (P.position w) hposdom]
  exact (extChartAt 𝓘(ℝ, E) P.initialChart).right_inv htarget

/-- **Window chart readout at clock zero.**  The same identity in the calibrated
seed window form: the initial-chart readout of the window point at clock zero is
the label position. -/
theorem calibratedWindow_chart_readout_initial (P : CalibratedSeedWindow F u)
    (Pres : C11LevelSeedPresentation F u P.seed.covector P.seed.level
      P.seed.openLabels P.seed.labels P.seed.curve)
    {w : P.seed.covector.ker} (hw : w ∈ P.seed.labels) :
    extChartAt 𝓘(ℝ, E) Pres.initialChart (P.seed.curve w 0) = Pres.position w :=
  curve_chart_readout_initial P.seed Pres hw

/-! ## Explicit finBasis coordinate comparability -/

/-- **Coordinate amplitude to ambient label amplitude.**  The reverse direction
of the cube coordinate comparison: the cube coordinate difference is bounded by
the ambient label difference with the explicit constant
||b.equivFunL|| / (2R). -/
theorem norm_labelCubeCoordinates_sub_le {W : Type*} [NormedAddCommGroup W]
    [NormedSpace ℝ W] {ι : Type*} [Fintype ι] (b : Basis ι ℝ W) {R : ℝ}
    (hR : 0 < R) (w z : W) :
    ‖labelCubeCoordinates b R w - labelCubeCoordinates b R z‖ ≤
      (‖b.equivFunL.toContinuousLinearMap‖ / (2 * R)) * ‖w - z‖ := by
  have hsub := labelCubeCoordinates_sub b hR w z
  have hnorm : ‖b.equivFun (w - z)‖ =
      (2 * R) * ‖labelCubeCoordinates b R w - labelCubeCoordinates b R z‖ := by
    have h := congrArg norm hsub
    rw [norm_smul, Real.norm_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * R)] at h
    exact h.symm
  have hop : ‖b.equivFun (w - z)‖ ≤
      ‖b.equivFunL.toContinuousLinearMap‖ * ‖w - z‖ :=
    b.equivFunL.toContinuousLinearMap.le_opNorm (w - z)
  have hle : (2 * R) * ‖labelCubeCoordinates b R w - labelCubeCoordinates b R z‖ ≤
      ‖b.equivFunL.toContinuousLinearMap‖ * ‖w - z‖ := by
    rw [hnorm] at hop
    exact hop
  rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity : (0 : ℝ) < 2 * R)]
  linarith

/-- **Two-sided finBasis coordinate comparability.**  The explicit constants
between the finBasis cube coordinate norm and the inherited ambient norm on the
label subspace, in both directions. -/
theorem norm_labelCubeCoordinates_comparability {W : Type*} [NormedAddCommGroup W]
    [NormedSpace ℝ W] {ι : Type*} [Fintype ι] (b : Basis ι ℝ W) (R : ℝ)
    (hR : 0 < R) (w z : W) :
    ‖w - z‖ ≤ (‖b.equivFunL.symm.toContinuousLinearMap‖ * (2 * R)) *
        ‖labelCubeCoordinates b R w - labelCubeCoordinates b R z‖ ∧
      ‖labelCubeCoordinates b R w - labelCubeCoordinates b R z‖ ≤
        (‖b.equivFunL.toContinuousLinearMap‖ / (2 * R)) * ‖w - z‖ :=
  ⟨norm_sub_le_labelCubeCoordinates b hR w z,
    norm_labelCubeCoordinates_sub_le b hR w z⟩

/-! ## The node-position coordinate slot and the window readout -/

/-- **Window readout amplitude from cube coordinate amplitude.**  A bound on the
finBasis cube coordinate amplitude of two retained window labels converts through
the explicit comparability constant into an ambient label amplitude, and hence
into a window readout amplitude bound with the seed local Lipschitz constant. -/
theorem readout_amplitude_le_of_labelCubeAmplitude (P : CalibratedSeedWindow F u)
    {z zc : ℝ × P.seed.covector.ker} {R Rc : ℝ} (hR : 0 < R)
    (hz : z ∈ ball P.center (P.seed.radius P.center))
    (hzc : zc ∈ ball P.center (P.seed.radius P.center))
    (hcube : ‖labelCubeCoordinates (Module.finBasis ℝ P.seed.covector.ker) R z.2 -
      labelCubeCoordinates (Module.finBasis ℝ P.seed.covector.ker) R zc.2‖ ≤ Rc) :
    ‖P.readout z - P.readout zc‖ ≤
      (P.seed.constant P.center : ℝ) *
        max |z.1 - zc.1|
          ((‖(Module.finBasis ℝ P.seed.covector.ker).equivFunL.symm.toContinuousLinearMap‖ *
            (2 * R)) * Rc) := by
  have h1 := readout_amplitude_le_coordinate P hz hzc
  have hlab : ‖z.2 - zc.2‖ ≤
      (‖(Module.finBasis ℝ P.seed.covector.ker).equivFunL.symm.toContinuousLinearMap‖ *
        (2 * R)) * Rc :=
    (norm_sub_le_labelCubeCoordinates (Module.finBasis ℝ P.seed.covector.ker) hR
      z.2 zc.2).trans (mul_le_mul_of_nonneg_left hcube (by positivity))
  exact h1.trans (mul_le_mul_of_nonneg_left (max_le_max le_rfl hlab)
    (NNReal.coe_nonneg _))

end OTSelector.Reconstruction

end
end
