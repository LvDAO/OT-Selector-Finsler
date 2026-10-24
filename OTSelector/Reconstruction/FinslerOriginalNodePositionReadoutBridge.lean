import OTSelector.Geometry.Finsler.Calibration.ReadoutAmplitude
import OTSelector.Reconstruction.FinslerOriginalReadoutLipschitzFromAtlas
import OTSelector.Reconstruction.FinslerOriginalNormalizedMomentumEligibleNodes

/-!
# Geometry.Finsler.Calibration.ReadoutAmplitude

* **Conditions:** Two parameter points lie in the same actual calibrated window ball.
* **Objects:** The original window readout distance bounded by its local Lipschitz constant times the maximum clock/label displacement.
* **Proof detail:** Apply the seed-provided local readout Lipschitz bound and the product max-norm distance identity.

Mathematical sources:
- [Jiří Lebl, Basic Analysis II: Introduction to Real Analysis, Volume II](https://www.jirka.org/ra/realanal2.pdf): Sections 8.3–8.4, total derivative, chain rule and mean-value bounds; Section 8.6, higher derivatives.

Source relation (derived): A generic metric readout estimate. No momentum-node normalization or model-versus-actual claim is part of the selected command.
-/

/-!
# Node-position to window-readout amplitude bridge

This file closes the remaining gaps (a) and (b) of
FinslerOriginalReadoutLipschitzFromAtlas.lean.

Gap (a): the node-position to readout estimate.  The normalized node position is
the matrix normalization of the literal original node position in the label
chart: normalizedMomentumNodePosition = T * v originalMomentumNodePosition.
Hence a bound on the normalized node-position amplitude (the pressure-lane
amplitude event) demultiplies with the inverse-frame constant to the literal
label-chart amplitude of the node position.  On the window side the readout is
Lipschitz on the coordinate ball (seed local data), so the readout amplitude is
bounded by the explicit constant times the maximum of the clock and label
coordinate amplitudes.

Gap (b): the single reference point and the half-radius shrink.  The retained
window points are compared with the single window centre; if the constant times
the coordinate amplitude is strictly below half the constructed chart radius,
then the two readout-deviation hypotheses of the atlas ball containment hold and
the retained pair lies in one manifold ball of explicit radius K * Drad.

Contents:

1. norm_le_of_normalized_amplitude: inverse-frame demultiplication.
2. originalMomentumNodePosition_norm_le_of_normalized: the concrete node-position
   amplitude bridge.
3. readout_amplitude_le_coordinate: window readout amplitude bounded by the
   coordinate amplitude through the seed local Lipschitz constant.
4. readout_deviation_le_of_coordinate_deviation: the same estimate relative to
   the single window centre.
5. calibratedWindow_ballContainment_of_coordinateAmplitude: the half-radius
   shrink of the atlas ball containment, with the reference point and the
   readout amplitude passed through explicitly.
6. calibratedWindow_ballContainment_of_labelBall: the same with the amplitude
   instantiated at the coordinate amplitude bound.
-/
open Set Function Filter MeasureTheory Matrix Module Manifold Metric
open OTSelector.Geometry ContinuousFinslerNorm OTSelector.Probability
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

/-! ## Gap (a): normalized node amplitude to literal label-chart amplitude -/

/-- **Inverse-frame demultiplication.**  If the inverse frame has distortion
constant C, a bound on the normalized amplitude ||T * v p|| <= R gives the literal
amplitude bound ||p|| <= C * R. -/
theorem norm_le_of_normalized_amplitude {q : ℕ}
    {T : Matrix (Fin q) (Fin q) ℝ} [Invertible T]
    {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ v, ‖T⁻¹ *ᵥ v‖ ≤ C * ‖v‖)
    {p : Fin q → ℝ} {R : ℝ} (hamp : ‖T *ᵥ p‖ ≤ R) :
    ‖p‖ ≤ C * R := by
  have hp : p = T⁻¹ *ᵥ (T *ᵥ p) := by
    rw [Matrix.mulVec_mulVec, Matrix.inv_mul_of_invertible, Matrix.one_mulVec]
  rw [hp]
  exact (hC _).trans (mul_le_mul_of_nonneg_left hamp hC0)

/-- **Literal node-position amplitude.**  A bound on the normalized node-position
amplitude demultiplies to the literal label-chart amplitude of the original node
position.  The normalized node position is by definition T applied to the literal
node position, so this is exactly the amplitude-event to chart-amplitude bridge. -/
theorem originalMomentumNodePosition_norm_le_of_normalized
    (S : CalibratedLevelSeedPatch F u) (w : S.covector.ker)
    (T : Matrix (Fin (finrank ℝ S.covector.ker))
      (Fin (finrank ℝ S.covector.ker)) ℝ) [Invertible T]
    {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ v, ‖T⁻¹ *ᵥ v‖ ≤ C * ‖v‖)
    {c : ℝ} {e : LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker)} {R : ℝ}
    (hamp : ‖normalizedMomentumNodePosition S w T c e‖ ≤ R) :
    ‖originalMomentumNodePosition S w c e‖ ≤ C * R := by
  simpa only [normalizedMomentumNodePosition] using
    norm_le_of_normalized_amplitude (T := T) hC0 hC hamp

/-! ## Gap (a): window readout amplitude from coordinate amplitudes -/



/-- **Window readout deviation from the single centre.**  The retained window
point's readout deviation from the window centre is bounded by the seed local
constant times the maximum of its clock and label coordinate deviations from the
centre.  This is the estimate needed to thread the single reference point. -/
theorem readout_deviation_le_of_coordinate_deviation (P : CalibratedSeedWindow F u)
    {z : ℝ × P.seed.covector.ker} {Rt Rw : ℝ}
    (hz : z ∈ ball P.center (P.seed.radius P.center))
    (ht : |z.1 - P.center.1| ≤ Rt) (hw : ‖z.2 - P.center.2‖ ≤ Rw) :
    ‖P.readout z - P.readout P.center‖ ≤
      (P.seed.constant P.center : ℝ) * max Rt Rw := by
  have hcball : P.center ∈ ball P.center (P.seed.radius P.center) :=
    mem_ball_self (P.seed.local_data P.center P.center_mem).1
  have h := readout_amplitude_le_coordinate P hz hcball
  have hle : max |z.1 - P.center.1| ‖z.2 - P.center.2‖ ≤ max Rt Rw :=
    max_le_max ht hw
  exact h.trans (mul_le_mul_of_nonneg_left hle (NNReal.coe_nonneg _))

/-! ## Gap (b): the half-radius shrink through the retained window data -/

/-- **Half-radius shrink of the atlas ball containment.**  With the single window
centre as reference point, if the local constant times the retained coordinate
amplitude is strictly less than half the constructed chart radius, then the two
readout-deviation hypotheses of the atlas ball containment hold, and any retained
pair whose readout amplitude is at most Drad lies in one manifold ball of explicit
radius K * Drad. -/
theorem calibratedWindow_ballContainment_of_coordinateAmplitude
    (P : CalibratedSeedWindow F u) :
    letI : MetricSpace M := F.metricSpace
    ∃ (r : ℝ) (K : ℝ≥0), 0 < r ∧
      ∀ (z zc : ℝ × P.seed.covector.ker) {Rt Rw Drad : ℝ},
        z ∈ P.domain → zc ∈ P.domain →
        |z.1 - P.center.1| ≤ Rt → ‖z.2 - P.center.2‖ ≤ Rw →
        |zc.1 - P.center.1| ≤ Rt → ‖zc.2 - P.center.2‖ ≤ Rw →
        (P.seed.constant P.center : ℝ) * max Rt Rw < r / 2 →
        ‖P.readout z - P.readout zc‖ ≤ Drad →
        dist (P.toManifold z) (P.toManifold zc) ≤ (K : ℝ) * Drad := by
  letI : MetricSpace M := F.metricSpace
  obtain ⟨r, K, hr, hcont⟩ := calibratedWindow_ballContainment (P := P)
  refine ⟨r, K, hr, ?_⟩
  intro z zc Rt Rw Drad hz hzc ht hw htc hwc hshrink hamp
  have hzball := inter_subset_left hz
  have hzcball := inter_subset_left hzc
  have hzdev := readout_deviation_le_of_coordinate_deviation P hzball ht hw
  have hzcdev := readout_deviation_le_of_coordinate_deviation P hzcball htc hwc
  exact hcont z zc hz hzc (lt_of_le_of_lt hzdev hshrink)
    (lt_of_le_of_lt hzcdev hshrink) hamp

/-- **Half-radius shrink with the coordinate amplitude instantiated.**  The
readout amplitude is bounded by the seed local constant times twice the retained
coordinate amplitude (triangle through the single centre), so under the
corresponding half-radius condition the retained pair lies in one manifold ball
of radius K times that explicit amplitude. -/
theorem calibratedWindow_ballContainment_of_labelBall
    (P : CalibratedSeedWindow F u) :
    letI : MetricSpace M := F.metricSpace
    ∃ (r : ℝ) (K : ℝ≥0), 0 < r ∧
      ∀ (z zc : ℝ × P.seed.covector.ker) {Rt Rw : ℝ},
        z ∈ P.domain → zc ∈ P.domain →
        |z.1 - P.center.1| ≤ Rt → ‖z.2 - P.center.2‖ ≤ Rw →
        |zc.1 - P.center.1| ≤ Rt → ‖zc.2 - P.center.2‖ ≤ Rw →
        (P.seed.constant P.center : ℝ) * max Rt Rw < r / 2 →
        dist (P.toManifold z) (P.toManifold zc) ≤
          (K : ℝ) * ((P.seed.constant P.center : ℝ) * (2 * max Rt Rw)) := by
  letI : MetricSpace M := F.metricSpace
  obtain ⟨r, K, hr, hcont⟩ := calibratedWindow_ballContainment_of_coordinateAmplitude
    (P := P)
  refine ⟨r, K, hr, ?_⟩
  intro z zc Rt Rw hz hzc ht hw htc hwc hshrink
  have hzball := inter_subset_left hz
  have hzcball := inter_subset_left hzc
  have hdz : dist z P.center ≤ max Rt Rw := by
    rw [Prod.dist_eq, Real.dist_eq, dist_eq_norm]
    exact max_le_max ht hw
  have hdzc : dist P.center zc ≤ max Rt Rw := by
    rw [Prod.dist_eq, Real.dist_eq, dist_eq_norm]
    exact max_le_max (by rw [abs_sub_comm]; exact htc) (by rw [norm_sub_rev]; exact hwc)
  have htri : dist z zc ≤ 2 * max Rt Rw := by
    calc dist z zc ≤ dist z P.center + dist P.center zc := dist_triangle _ _ _
      _ ≤ max Rt Rw + max Rt Rw := add_le_add hdz hdzc
      _ = 2 * max Rt Rw := by ring
  have hamp : ‖P.readout z - P.readout zc‖ ≤
      (P.seed.constant P.center : ℝ) * (2 * max Rt Rw) := by
    have h1 := P.lipschitzOn_readout.dist_le_mul z hzball zc hzcball
    rw [dist_eq_norm] at h1
    exact h1.trans (mul_le_mul_of_nonneg_left htri (NNReal.coe_nonneg _))
  exact hcont z zc hz hzc ht hw htc hwc hshrink hamp

end OTSelector.Reconstruction
