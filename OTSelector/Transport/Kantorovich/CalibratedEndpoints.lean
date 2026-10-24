import OTSelector.Geometry.Finsler.Basic
import OTSelector.Geometry.Finsler.CalibratedCovector
import OTSelector.Geometry.Finsler.CalibratedPartnerOrientation
import OTSelector.Geometry.Finsler.CalibratedReach
import OTSelector.Geometry.Finsler.Energy.Basic
import OTSelector.Geometry.Finsler.Geodesic.Defs
import OTSelector.Geometry.Finsler.Geodesic.SmoothMinimizer
import OTSelector.Geometry.Finsler.LengthMetric
import OTSelector.Topology.MetricSpace.SaturatedCalibration
import OTSelector.Transport.Kantorovich.CalibratedReach
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Geometry.FinslerCalibratedEndpoints.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Geometry.FinslerCalibratedEndpoints`; the selected original proof blocks follow. -/
section

/-!
Conditions: A dominated potential and calibrated/isometric curves; properness, completeness and Euler–Lagrange hypotheses occur only in the corresponding reach/trajectory variants.

Objects: Initial/final endpoints, their negation duality, endpoint uniqueness and actual calibrated-segment endpoint realization.

Proof detail: Unpack calibration inequalities, use equality of distance on isometric subsegments, and apply compact reach/actual trajectory arguments for the stronger variants.

Sources: Rotem Assouline, Section 4, Definitions 4.1–4.2 and Proposition 4.3; Section 4.1, Definitions 4.4/4.6 and Lemma 4.5 (https://arxiv.org/html/2409.08001v6#S4.SS1); Zhongmin Shen, Section 4, pp. 313–314, length distance, Definition 4.1 and Lemma 4.2, equations (4–1)–(4–4) (https://library.slmath.org/books/Book50/files/08Sh.pdf#page=11).
Relation: Definitions and derived proper-metric/Finsler variants of calibrated rays. The Tonelli paper is a mathematical model, not an identical hypothesis package.
-/

/-!
# Genuine one-sided calibrated endpoints

Initial endpoints have a nontrivial forward calibrated partner and no nontrivial
backward partner. Terminal endpoints have the reversed property. These sets are
Borel for the original complete Finsler distance. An ordered geometric label has
at most one endpoint of each orientation on its regular domain. Actual complete
potential-covector curves enter the two-sided interior at every strictly intermediate
positive time along a forward calibrated segment. No endpoint mass claim is assumed.
-/

open Set Filter Metric Manifold Bundle MeasureTheory
open scoped Topology ContDiff NNReal ENNReal

noncomputable section
namespace OTSelector.Geometry

section Metric
variable {M Z : Type*} [MetricSpace M]

/-- A genuine initial endpoint has a forward calibrated partner but no predecessor. -/
def calibratedInitialEndpoints (u : M → ℝ) : Set M :=
  {x | (∃ y, x ≠ y ∧ u y - u x = dist x y) ∧
    ¬ ∃ y, y ≠ x ∧ u x - u y = dist y x}

/-- A genuine terminal endpoint has a calibrated predecessor but no successor. -/
def calibratedTerminalEndpoints (u : M → ℝ) : Set M :=
  {x | (∃ y, y ≠ x ∧ u x - u y = dist y x) ∧
    ¬ ∃ y, x ≠ y ∧ u y - u x = dist x y}

/-- Reversing the original potential exchanges the endpoint orientations. -/
theorem calibratedTerminalEndpoints_eq_initial_neg (u : M → ℝ) :
    calibratedTerminalEndpoints u = calibratedInitialEndpoints (-u) := by
  ext x
  simp only [calibratedTerminalEndpoints, calibratedInitialEndpoints, mem_ofPred_eq,
    Pi.neg_apply, neg_sub_neg, ne_comm, dist_comm]

/-- The ordered calibration relation makes the label injective on initial endpoints
of the domain where that relation holds. No measure or endpoint order is assumed. -/
theorem injOn_label_calibratedInitialEndpoints {u : M → ℝ} {a : M → Z} {N : Set M}
    (horder : ∀ x ∈ N, ∀ y ∈ N,
      (a x = a y ∧ u x ≤ u y) ↔ u y - u x = dist x y) :
    InjOn a (calibratedInitialEndpoints u ∩ N) := by
  intro x hx y hy hlabel
  by_contra hxy
  rcases le_total (u x) (u y) with hle | hle
  · exact hy.1.2 ⟨x, hxy, (horder x hx.2 y hy.2).mp ⟨hlabel, hle⟩⟩
  · exact hx.1.2 ⟨y, (Ne.symm hxy), (horder y hy.2 x hx.2).mp ⟨hlabel.symm, hle⟩⟩

/-- The same actual ordered relation allows at most one terminal endpoint per label. -/
theorem injOn_label_calibratedTerminalEndpoints {u : M → ℝ} {a : M → Z} {N : Set M}
    (horder : ∀ x ∈ N, ∀ y ∈ N,
      (a x = a y ∧ u x ≤ u y) ↔ u y - u x = dist x y) :
    InjOn a (calibratedTerminalEndpoints u ∩ N) := by
  intro x hx y hy hlabel
  by_contra hxy
  rcases le_total (u x) (u y) with hle | hle
  · exact hx.1.2 ⟨y, hxy, (horder x hx.2 y hy.2).mp ⟨hlabel, hle⟩⟩
  · exact hy.1.2 ⟨x, (Ne.symm hxy), (horder y hy.2 x hx.2).mp ⟨hlabel.symm, hle⟩⟩

/-- Every strictly intermediate point on the same calibrated isometric segment is
an actual two-sided interior point, with the exact distance from its initial point. -/
theorem calibratedInterior_of_calibrated_isometry {u : M → ℝ} {c : ℝ → M} {b : ℝ}
    (hu : LipschitzWith 1 u)
    (hiso : Isometry (fun t : Icc (0 : ℝ) b ↦ c t))
    (hsat : u (c b) - u (c 0) = b) {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) b) :
    c t ∈ calibratedInterior u ∧ dist (c 0) (c t) = t := by
  have hb : 0 ≤ b := (ht.1.trans ht.2).le
  have ht' : t ∈ Icc (0 : ℝ) b := ⟨ht.1.le, ht.2.le⟩
  have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) b := left_mem_Icc.mpr hb
  have hb' : b ∈ Icc (0 : ℝ) b := right_mem_Icc.mpr hb
  have hclock := eq_affine_of_lipschitz_saturated_isometry hu hiso
    (by simpa only [sub_zero] using hsat)
  have hdt : dist (c 0) (c t) = t := by
    simpa only [Subtype.dist_eq, Real.dist_eq, zero_sub,
      abs_neg, abs_of_pos ht.1] using hiso.dist_eq ⟨0, h0⟩ ⟨t, ht'⟩
  have htb : dist (c t) (c b) = b - t := by
    simpa only [Subtype.dist_eq, Real.dist_eq, abs_of_neg (sub_neg.mpr ht.2), neg_sub]
      using hiso.dist_eq ⟨t, ht'⟩ ⟨b, hb'⟩
  refine ⟨⟨⟨c 0, dist_pos.mp (hdt.symm ▸ ht.1), ?_⟩,
    ⟨c b, dist_pos.mp (htb.symm ▸ sub_pos.mpr ht.2), ?_⟩⟩, hdt⟩
  · rw [hclock t ht', hdt]
    ring
  · rw [hclock b hb', hclock t ht', htb]
    ring

end Metric

namespace ContinuousFinslerNorm
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [PreconnectedSpace M]
  (F : ContinuousFinslerNorm E M)

private theorem forward_calibrated_set_eq_iUnion {u : M → ℝ} :
    let _instEndpointsReachMetric : MetricSpace M := F.metricSpace
    {x | ∃ y, x ≠ y ∧ u y - u x = dist x y} =
      ⋃ n : ℕ, {x | ∃ y, (1 / (n + 1 : ℝ)) ≤ dist x y ∧
        u y - u x = dist x y} := by
  let _instEndpointsReachMetric : MetricSpace M := F.metricSpace
  ext x
  constructor
  · rintro ⟨y, hxy, hsat⟩
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt (dist_pos.mpr hxy)
    exact mem_iUnion.mpr ⟨n, y, hn.le, hsat⟩
  · intro hx
    obtain ⟨n, y, hn, hsat⟩ := mem_iUnion.mp hx
    exact ⟨y, dist_pos.mp (lt_of_lt_of_le (by positivity) hn), hsat⟩

variable [MeasurableSpace M] [BorelSpace M]

private theorem measurableSet_forward_calibrated
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace) {u : M → ℝ}
    (hu : let _instEndpointsForwardLip : MetricSpace M := F.metricSpace
      LipschitzWith 1 u) :
    let _instEndpointsForwardMetric : MetricSpace M := F.metricSpace
    MeasurableSet {x | ∃ y, x ≠ y ∧ u y - u x = dist x y} := by
  let _instEndpointsForwardMetric : MetricSpace M := F.metricSpace
  dsimp only
  rw [F.forward_calibrated_set_eq_iUnion]
  exact MeasurableSet.iUnion (fun n ↦
    (F.isClosed_calibratedReach_ge hcomplete hu (r := 1 / (n + 1 : ℝ))
      (by positivity)).measurableSet)

/-- Genuine initial endpoints of an original complete Finsler calibration form a Borel set. -/
theorem measurableSet_calibratedInitialEndpoints
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace) {u : M → ℝ}
    (hu : let _instInitialEndpointsLip : MetricSpace M := F.metricSpace
      LipschitzWith 1 u) :
    let _instInitialEndpointsMetric : MetricSpace M := F.metricSpace
    MeasurableSet (calibratedInitialEndpoints u) := by
  let _instInitialEndpointsMetric : MetricSpace M := F.metricSpace
  dsimp only
  have hback := F.measurableSet_forward_calibrated hcomplete hu.neg
  dsimp only at hback
  have heq : {x | ∃ y, x ≠ y ∧ (-u) y - (-u) x = dist x y} =
      {x | ∃ y, y ≠ x ∧ u x - u y = dist y x} := by
    ext x
    simp only [mem_ofPred_eq, Pi.neg_apply, neg_sub_neg, ne_comm, dist_comm]
  rw [heq] at hback
  exact (F.measurableSet_forward_calibrated hcomplete hu).inter hback.compl

/-- Genuine terminal endpoints are Borel for the same original complete distance. -/
theorem measurableSet_calibratedTerminalEndpoints
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace) {u : M → ℝ}
    (hu : let _instTerminalEndpointsLip : MetricSpace M := F.metricSpace
      LipschitzWith 1 u) :
    let _instTerminalEndpointsMetric : MetricSpace M := F.metricSpace
    MeasurableSet (calibratedTerminalEndpoints u) := by
  let _instTerminalEndpointsMetric : MetricSpace M := F.metricSpace
  dsimp only
  rw [calibratedTerminalEndpoints_eq_initial_neg]
  exact F.measurableSet_calibratedInitialEndpoints hcomplete hu.neg

namespace IsSmoothStronglyConvex

omit [MeasurableSpace M] [BorelSpace M] in
/-- A genuine forward calibrated partner identifies the same complete potential-covector
curve with the actual unit minimizing segment. Every strictly intermediate positive time
is in the two-sided calibrated interior and has exactly that distance from the start. -/
theorem calibrated_forward_curve_of_initial_covector {F : ContinuousFinslerNorm E M}
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    {c : ℝ → M} (hc : F.IsEulerLagrangeOn c univ)
    (hv : mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) c 0 1 ≠ 0)
    {u : M → ℝ} (hu : let _instEndpointShiftLip : MetricSpace M := F.metricSpace
      LipschitzWith 1 u) {y : M} (hxy : c 0 ≠ y)
    (hsat : let _instEndpointShiftSat : MetricSpace M := F.metricSpace
      u y - u (c 0) = dist (c 0) y)
    (hdu : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ) u (c 0))
    (hp : mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) u (c 0) =
      fderiv ℝ (F.fiberEnergy (c 0)) (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) c 0 1)) :
    let _instEndpointShiftMetric : MetricSpace M := F.metricSpace
    (∀ t : ℝ, F.toFun (tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) c ⟨t, (1 : ℝ)⟩) = 1) ∧
      c (dist (c 0) y) = y ∧
      Isometry (fun t : Icc (0 : ℝ) (dist (c 0) y) ↦ c t) ∧
      (∀ t ∈ Icc (0 : ℝ) (dist (c 0) y), u (c t) = u (c 0) + t) ∧
      ∀ t ∈ Ioo (0 : ℝ) (dist (c 0) y),
        c t ∈ calibratedInterior u ∧ dist (c 0) (c t) = t := by
  let _instEndpointShiftMetric : MetricSpace M := F.metricSpace
  dsimp only
  let _instEndpointShiftENorm : ∀ x : M, ENorm (TangentSpace 𝓘(ℝ, E) x) := F.enorm
  obtain ⟨g, hg0, hgy, hgEL, hgsm, hgs, hgi, _⟩ :=
    hF.exists_smooth_lengthMetric_minimizer hcomplete hxy
  have hgsat : u (g (dist (c 0) y)) - u (g 0) = dist (c 0) y - 0 := by
    simpa only [hgy, hg0, sub_zero] using hsat
  have hgp : mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) u (g 0) =
      fderiv ℝ (F.fiberEnergy (g 0)) (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) g 0 1) := by
    apply hF.mfderiv_eq_fiberEnergy_of_calibrated_interval hu (dist_pos.mpr hxy)
      hgi hgsat (hgsm.mdifferentiable (by simp) 0) (hgs 0)
    rwa [hg0]
  have hgv : mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) g 0 1 ≠ 0 := by
    intro hz
    have hunit := hgs 0
    change F.toFun ⟨g 0, mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) g 0 1⟩ = 1 at hunit
    rw [hz, F.map_zero] at hunit
    exact zero_ne_one hunit
  have heq := hF.eq_of_complete_initial_fiberEnergy_covector hc hgEL rfl hg0 hv hgv hp hgp
  have hclock := eq_affine_of_lipschitz_saturated_isometry hu hgi hgsat
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro t
    rw [heq]
    exact hgs t
  · simpa only [← heq] using hgy
  · simpa only [← heq] using hgi
  · intro t ht
    have hh := hclock t ht
    simpa only [← heq, sub_zero] using hh
  · intro t ht
    have hh := calibratedInterior_of_calibrated_isometry hu hgi
      (by simpa only [sub_zero] using hgsat) ht
    simpa only [← heq] using hh

end IsSmoothStronglyConvex
end ContinuousFinslerNorm
end OTSelector.Geometry

end
end
