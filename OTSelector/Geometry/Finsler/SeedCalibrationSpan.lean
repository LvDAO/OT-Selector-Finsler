import OTSelector.Geometry.Finsler.Basic
import OTSelector.Geometry.Finsler.CalibratedCompleteCylinder
import OTSelector.Geometry.Finsler.CalibratedLevelSeedPatch
import OTSelector.Geometry.Finsler.CalibratedSeedWindow
import OTSelector.Geometry.Finsler.Energy.Basic
import OTSelector.Geometry.Finsler.Geodesic.Basic
import OTSelector.Geometry.Finsler.LengthMetric
import OTSelector.Transport.Kantorovich.CalibratedReach
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Geometry.FinslerSeedCalibrationSpan.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Geometry.FinslerSeedCalibrationSpan`; the selected original proof blocks follow. -/
section

/-!
# Geometry.Finsler.SeedCalibrationSpan

* **Conditions:** An actual complete seed and a 1-Lipschitz potential; the seed labels and normalization remain fixed.
* **Objects:** A closed interval of calibrated times and an exact countable rational-window cover of its interior, including a fixed-chart-ball version.
* **Proof detail:** Use continuity for closedness, unit-speed endpoint calibration for interval convexity and rational density plus the existing local cover for all interior times.

Mathematical sources:
- [Rotem Assouline, Curvature-Dimension for Autonomous Lagrangians, arXiv:2409.08001v6 (10 February 2026)](https://arxiv.org/pdf/2409.08001v6#page=29): Sections 4–4.1, Definition 4.2 and Proposition 4.3, p. 29; Lemma 4.5, pp. 30–31; Definition 4.6 and Lemma 4.8, pp. 31–32.
- [Rotem Assouline, Curvature-Dimension for Autonomous Lagrangians, arXiv:2409.08001v6 (10 February 2026)](https://arxiv.org/pdf/2409.08001v6#page=38): Section 4.3, Proposition 4.18(i)–(iv), pp. 38–39, especially change of variables (4.13); Lemma 4.23 and proof, pp. 46–47.
- [Jiří Lebl, Basic Analysis I: Introduction to Real Analysis, Volume I](https://www.jirka.org/ra/realanal.pdf#page=31): Section 1.2.2, Theorem 1.2.4, p. 31.

Source relation (derived): The rational-window enumeration is a local countability implementation; finite or arbitrary real support endpoints are allowed.
-/

/-!
# The full calibrated interval of one original seed

Calibration is closed and persists between any two calibrated times. Rational
windows of the same seed cover every interior time, including spans with arbitrary
real endpoints. All windows retain the original labels and Haar normalization.
-/

open Set Filter Metric MeasureTheory Manifold
open scoped Topology ContDiff

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OTSelector.Geometry.ContinuousFinslerNorm.CalibratedLevelSeedPatch

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}

/-- All times at which the same complete original curve follows its original clock. -/
def calibrationTimes (S : CalibratedLevelSeedPatch F u) (w : S.covector.ker) : Set ℝ :=
  {t | u (S.curve w t) = (S.level : ℝ) + t}

/-- Countably many rational calibration endpoints and actual chart centers for one seed. -/
abbrev RationalWindowIndex (S : CalibratedLevelSeedPatch F u) :=
  ({a : ℚ // a < 0} × {b : ℚ // 0 < b}) × S.centers

instance (S : CalibratedLevelSeedPatch F u) : Countable S.RationalWindowIndex := by
  let : Countable S.centers := S.centers_countable.to_subtype
  infer_instance

/-- Each indexed window uses exactly the original seed and its fixed normalization. -/
def rationalWindow (S : CalibratedLevelSeedPatch F u) (k : S.RationalWindowIndex) :
    CalibratedSeedWindow F u where
  seed := S
  left := k.1.1.val
  right := k.1.2.val
  left_neg := k.1.1.property
  right_pos := k.1.2.property
  center := k.2.val
  center_mem := k.2.property

variable [T2Space M] [PreconnectedSpace M]

omit [BorelSpace E] in
/-- The same complete original curve retains calibration at all finite limits of
calibrated times, including endpoints of a compact scalar support. -/
theorem isClosed_calibrationTimes (S : CalibratedLevelSeedPatch F u)
    (hF : F.IsSmoothStronglyConvex)
    (hu : let _instClosedClockLip : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    {w : S.covector.ker} (hw : w ∈ S.labels) : IsClosed (S.calibrationTimes w) := by
  let _instClosedClockMetric : MetricSpace M := F.metricSpace
  have hc : Continuous (S.curve w) :=
    continuous_iff_continuousAt.mpr (fun t ↦
      (hF.contMDiffAt_of_isEulerLagrangeAt (S.complete w hw t (mem_univ _))).continuousAt)
  exact isClosed_eq (hu.continuous.comp hc) (continuous_const.add continuous_id)

omit [BorelSpace E] in
/-- Calibration along the same complete unit curve fills the interval between
any two calibrated times. -/
theorem Icc_subset_calibrationTimes (S : CalibratedLevelSeedPatch F u)
    (hF : F.IsSmoothStronglyConvex)
    (hu : let _instSpanClockLip : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    {w : S.covector.ker} (hw : w ∈ S.labels) {a b : ℝ}
    (ha : a ∈ S.calibrationTimes w) (hb : b ∈ S.calibrationTimes w) :
    Icc a b ⊆ S.calibrationTimes w :=
  (hF.calibrated_window_of_complete_unit_endpoints hu (S.complete w hw) (S.unit w hw)
    ha hb).1

omit [BorelSpace E] in
/-- Arbitrary real calibrated endpoints admit rational screened windows on the
same seed around every interior time. -/
theorem exists_rational_endpoints_of_calibrated_span (S : CalibratedLevelSeedPatch F u)
    (hF : F.IsSmoothStronglyConvex)
    (hu : let _instRationalClockLip : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    {w : S.covector.ker} (hw : w ∈ S.labels) {a b t : ℝ}
    (ha : a ∈ S.calibrationTimes w) (hb : b ∈ S.calibrationTimes w)
    (ht : t ∈ Ioo a b) :
    ∃ (l r : ℚ), l < 0 ∧ 0 < r ∧ t ∈ Ioo (l : ℝ) r ∧
      (l : ℝ) ∈ S.calibrationTimes w ∧ (r : ℝ) ∈ S.calibrationTimes w := by
  let L := min a (-S.reach)
  let U := max b S.reach
  have hL : L ∈ S.calibrationTimes w := by
    rcases min_cases a (-S.reach) with ⟨heq, _⟩ | ⟨heq, _⟩
    · simpa only [L, heq] using ha
    · simpa only [L, heq, calibrationTimes, mem_ofPred_eq] using
        S.clock w hw (-S.reach) ⟨le_rfl, by linarith [S.reach_pos]⟩
  have hU : U ∈ S.calibrationTimes w := by
    rcases max_cases b S.reach with ⟨heq, _⟩ | ⟨heq, _⟩
    · simpa only [U, heq] using hb
    · simpa only [U, heq, calibrationTimes, mem_ofPred_eq] using
        S.clock w hw S.reach ⟨by linarith [S.reach_pos], le_rfl⟩
  have hLt : L < min t 0 := lt_min ((min_le_left _ _).trans_lt ht.1)
    ((min_le_right _ _).trans_lt (neg_neg_of_pos S.reach_pos))
  have htU : max t 0 < U := max_lt (ht.2.trans_le (le_max_left _ _))
    (S.reach_pos.trans_le (le_max_right _ _))
  obtain ⟨l, hLl, hl⟩ := exists_rat_btwn hLt
  obtain ⟨r, hr, hrU⟩ := exists_rat_btwn htU
  have hl0 : l < 0 := by exact_mod_cast hl.trans_le (min_le_right t 0)
  have hr0 : 0 < r := by exact_mod_cast (le_max_right t 0).trans_lt hr
  have hlt : (l : ℝ) < t := hl.trans_le (min_le_left t 0)
  have htr : t < (r : ℝ) := (le_max_left t 0).trans_lt hr
  have hspan := S.Icc_subset_calibrationTimes hF hu hw hL hU
  exact ⟨l, r, hl0, hr0, ⟨hlt, htr⟩,
    hspan ⟨hLl.le, (hlt.trans htr).le.trans hrU.le⟩,
    hspan ⟨hLl.le.trans (hlt.trans htr).le, hrU.le⟩⟩

omit [BorelSpace E] in
/-- Every interior point of a real calibrated span belongs to an actual rational
window of this same seed. -/
theorem exists_rationalWindow_of_calibrated_span (S : CalibratedLevelSeedPatch F u)
    (hF : F.IsSmoothStronglyConvex)
    (hu : let _instWindowSpanLip : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    {w : S.covector.ker} (hw : w ∈ S.labels) {a b t : ℝ}
    (ha : a ∈ S.calibrationTimes w) (hb : b ∈ S.calibrationTimes w)
    (ht : t ∈ Ioo a b) :
    ∃ k : S.RationalWindowIndex, (t, w) ∈ (S.rationalWindow k).domain := by
  obtain ⟨l, r, hl, hr, htime, hleft, hright⟩ :=
    S.exists_rational_endpoints_of_calibrated_span hF hu hw ha hb ht
  have hm : (t, w) ∈ ⋃ q ∈ S.centers, ball q (S.radius q) := by
    rw [S.local_cover]
    exact ⟨mem_univ _, S.labels_subset hw⟩
  obtain ⟨q, hq, hball⟩ := mem_iUnion₂.mp hm
  exact ⟨(⟨⟨l, hl⟩, ⟨r, hr⟩⟩, ⟨q, hq⟩), hball, htime, hw, hleft, hright⟩

omit [BorelSpace E] in
/-- The fixed countable family covers exactly the entire active time interval of
each original label, rather than a single prescribed rational subinterval. -/
theorem iUnion_rationalWindow_timeDomain (S : CalibratedLevelSeedPatch F u)
    (hF : F.IsSmoothStronglyConvex)
    (hu : let _instFullClockLip : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    {w : S.covector.ker} (hw : w ∈ S.labels) :
    (⋃ k : S.RationalWindowIndex, {t : ℝ | (t, w) ∈ (S.rationalWindow k).domain}) =
      interior (S.calibrationTimes w) := by
  apply Subset.antisymm
  · intro t ht
    obtain ⟨k, hk⟩ := mem_iUnion.mp ht
    apply mem_interior_iff_mem_nhds.mpr
    apply Filter.mem_of_superset (isOpen_Ioo.mem_nhds hk.2.1)
    exact Ioo_subset_Icc_self.trans
      (S.Icc_subset_calibrationTimes hF hu hw hk.2.2.2.1 hk.2.2.2.2)
  · intro t ht
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp ht)
    have hlo : t - ε / 2 ∈ S.calibrationTimes w := hball (by
      rw [mem_ball, Real.dist_eq, sub_sub_cancel_left, abs_neg, abs_of_pos (half_pos hε)]
      exact half_lt_self hε)
    have hhi : t + ε / 2 ∈ S.calibrationTimes w := hball (by
      rw [mem_ball, Real.dist_eq, add_sub_cancel_left, abs_of_pos (half_pos hε)]
      exact half_lt_self hε)
    obtain ⟨k, hk⟩ := S.exists_rationalWindow_of_calibrated_span hF hu hw hlo hhi
      (show t ∈ Ioo (t - ε / 2) (t + ε / 2) by constructor <;> linarith)
    exact mem_iUnion.mpr ⟨k, hk⟩

omit [BorelSpace E] in
/-- With one chart center fixed, rational endpoint screens cover the full active
part of that chart. The curve, chart readout and parameter normalization stay fixed. -/
theorem iUnion_rationalWindow_fixedCenter_timeDomain (S : CalibratedLevelSeedPatch F u)
    (hF : F.IsSmoothStronglyConvex)
    (hu : let _instFixedChartClockLip : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (q : S.centers) {w : S.covector.ker} (hw : w ∈ S.labels)
    (hwball : w ∈ ball q.1.2 (S.radius q)) :
    (⋃ lr : ({a : ℚ // a < 0} × {b : ℚ // 0 < b}),
      {t : ℝ | (t, w) ∈ (S.rationalWindow (lr, q)).domain}) =
      interior (S.calibrationTimes w) ∩ ball q.1.1 (S.radius q) := by
  apply Subset.antisymm
  · intro t ht
    obtain ⟨lr, hlr⟩ := mem_iUnion.mp ht
    refine ⟨?_, ?_⟩
    · rw [← S.iUnion_rationalWindow_timeDomain hF hu hw]
      exact mem_iUnion.mpr ⟨(lr, q), hlr⟩
    · have hball := hlr.1
      change max (dist t q.1.1) (dist w q.1.2) < S.radius q at hball
      exact (max_lt_iff.mp hball).1
  · intro t ht
    have hactive := ht.1
    rw [← S.iUnion_rationalWindow_timeDomain hF hu hw] at hactive
    obtain ⟨k, hk⟩ := mem_iUnion.mp hactive
    refine mem_iUnion.mpr ⟨k.1, ?_, hk.2⟩
    change max (dist t q.1.1) (dist w q.1.2) < S.radius q
    exact max_lt ht.2 hwball

end OTSelector.Geometry.ContinuousFinslerNorm.CalibratedLevelSeedPatch

end
end
