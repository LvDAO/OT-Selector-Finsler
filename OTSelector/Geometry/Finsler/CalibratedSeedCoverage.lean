import OTSelector.Geometry.Finsler.Basic
import OTSelector.Geometry.Finsler.C11FamilyCover
import OTSelector.Geometry.Finsler.CalibratedClockShift
import OTSelector.Geometry.Finsler.CalibratedCompleteCylinder
import OTSelector.Geometry.Finsler.CalibratedInterior
import OTSelector.Geometry.Finsler.CalibratedLevelSeedPatch
import OTSelector.Geometry.Finsler.CalibratedTranslation
import OTSelector.Geometry.Finsler.CompleteHamiltonianFamily
import OTSelector.Geometry.Finsler.Energy.Basic
import OTSelector.Geometry.Finsler.Geodesic.Defs
import OTSelector.Geometry.Finsler.LengthMetric
import OTSelector.Transport.Kantorovich.CalibratedReach

/-!
# Geometry.Finsler.CalibratedSeedCoverage

* **Conditions:** A point in the actual calibrated interior and the existing rational initial-level seed cover.
* **Objects:** A complete unit calibrated curve through the point and an actual rational seed/endpoints window containing it.
* **Proof detail:** Choose a rational potential level along its true local clock, identify the selected seed curve by time-shift uniqueness and choose rational calibration endpoint times.

Mathematical sources:
- [Rotem Assouline, Curvature-Dimension for Autonomous Lagrangians, arXiv:2409.08001v6 (10 February 2026)](https://arxiv.org/pdf/2409.08001v6#page=29): Sections 4–4.1, Definition 4.2 and Proposition 4.3, p. 29; Lemma 4.5, pp. 30–31; Definition 4.6 and Lemma 4.8, pp. 31–32.
- [Rotem Assouline, Curvature-Dimension for Autonomous Lagrangians, arXiv:2409.08001v6 (10 February 2026)](https://arxiv.org/pdf/2409.08001v6#page=38): Section 4.3, Proposition 4.18(i)–(iv), pp. 38–39, especially change of variables (4.13); Lemma 4.23 and proof, pp. 46–47.
- [Jiří Lebl, Basic Analysis I: Introduction to Real Analysis, Volume I](https://www.jirka.org/ra/realanal.pdf#page=31): Section 1.2.2, Theorem 1.2.4, p. 31.

Source relation (derived): The construction is pointwise on every interior point and needs no levelwise AE selection.
-/

/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Geometry.FinslerCalibratedSeedCoverage.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Geometry.FinslerCalibratedSeedCoverage`; the selected original proof blocks follow. -/
section

/-!
# Original calibrated points covered by rational level seed windows

Every original calibrated interior point lies on a complete unit curve with a
positive two-sided potential clock. A rational potential level on that curve
selects an actual seed; complete-curve identification transports the original
point into a rational endpoint window of that seed, without a levelwise AE choice.
-/

open Set Metric Manifold Bundle
open scoped Topology ContDiff NNReal

noncomputable section
namespace OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [PreconnectedSpace M]
  {F : ContinuousFinslerNorm E M}

/-- Every original calibrated interior point admits a complete original unit curve
with a strictly positive two-sided interval carrying its exact original potential clock. -/
theorem exists_complete_unit_calibrated_curve_of_mem_calibratedInterior
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    {u : M → ℝ} (hu : let _instInteriorCurveLip : MetricSpace M := F.metricSpace
      LipschitzWith 1 u)
    {y : M} (hy : let _instInteriorCurveSet : MetricSpace M := F.metricSpace
      y ∈ OTSelector.Geometry.calibratedInterior u) :
    ∃ (c : ℝ → M) (δ : ℝ), 0 < δ ∧ c 0 = y ∧ F.IsEulerLagrangeOn c univ ∧
      (∀ t : ℝ, F.toFun (tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) c ⟨t, (1 : ℝ)⟩) = 1) ∧
      ∀ t ∈ Icc (-δ) δ, u (c t) = u y + t := by
  let _instInteriorCurveMetric : MetricSpace M := F.metricSpace
  obtain ⟨ι, _, old, K, U, G, L, δ, A, Γ, hdata, hcover, hreach, hfamily⟩ :=
    hF.exists_countable_calibrated_C11_family_cover hcomplete hu
  have hycover : y ∈ ⋃ i, (extChartAt 𝓘(ℝ, E) (old i)).symm '' K i := by
    rwa [hcover]
  obtain ⟨i, x, hx, hxy⟩ := mem_iUnion.mp hycover
  obtain ⟨_, hKt, _, _, _, _, hmatch, _⟩ := hdata i
  obtain ⟨_, hKU, _, hfamilyi⟩ := hfamily i
  obtain ⟨hzero, hEL, _, hp⟩ := hfamilyi x (hKU hx)
  obtain ⟨hδ, _, hpartners⟩ := hreach i
  obtain ⟨a, _, b, _, ha, hua, hb, hub⟩ := hpartners x hx
  have hd : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ) u
      ((extChartAt 𝓘(ℝ, E) (old i)).symm x) :=
    hF.mdifferentiableAt_of_mem_calibratedInterior hcomplete hu (hxy.symm ▸ hy)
  have hmomentum : F.chartMomentumFamily (old i) (Γ i) (x, 0) =
      (x, fderiv ℝ (u ∘ (extChartAt 𝓘(ℝ, E) (old i)).symm) x) := by
    rw [hp, hmatch hx]
  obtain ⟨hunit, _, _, hclock, _⟩ :=
    hF.calibrated_translation_of_chartMomentum hcomplete (old i) hu (hKt hx)
      hEL hzero hmomentum hd hδ ⟨ha, hua⟩ ⟨hb, hub⟩
  exact ⟨Γ i x, δ i, hδ, hzero.trans hxy, hEL, hunit, by simpa only [hxy] using hclock⟩

variable [MeasurableSpace E] [BorelSpace E]

omit [BorelSpace E] in
/-- Exact initial coverage of rational original-potential levels covers every calibrated
interior point by an actual seed curve inside a rational endpoint-calibrated window. -/
theorem exists_calibrated_window_seed_of_rational_initial_cover
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    {u : M → ℝ} (hu : let _instRationalSeedLip : MetricSpace M := F.metricSpace
      LipschitzWith 1 u)
    {κ : Type*} (P : κ → F.CalibratedLevelSeedPatch u)
    (hcover : let _instRationalSeedCover : MetricSpace M := F.metricSpace
      ∀ q : ℚ, ∀ z ∈ OTSelector.Geometry.calibratedInterior u, u z = (q : ℝ) →
        ∃ k, ∃ w ∈ (P k).labels, (P k).curve w 0 = z)
    {y : M} (hy : let _instRationalSeedPoint : MetricSpace M := F.metricSpace
      y ∈ OTSelector.Geometry.calibratedInterior u) :
    ∃ k, ∃ w ∈ (P k).labels, ∃ (t : ℝ) (a b : ℚ), a < 0 ∧ 0 < b ∧
      t ∈ Ioo (a : ℝ) (b : ℝ) ∧ (P k).curve w t = y ∧
      u ((P k).curve w (a : ℝ)) = ((P k).level : ℝ) + (a : ℝ) ∧
      u ((P k).curve w (b : ℝ)) = ((P k).level : ℝ) + (b : ℝ) := by
  let _instRationalSeedMetric : MetricSpace M := F.metricSpace
  obtain ⟨c, δ, hδ, hc0, hc, hunit, hclock⟩ :=
    hF.exists_complete_unit_calibrated_curve_of_mem_calibratedInterior hcomplete hu hy
  obtain ⟨q, hql, hqu⟩ := exists_rat_btwn (show u y - δ / 2 < u y + δ / 2 by linarith)
  let s : ℝ := (q : ℝ) - u y
  have hslow : -δ / 2 < s := by dsimp [s]; linarith
  have hshigh : s < δ / 2 := by dsimp [s]; linarith
  have hs : s ∈ Ioo (-δ) δ := ⟨by linarith, by linarith⟩
  have hsclosed : s ∈ Icc (-δ) δ := ⟨hs.1.le, hs.2.le⟩
  have hδle : -δ ≤ δ := by linarith
  have hinterior := (hF.calibrated_window_of_complete_unit_endpoints hu hc hunit
    (hclock (-δ) (left_mem_Icc.mpr hδle))
    (hclock δ (right_mem_Icc.mpr hδle))).2.2 s hs
  have hvalue : u (c s) = (q : ℝ) := by rw [hclock s hsclosed]; dsimp [s]; ring
  obtain ⟨k, w, hw, hd0⟩ := hcover q (c s) hinterior hvalue
  have hlevel : u ((P k).curve w 0) = ((P k).level : ℝ) := by
    simpa only [add_zero] using (P k).clock w hw 0
      ⟨neg_nonpos.mpr (P k).reach_pos.le, (P k).reach_pos.le⟩
  have hdclock : ∀ t ∈ Icc (-(P k).reach) (P k).reach,
      u ((P k).curve w t) = u ((P k).curve w 0) + t := by
    intro t ht
    rw [hlevel]
    exact (P k).clock w hw t ht
  have hshift := hF.eq_timeShift_of_complete_unit_calibrated_clocks hcomplete hu
    hc ((P k).complete w hw) hunit ((P k).unit w hw) hδ (P k).reach_pos
    (by simpa only [hc0] using hclock) hdclock hs hd0
  have hlevelc : ((P k).level : ℝ) = u y + s :=
    hlevel.symm.trans ((congrArg u hd0).trans (hclock s hsclosed))
  have hback : (P k).curve w (-s) = y := by
    rw [hshift]
    simpa only [neg_add_cancel] using hc0
  obtain ⟨a, hal, hau⟩ := exists_rat_btwn
    (show -δ - s < min 0 (-s) from lt_min (by linarith [hs.1]) (by linarith))
  obtain ⟨b, hbl, hbu⟩ := exists_rat_btwn
    (show max 0 (-s) < δ - s from max_lt (by linarith [hs.2]) (by linarith))
  have ha0 : (a : ℝ) < 0 := hau.trans_le (min_le_left _ _)
  have hat : (a : ℝ) < -s := hau.trans_le (min_le_right _ _)
  have hb0 : (0 : ℝ) < b := (le_max_left _ _).trans_lt hbl
  have htb : -s < (b : ℝ) := (le_max_right _ _).trans_lt hbl
  have haI : (a : ℝ) + s ∈ Icc (-δ) δ := ⟨by linarith, by linarith [hs.2]⟩
  have hbI : (b : ℝ) + s ∈ Icc (-δ) δ := ⟨by linarith [hs.1], by linarith⟩
  refine ⟨k, w, hw, -s, a, b, by exact_mod_cast ha0, by exact_mod_cast hb0,
    ⟨hat, htb⟩, hback, ?_, ?_⟩
  · rw [hshift, hclock _ haI, hlevelc]
    ring
  · rw [hshift, hclock _ hbI, hlevelc]
    ring

end OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

end
end
