import OTSelector.Geometry.Finsler.Basic
import OTSelector.Geometry.Finsler.CalibratedConstantSpeed
import OTSelector.Geometry.Finsler.CalibratedDistance
import OTSelector.Geometry.Finsler.CalibratedInterior
import OTSelector.Geometry.Finsler.Energy.Basic
import OTSelector.Geometry.Finsler.Geodesic.Basic
import OTSelector.Geometry.Finsler.Geodesic.Defs
import OTSelector.Geometry.Finsler.LengthMetric
import OTSelector.Transport.Kantorovich.CalibratedReach
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Geometry.CalibratedCompleteCylinder.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Geometry.CalibratedCompleteCylinder`; the selected original proof blocks follow. -/
section

/-!
# Geometry.Finsler.CalibratedCompleteCylinder

* **Conditions:** Actual complete unit-speed Euler–Lagrange curves have a common potential clock and injective initial seed positions; a 1-Lipschitz potential calibrates both interval endpoints.
* **Objects:** Calibration/isometry throughout the closed interval and injectivity of the actual interior time–label cylinder.
* **Proof detail:** Squeeze potential increments between unit-speed length bounds, recover time by the common clock and identify whole curves through an interior meeting point using calibrated uniqueness.

Mathematical sources:
- [Rotem Assouline, Curvature-Dimension for Autonomous Lagrangians, arXiv:2409.08001v6 (10 February 2026)](https://arxiv.org/pdf/2409.08001v6#page=29): Sections 4–4.1, Definition 4.2 and Proposition 4.3, p. 29; Lemma 4.5, pp. 30–31; Definition 4.6 and Lemma 4.8, pp. 31–32.
- [Zhongmin Shen, Landsberg Curvature, S-Curvature and Riemann Curvature, MSRI Publications 50 (2004)](https://library.slmath.org/books/Book50/files/08Sh.pdf#page=11): Section 4, Definition 4.1 and Lemma 4.2, pp. 313–314; equations (4–1), (4–2) and the canonical-lift spray interpretation.

Source relation (derived): A same-curve cylinder construction from actual endpoint calibration, rather than an assumed open foliation.
-/

/-!
# Injective calibrated cylinders from complete original unit curves

A common original-potential clock separates time. At an interior meeting point,
original differentiability and uniqueness identify the entire complete curves,
so initial seed injectivity separates labels even at arbitrary finite times.
-/

open Set Metric Manifold Bundle
open scoped Topology ContDiff NNReal

noncomputable section
namespace OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

variable {E M W : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [PreconnectedSpace M]
  {F : ContinuousFinslerNorm E M}

/-- Original calibration at two endpoints of a complete unit curve gives its entire
potential clock, original-distance isometry, and calibrated interior on the open interval.
No ordering assumption on the two endpoint times is required. -/
theorem calibrated_window_of_complete_unit_endpoints
    (hF : F.IsSmoothStronglyConvex)
    {u : M → ℝ} (hu : let _instCalibratedWindowLip : MetricSpace M := F.metricSpace
      LipschitzWith 1 u)
    {c : ℝ → M} {a b q : ℝ}
    (hEL : F.IsEulerLagrangeOn c univ)
    (hunit : ∀ t : ℝ,
      F.toFun (tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) c ⟨t, (1 : ℝ)⟩) = 1)
    (ha : u (c a) = q + a) (hb : u (c b) = q + b) :
    let _instCalibratedWindowMetric : MetricSpace M := F.metricSpace
    (∀ t ∈ Icc a b, u (c t) = q + t) ∧
      Isometry (fun t : Icc a b ↦ c t) ∧
      ∀ t ∈ Ioo a b, c t ∈ OTSelector.Geometry.calibratedInterior u := by
  let _instCalibratedWindowMetric : MetricSpace M := F.metricSpace
  have hcurve : LipschitzWith 1 c := by
    simpa only [hunit 0] using hF.lipschitzWith_of_isEulerLagrangeOn_univ hEL 0
  have hscalar : LipschitzWith 1 (u ∘ c) := by
    simpa only [one_mul] using hu.comp hcurve
  have hclock : ∀ t ∈ Icc a b, u (c t) = q + t := by
    intro t ht
    have hs := OTSelector.Geometry.eq_affine_of_lipschitz_saturated hscalar
      (a := a) (b := b) (by
        simp only [Function.comp_apply, ha, hb, NNReal.coe_one, one_mul]
        ring) t ht
    simp only [Function.comp_apply, ha, NNReal.coe_one, one_mul] at hs
    linarith
  have hiso : Isometry (fun t : Icc a b ↦ c t) :=
    F.isometry_Icc_of_unitSpeed_calibration (C := q) hu
      (((hF.contMDiffOn_of_isEulerLagrangeOn hEL).mono (subset_univ _)).of_le (by simp))
      (fun t _ ↦ hunit t)
      (fun t ht ↦ (hclock t ht).trans (add_comm q t))
  refine ⟨hclock, hiso, ?_⟩
  intro t ht
  have hab : a < b := ht.1.trans ht.2
  have htclosed : t ∈ Icc a b := ⟨ht.1.le, ht.2.le⟩
  have hleft : dist (c a) (c t) = t - a := by
    simpa only [Subtype.dist_eq, Real.dist_eq,
      abs_of_nonpos (sub_nonpos.mpr ht.1.le), neg_sub] using
      hiso.dist_eq ⟨a, left_mem_Icc.mpr hab.le⟩ ⟨t, htclosed⟩
  have hright : dist (c t) (c b) = b - t := by
    simpa only [Subtype.dist_eq, Real.dist_eq,
      abs_of_nonpos (sub_nonpos.mpr ht.2.le), neg_sub] using
      hiso.dist_eq ⟨t, htclosed⟩ ⟨b, right_mem_Icc.mpr hab.le⟩
  refine ⟨⟨c a, ?_, ?_⟩, ⟨c b, ?_, ?_⟩⟩
  · exact dist_pos.mp (by rw [hleft]; exact sub_pos.mpr ht.1)
  · rw [hclock t htclosed, ha, hleft]
    ring
  · exact dist_pos.mp (by rw [hright]; exact sub_pos.mpr ht.2)
  · rw [hb, hclock t htclosed, hright]
    ring

/-- A common calibrated clock makes the actual complete unit family injective in
both time and label on the open interval, provided its initial seeds are injective. -/
theorem injOn_calibrated_timeLabel_of_complete_unit_curves
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    {u : M → ℝ} (hu : let _instCompleteCylinderLip : MetricSpace M := F.metricSpace
      LipschitzWith 1 u)
    {Γ : W → ℝ → M} {S : Set W} {a b q : ℝ}
    (hEL : ∀ w ∈ S, F.IsEulerLagrangeOn (Γ w) univ)
    (hunit : ∀ w ∈ S, ∀ t : ℝ,
      F.toFun (tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (Γ w) ⟨t, (1 : ℝ)⟩) = 1)
    (hclock : ∀ w ∈ S, ∀ t ∈ Icc a b, u (Γ w t) = q + t)
    (hinitial : InjOn (fun w ↦ Γ w 0) S) :
    InjOn (fun p : ℝ × W ↦ Γ p.2 p.1) (Ioo a b ×ˢ S) := by
  let _instCompleteCylinderMetric : MetricSpace M := F.metricSpace
  intro p hp r hr heq
  have hab : a < b := hp.1.1.trans hp.1.2
  have hpt : p.1 ∈ Icc a b := ⟨hp.1.1.le, hp.1.2.le⟩
  have hrt : r.1 ∈ Icc a b := ⟨hr.1.1.le, hr.1.2.le⟩
  have ht : p.1 = r.1 := add_left_cancel
    ((hclock p.2 hp.2 p.1 hpt).symm.trans
      ((congrArg u heq).trans (hclock r.2 hr.2 r.1 hrt)))
  have hsame : Γ p.2 p.1 = Γ r.2 p.1 := by simpa only [ht] using heq
  have hinterior : Γ p.2 p.1 ∈ OTSelector.Geometry.calibratedInterior u :=
    (hF.calibrated_window_of_complete_unit_endpoints hu (hEL p.2 hp.2) (hunit p.2 hp.2)
      (hclock p.2 hp.2 a (left_mem_Icc.mpr hab.le))
      (hclock p.2 hp.2 b (right_mem_Icc.mpr hab.le))).2.2 p.1 hp.1
  have hcurves : Γ p.2 = Γ r.2 :=
    hF.eq_of_complete_unitSpeed_calibrated_curves (C := q) (D := q) hu hp.1.2
      (hEL p.2 hp.2) (hEL r.2 hr.2) hsame (hunit p.2 hp.2) (hunit r.2 hr.2)
      (fun t ht ↦ (hclock p.2 hp.2 t ⟨hp.1.1.le.trans ht.1, ht.2⟩).trans (add_comm q t))
      (fun t ht ↦ (hclock r.2 hr.2 t ⟨hp.1.1.le.trans ht.1, ht.2⟩).trans (add_comm q t))
      (hF.mdifferentiableAt_of_mem_calibratedInterior hcomplete hu hinterior)
  exact Prod.ext ht (hinitial hp.2 hr.2 (congrArg (fun c : ℝ → M ↦ c 0) hcurves))

/-- Original calibration at two endpoints suffices for joint time-label injectivity;
its full intervening clock follows from actual unit speed and scalar saturation. -/
theorem injOn_timeLabel_of_complete_unit_calibrated_endpoints
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    {u : M → ℝ} (hu : let _instCompleteEndpointLip : MetricSpace M := F.metricSpace
      LipschitzWith 1 u)
    {Γ : W → ℝ → M} {S : Set W} {a b q : ℝ}
    (hEL : ∀ w ∈ S, F.IsEulerLagrangeOn (Γ w) univ)
    (hunit : ∀ w ∈ S, ∀ t : ℝ,
      F.toFun (tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (Γ w) ⟨t, (1 : ℝ)⟩) = 1)
    (hend : ∀ w ∈ S, u (Γ w a) = q + a ∧ u (Γ w b) = q + b)
    (hinitial : InjOn (fun w ↦ Γ w 0) S) :
    InjOn (fun p : ℝ × W ↦ Γ p.2 p.1) (Ioo a b ×ˢ S) := by
  let _instCompleteEndpointMetric : MetricSpace M := F.metricSpace
  apply hF.injOn_calibrated_timeLabel_of_complete_unit_curves hcomplete hu hEL hunit
    (q := q) ?_ hinitial
  intro w hw
  exact (hF.calibrated_window_of_complete_unit_endpoints hu (hEL w hw) (hunit w hw)
    (hend w hw).1 (hend w hw).2).1

end OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

end
end
