import OTSelector.Geometry.Finsler.Basic
import OTSelector.Geometry.Finsler.CalibratedCompleteCylinder
import OTSelector.Geometry.Finsler.CalibratedInterior
import OTSelector.Geometry.Finsler.CalibratedIntervalCovector
import OTSelector.Geometry.Finsler.CalibratedLevelSeedPatch
import OTSelector.Geometry.Finsler.CalibratedSeedCoverage
import OTSelector.Geometry.Finsler.Energy.Basic
import OTSelector.Geometry.Finsler.Geodesic.Basic
import OTSelector.Geometry.Finsler.Geodesic.Defs
import OTSelector.Geometry.Finsler.LengthMetric
import OTSelector.Geometry.Finsler.PotentialGlobalFamily
import OTSelector.Geometry.Finsler.PotentialPairShift
import OTSelector.Transport.Kantorovich.CalibratedReach

/-!
# Geometry.Finsler.CalibratedSeedRecovery

* **Conditions:** An actual complete seed with local potential clock and ordered original labels; a tested point lies in the same calibrated-interior label class.
* **Objects:** Recovery of the point by that same complete seed at its actual potential difference, and exact complete-curve shifts for calibrated initial pairs.
* **Proof detail:** Derive true initial covectors from local clocks, use ordered calibration between the two base points and identify complete curves by tangent uniqueness.

Mathematical sources:
- [Rotem Assouline, Curvature-Dimension for Autonomous Lagrangians, arXiv:2409.08001v6 (10 February 2026)](https://arxiv.org/pdf/2409.08001v6#page=29): Sections 4–4.1, Definition 4.2 and Proposition 4.3, p. 29; Lemma 4.5, pp. 30–31; Definition 4.6 and Lemma 4.8, pp. 31–32.
- [Zhongmin Shen, Landsberg Curvature, S-Curvature and Riemann Curvature, MSRI Publications 50 (2004)](https://library.slmath.org/books/Book50/files/08Sh.pdf#page=6): Section 2, p. 308, Legendre transformation, inverse Legendre transformation and equation (2–12).
- [Gerald Teschl, Ordinary Differential Equations and Dynamical Systems (AMS 2012 author preliminary version)](https://www.mat.univie.ac.at/~gerald/ftp/book-ode/ode.pdf#page=61): Section 2.6, pp. 50–51, overlap uniqueness, equation (2.63), and Theorem 2.13 (unique maximal solution).

Source relation (derived): No globally calibrated clock or prior meeting of the two curves is assumed.
-/

/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Geometry.FinslerCalibratedSeedRecovery.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Geometry.FinslerCalibratedSeedRecovery`; the selected original proof blocks follow. -/
section

/-!
# Complete original seed curves recover every interior point of the same label

A calibrated initial pair identifies complete unit curves carrying local clocks of
the original potential. The ordered geometric-label characterization then recovers
any calibrated interior point from its chosen seed at the actual potential difference.
No globally calibrated clock or prior meeting of the curves is assumed.
-/

open Set Metric Manifold Bundle
open scoped Topology ContDiff NNReal

noncomputable section
namespace OTSelector.Geometry.ContinuousFinslerNorm

set_option backward.isDefEq.respectTransparency false

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [PreconnectedSpace M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}

namespace IsSmoothStronglyConvex

private theorem initial_covector_of_complete_unit_clock (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _instSeedCovectorLip : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    {c : ℝ → M} (hc : F.IsEulerLagrangeOn c univ)
    (hunit : ∀ t : ℝ,
      F.toFun (tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) c ⟨t, (1 : ℝ)⟩) = 1)
    {δ : ℝ} (hδ : 0 < δ)
    (hclock : ∀ t ∈ Icc (-δ) δ, u (c t) = u (c 0) + t) :
    MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ) u (c 0) ∧
      mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) c 0 1 ≠ 0 ∧
      fderiv ℝ (F.fiberEnergy (c 0)) (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) c 0 1) =
        mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) u (c 0) := by
  let _instSeedCovectorMetric : MetricSpace M := F.metricSpace
  have hab : -δ < δ := by linarith
  have hwindow := hF.calibrated_window_of_complete_unit_endpoints hu hc hunit
    (hclock (-δ) (left_mem_Icc.mpr hab.le)) (hclock δ (right_mem_Icc.mpr hab.le))
  have hdu := hF.mdifferentiableAt_of_mem_calibratedInterior hcomplete hu
    (hwindow.2.2 0 ⟨neg_neg_of_pos hδ, hδ⟩)
  refine ⟨hdu, ?_, ?_⟩
  · intro hz
    have h := hunit 0
    change F.toFun ⟨c 0, mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) c 0 1⟩ = 1 at h
    rw [hz, F.map_zero] at h
    exact zero_ne_one h
  · apply (hF.mfderiv_eq_fiberEnergy_of_calibrated_closedInterval hu hab hwindow.2.1
      ?_ (show (0 : ℝ) ∈ Icc (-δ) δ from ⟨by linarith, hδ.le⟩)
      ((hF.contMDiffAt_of_isEulerLagrangeAt (hc 0 (mem_univ _))).mdifferentiableAt
        (by simp)) (hunit 0) hdu).symm
    rw [hclock δ (right_mem_Icc.mpr hab.le), hclock (-δ) (left_mem_Icc.mpr hab.le)]
    ring

/-- Local original clocks and a calibrated initial pair identify the entire complete
unit curves after the actual potential difference, without a supplied meeting point. -/
theorem eq_timeShift_of_calibrated_pair_of_complete_unit_clocks
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _instSeedPairLip : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    {c d : ℝ → M} (hc : F.IsEulerLagrangeOn c univ) (hd : F.IsEulerLagrangeOn d univ)
    (hcunit : ∀ t : ℝ,
      F.toFun (tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) c ⟨t, (1 : ℝ)⟩) = 1)
    (hdunit : ∀ t : ℝ,
      F.toFun (tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) d ⟨t, (1 : ℝ)⟩) = 1)
    {δ ε : ℝ} (hδ : 0 < δ) (hε : 0 < ε)
    (hcclock : ∀ t ∈ Icc (-δ) δ, u (c t) = u (c 0) + t)
    (hdclock : ∀ t ∈ Icc (-ε) ε, u (d t) = u (d 0) + t)
    (hsat : let _instSeedPairSat : MetricSpace M := F.metricSpace
      u (d 0) - u (c 0) = dist (c 0) (d 0)) :
    c = fun t ↦ d (t + u (c 0) - u (d 0)) := by
  obtain ⟨hduc, hvc, hpc⟩ := hF.initial_covector_of_complete_unit_clock
    hcomplete hu hc hcunit hδ hcclock
  obtain ⟨hdud, hvd, hpd⟩ := hF.initial_covector_of_complete_unit_clock
    hcomplete hu hd hdunit hε hdclock
  exact hF.eq_timeShift_of_calibrated_pair hcomplete hu hsat hduc hdud hc hd
    hvc hvd rfl rfl hpc hpd

end IsSmoothStronglyConvex

namespace CalibratedLevelSeedPatch

variable [MeasurableSpace E]

/-- Every original calibrated interior point with the seed's geometric label lies
on that complete seed curve at exactly its original potential difference. -/
theorem curve_eq_point_of_same_geometricLabel
    (S : CalibratedLevelSeedPatch F u) (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _instSeedRecoveryLip : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    {Z : Type*} {a : M → Z}
    (horder : let _instSeedRecoveryOrder : MetricSpace M := F.metricSpace
      ∀ x ∈ F.potentialRegularDomain u, ∀ y ∈ F.potentialRegularDomain u,
        (a x = a y ∧ u x ≤ u y) ↔ u y - u x = dist x y)
    {w : S.covector.ker} (hw : w ∈ S.labels) {x : M}
    (hx : let _instSeedRecoveryInterior : MetricSpace M := F.metricSpace
      x ∈ OTSelector.Geometry.calibratedInterior u)
    (ha : a x = a (S.curve w 0)) :
    S.curve w (u x - (S.level : ℝ)) = x := by
  let _instSeedRecoveryMetric : MetricSpace M := F.metricSpace
  have hseed := S.mapsTo_initial_calibratedInterior hF hu hw
  have hsreg := hF.mem_potentialRegularDomain_of_mem_calibratedInterior hcomplete hu hseed
  have hxreg := hF.mem_potentialRegularDomain_of_mem_calibratedInterior hcomplete hu hx
  obtain ⟨c, δ, hδ, hc0, hc, hunit, hclock⟩ :=
    hF.exists_complete_unit_calibrated_curve_of_mem_calibratedInterior hcomplete hu hx
  have hcclock : ∀ t ∈ Icc (-δ) δ, u (c t) = u (c 0) + t := by
    simpa only [hc0] using hclock
  have hsclock : ∀ t ∈ Icc (-S.reach) S.reach,
      u (S.curve w t) = u (S.curve w 0) + t := by
    rw [S.potential_initial hw]
    exact S.clock w hw
  rcases le_total (u (S.curve w 0)) (u x) with hle | hle
  · have hsat : u (c 0) - u (S.curve w 0) = dist (S.curve w 0) (c 0) := by
      rw [hc0]
      exact (horder _ hsreg _ hxreg).mp ⟨ha.symm, hle⟩
    have heq := hF.eq_timeShift_of_calibrated_pair_of_complete_unit_clocks hcomplete hu
      (S.complete w hw) hc (S.unit w hw) hunit S.reach_pos hδ hsclock hcclock hsat
    simpa only [S.potential_initial hw, hc0, sub_add_cancel, sub_self] using
      congrFun heq (u x - (S.level : ℝ))
  · have hsat : u (S.curve w 0) - u (c 0) = dist (c 0) (S.curve w 0) := by
      rw [hc0]
      exact (horder _ hxreg _ hsreg).mp ⟨ha, hle⟩
    have heq := hF.eq_timeShift_of_calibrated_pair_of_complete_unit_clocks hcomplete hu
      hc (S.complete w hw) hunit (S.unit w hw) hδ S.reach_pos hcclock hsclock hsat
    simpa only [zero_add, hc0, S.potential_initial hw] using (congrFun heq 0).symm

end CalibratedLevelSeedPatch
end OTSelector.Geometry.ContinuousFinslerNorm

end
end
