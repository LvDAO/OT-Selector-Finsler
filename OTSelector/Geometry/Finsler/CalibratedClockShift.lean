import OTSelector.Geometry.Finsler.Basic
import OTSelector.Geometry.Finsler.CalibratedCompleteCylinder
import OTSelector.Geometry.Finsler.CalibratedInterior
import OTSelector.Geometry.Finsler.CalibratedIntervalCovector
import OTSelector.Geometry.Finsler.Energy.Basic
import OTSelector.Geometry.Finsler.Geodesic.Basic
import OTSelector.Geometry.Finsler.Geodesic.Defs
import OTSelector.Geometry.Finsler.LegendreInjectivity
import OTSelector.Geometry.Finsler.LengthMetric
import OTSelector.Geometry.Finsler.TimeShiftUnique
import OTSelector.Transport.Kantorovich.CalibratedReach

/-!
# Geometry.Finsler.CalibratedClockShift

* **Conditions:** Two actual complete unit curves have local clocks of the same original potential and meet at an interior calibrated time.
* **Objects:** Their exact whole-curve time translation.
* **Proof detail:** Derive both actual initial covectors from their clocks and use original Legendre injectivity and complete-state uniqueness.

Mathematical sources:
- [Rotem Assouline, Curvature-Dimension for Autonomous Lagrangians, arXiv:2409.08001v6 (10 February 2026)](https://arxiv.org/pdf/2409.08001v6#page=29): Sections 4–4.1, Definition 4.2 and Proposition 4.3, p. 29; Lemma 4.5, pp. 30–31; Definition 4.6 and Lemma 4.8, pp. 31–32.
- [Zhongmin Shen, Landsberg Curvature, S-Curvature and Riemann Curvature, MSRI Publications 50 (2004)](https://library.slmath.org/books/Book50/files/08Sh.pdf#page=6): Section 2, p. 308, Legendre transformation, inverse Legendre transformation and equation (2–12).
- [Gerald Teschl, Ordinary Differential Equations and Dynamical Systems (AMS 2012 author preliminary version)](https://www.mat.univie.ac.at/~gerald/ftp/book-ode/ode.pdf#page=61): Section 2.6, pp. 50–51, overlap uniqueness, equation (2.63), and Theorem 2.13 (unique maximal solution).

Source relation (derived): Derived from the cited geometric/analytic principles with the exact actual source hypotheses. The local construction and its original phase/covector data are retained, rather than asserted as a verbatim source statement.
-/

/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Geometry.FinslerCalibratedClockShift.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Geometry.FinslerCalibratedClockShift`; the selected original proof blocks follow. -/
section

/-!
# Complete original curves identified by their calibrated clocks

Two complete unit Euler--Lagrange curves with local clocks of the same original
potential agree after shifting one to an interior point of the other. The clocks
construct the actual potential covectors; original Legendre injectivity and complete
trajectory uniqueness identify the entire curves without a supplied momentum equation.
-/

open Set Metric Manifold Bundle
open scoped Topology ContDiff NNReal

noncomputable section
namespace OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

set_option backward.isDefEq.respectTransparency false

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [PreconnectedSpace M]
  {F : ContinuousFinslerNorm E M}

/-- Local original-potential clocks identify complete unit curves after the actual
meeting-time shift. Differentiability and equality of their energy covectors are derived. -/
theorem eq_timeShift_of_complete_unit_calibrated_clocks
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    {u : M → ℝ} (hu : let _instCalibratedClockShiftLip : MetricSpace M := F.metricSpace
      LipschitzWith 1 u)
    {c d : ℝ → M} (hc : F.IsEulerLagrangeOn c univ)
    (hd : F.IsEulerLagrangeOn d univ)
    (hcunit : ∀ t : ℝ,
      F.toFun (tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) c ⟨t, (1 : ℝ)⟩) = 1)
    (hdunit : ∀ t : ℝ,
      F.toFun (tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) d ⟨t, (1 : ℝ)⟩) = 1)
    {δ ε s : ℝ} (hδ : 0 < δ) (hε : 0 < ε)
    (hcclock : ∀ t ∈ Icc (-δ) δ, u (c t) = u (c 0) + t)
    (hdclock : ∀ t ∈ Icc (-ε) ε, u (d t) = u (d 0) + t)
    (hs : s ∈ Ioo (-δ) δ) (hd0 : d 0 = c s) :
    d = fun r ↦ c (r + s) := by
  let _instCalibratedClockShiftMetric : MetricSpace M := F.metricSpace
  have hδab : -δ < δ := by linarith
  have hεab : -ε < ε := by linarith
  have hcwindow := hF.calibrated_window_of_complete_unit_endpoints hu hc hcunit
    (hcclock (-δ) (left_mem_Icc.mpr hδab.le))
    (hcclock δ (right_mem_Icc.mpr hδab.le))
  have hdwindow := hF.calibrated_window_of_complete_unit_endpoints hu hd hdunit
    (hdclock (-ε) (left_mem_Icc.mpr hεab.le))
    (hdclock ε (right_mem_Icc.mpr hεab.le))
  have hdu := hF.mdifferentiableAt_of_mem_calibratedInterior hcomplete hu
    (hcwindow.2.2 s hs)
  have hdd : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ) u (d 0) := by rwa [hd0]
  have hcovc := hF.mfderiv_eq_fiberEnergy_of_calibrated_closedInterval hu
    hδab hcwindow.2.1 (by
      rw [hcclock δ (right_mem_Icc.mpr hδab.le),
        hcclock (-δ) (left_mem_Icc.mpr hδab.le)]
      ring) ⟨hs.1.le, hs.2.le⟩
    ((hF.contMDiffAt_of_isEulerLagrangeAt (hc s (mem_univ _))).mdifferentiableAt
      (by simp)) (hcunit s) hdu
  have hcovd := hF.mfderiv_eq_fiberEnergy_of_calibrated_closedInterval hu
    hεab hdwindow.2.1 (by
      rw [hdclock ε (right_mem_Icc.mpr hεab.le),
        hdclock (-ε) (left_mem_Icc.mpr hεab.le)]
      ring) (show (0 : ℝ) ∈ Icc (-ε) ε from ⟨by linarith, hε.le⟩)
    ((hF.contMDiffAt_of_isEulerLagrangeAt (hd 0 (mem_univ _))).mdifferentiableAt
      (by simp)) (hdunit 0) hdd
  have hn (g : ℝ → M) (t : ℝ)
      (hunit : F.toFun (tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) g ⟨t, (1 : ℝ)⟩) = 1) :
      mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) g t 1 ≠ 0 := by
    intro hz
    change F.toFun ⟨g t, mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) g t 1⟩ = 1 at hunit
    rw [hz, F.map_zero] at hunit
    exact zero_ne_one hunit
  let instCalibratedClockShiftFiberNorm :
      NormedAddCommGroup (TangentSpace 𝓘(ℝ, E) (c s)) :=
    inferInstanceAs (NormedAddCommGroup E)
  let instCalibratedClockShiftFiberSpace :
      NormedSpace ℝ (TangentSpace 𝓘(ℝ, E) (c s)) :=
    inferInstanceAs (NormedSpace ℝ E)
  have hdp : fderiv ℝ (F.fiberEnergyModel (c s)) (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) d 0 1) =
      mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) u (c s) := by
    change fderiv ℝ (F.fiberEnergy (c s)) _ = _
    rw [← hd0]
    exact hcovd.symm
  have hcp : fderiv ℝ (F.fiberEnergyModel (c s)) (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) c s 1) =
      mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) u (c s) := hcovc.symm
  have hvel := hF.injOn_fiberEnergy_legendre (c s) (hn d 0 (hdunit 0))
    (hn c s (hcunit s)) (hdp.trans hcp.symm)
  have htan : tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) d ⟨0, (1 : ℝ)⟩ =
      tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) c ⟨s, (1 : ℝ)⟩ :=
    TotalSpace.ext hd0 (heq_of_eq hvel)
  simpa only [sub_zero] using hF.eq_timeShift_of_complete_tangent_eq hd hc htan

end OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

end
end
