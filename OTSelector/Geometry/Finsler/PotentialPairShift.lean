import OTSelector.Geometry.Finsler.Basic
import OTSelector.Geometry.Finsler.CalibratedIntervalCovector
import OTSelector.Geometry.Finsler.Energy.Basic
import OTSelector.Geometry.Finsler.Geodesic.Defs
import OTSelector.Geometry.Finsler.Geodesic.SmoothMinimizer
import OTSelector.Geometry.Finsler.LegendreInjectivity
import OTSelector.Geometry.Finsler.LengthMetric
import OTSelector.Geometry.Finsler.PotentialInitialState
import OTSelector.Geometry.Finsler.TimeShiftUnique

/-!
# Geometry.Finsler.PotentialPairShift

* **Conditions:** An actual calibrated endpoint pair and complete potential-covector curves at its endpoints.
* **Objects:** Their exact original-potential time shift, including the degenerate equal-point case.
* **Proof detail:** Construct the actual unit minimizing segment, identify both endpoint covectors and tangent states, then apply complete trajectory uniqueness.

Mathematical sources:
- [Rotem Assouline, Curvature-Dimension for Autonomous Lagrangians, arXiv:2409.08001v6 (10 February 2026)](https://arxiv.org/pdf/2409.08001v6#page=29): Sections 4–4.1, Definition 4.2 and Proposition 4.3, p. 29; Lemma 4.5, pp. 30–31; Definition 4.6 and Lemma 4.8, pp. 31–32.
- [Zhongmin Shen, Landsberg Curvature, S-Curvature and Riemann Curvature, MSRI Publications 50 (2004)](https://library.slmath.org/books/Book50/files/08Sh.pdf#page=6): Section 2, p. 308, Legendre transformation, inverse Legendre transformation and equation (2–12).
- [Gerald Teschl, Ordinary Differential Equations and Dynamical Systems (AMS 2012 author preliminary version)](https://www.mat.univie.ac.at/~gerald/ftp/book-ode/ode.pdf#page=61): Section 2.6, pp. 50–51, overlap uniqueness, equation (2.63), and Theorem 2.13 (unique maximal solution).

Source relation (derived): Derived from the cited geometric/analytic principles with the exact actual source hypotheses. The local construction and its original phase/covector data are retained, rather than asserted as a verbatim source statement.
-/

/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Geometry.FinslerPotentialPairShift.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Geometry.FinslerPotentialPairShift`; the selected original proof blocks follow. -/
section

/-!
# Actual calibrated pairs identify potential curves after their clock shift

A unit original minimizing segment between calibrated endpoints identifies both
endpoint energy covectors with the actual differential of the same potential.
Actual Legendre injectivity identifies the endpoint tangent states of arbitrary
complete potential-covector curves with those of this segment. Original initial
value uniqueness then gives their exact potential-clock translation, including
the degenerate pair, without assuming unit speed or a common curve.
-/

open Set Filter Metric Manifold Bundle
open scoped Topology ContDiff NNReal ENNReal

noncomputable section
namespace OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

set_option backward.isDefEq.respectTransparency false

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [PreconnectedSpace M]
  {F : ContinuousFinslerNorm E M}

omit [FiniteDimensional ℝ E] [T2Space M] [PreconnectedSpace M] in
private theorem tangentMap_eq_of_fiberEnergy_covector (hF : F.IsSmoothStronglyConvex)
    (x : M) {g : ℝ → M} {t : ℝ} (hgx : g t = x)
    {v : TangentSpace 𝓘(ℝ, E) x} (hv : v ≠ 0)
    (hg0 : mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) g t 1 ≠ 0) {u : M → ℝ}
    (hp : fderiv ℝ (F.fiberEnergy x) v = mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) u x)
    (hgp : mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) u (g t) =
      fderiv ℝ (F.fiberEnergy (g t)) (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) g t 1)) :
    tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) g ⟨t, (1 : ℝ)⟩ = ⟨x, v⟩ := by
  let instPairShiftFiberNorm : NormedAddCommGroup (TangentSpace 𝓘(ℝ, E) x) :=
    inferInstanceAs (NormedAddCommGroup E)
  let instPairShiftFiberSpace : NormedSpace ℝ (TangentSpace 𝓘(ℝ, E) x) :=
    inferInstanceAs (NormedSpace ℝ E)
  have hPg : fderiv ℝ (F.fiberEnergyModel x) (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) g t 1) =
      mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) u x := by
    change fderiv ℝ (F.fiberEnergy x) _ = _
    rw [← hgx]
    exact hgp.symm
  have hPv : fderiv ℝ (F.fiberEnergyModel x) v =
      mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) u x := hp
  have hvel := hF.injOn_fiberEnergy_legendre x hg0 hv (hPg.trans hPv.symm)
  exact TotalSpace.ext hgx (heq_of_eq hvel)

/-- Every calibrated original pair identifies complete actual potential-covector
curves after exactly the potential difference in time. Unit speed, a common curve,
or a prescribed translation are not input assumptions. Equal endpoints are included. -/
theorem eq_timeShift_of_calibrated_pair (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    {u : M → ℝ} (hu : let _instPotentialPairShiftLip : MetricSpace M := F.metricSpace
      LipschitzWith 1 u)
    {x y : M}
    (hsat : let _instPotentialPairShiftSat : MetricSpace M := F.metricSpace
      u y - u x = dist x y)
    (hdux : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ) u x)
    (hduy : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ) u y)
    {c d : ℝ → M} (hc : F.IsEulerLagrangeOn c univ) (hd : F.IsEulerLagrangeOn d univ)
    {v : TangentSpace 𝓘(ℝ, E) x} {w : TangentSpace 𝓘(ℝ, E) y}
    (hv : v ≠ 0) (hw : w ≠ 0)
    (hci : tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) c ⟨0, (1 : ℝ)⟩ = ⟨x, v⟩)
    (hdi : tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) d ⟨0, (1 : ℝ)⟩ = ⟨y, w⟩)
    (hp : fderiv ℝ (F.fiberEnergy x) v = mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) u x)
    (hq : fderiv ℝ (F.fiberEnergy y) w = mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) u y) :
    c = fun t ↦ d (t + u x - u y) := by
  let _instPotentialPairShiftMetric : MetricSpace M := F.metricSpace
  let _instPotentialPairShiftENorm :
      ∀ z : M, ENorm (TangentSpace 𝓘(ℝ, E) z) := F.enorm
  by_cases hxy : x = y
  · subst y
    have heq := hF.eq_of_complete_initial_fiberEnergy_covectors hc hd x hv hw hci hdi
      (hp.trans hq.symm)
    simpa only [add_sub_cancel_right] using heq
  obtain ⟨g, hg0, hgy, hgEL, hgsm, hgs, hgi, _⟩ :=
    hF.exists_smooth_lengthMetric_minimizer hcomplete hxy
  have hgsat : u (g (dist x y)) - u (g 0) = dist x y - 0 := by
    simpa only [hgy, hg0, sub_zero] using hsat
  have hcov (t : ℝ) (ht : t ∈ Icc (0 : ℝ) (dist x y))
      (hdu : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ) u (g t)) :
      mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) u (g t) =
        fderiv ℝ (F.fiberEnergy (g t)) (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) g t 1) :=
    hF.mfderiv_eq_fiberEnergy_of_calibrated_closedInterval hu (dist_pos.mpr hxy)
      hgi hgsat ht (hgsm.mdifferentiable (by simp) t) (hgs t) hdu
  have hn (t : ℝ) : mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) g t 1 ≠ 0 := by
    intro hz
    have hunit := hgs t
    change F.toFun ⟨g t, mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) g t 1⟩ = 1 at hunit
    rw [hz, F.map_zero] at hunit
    exact zero_ne_one hunit
  have htg0 : tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) g ⟨0, (1 : ℝ)⟩ = ⟨x, v⟩ := by
    apply tangentMap_eq_of_fiberEnergy_covector hF x hg0 hv (hn 0) hp
    apply hcov 0 (left_mem_Icc.mpr dist_nonneg)
    rwa [hg0]
  have htgy : tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) g ⟨dist x y, (1 : ℝ)⟩ = ⟨y, w⟩ := by
    apply tangentMap_eq_of_fiberEnergy_covector hF y hgy hw (hn (dist x y)) hq
    apply hcov (dist x y) (right_mem_Icc.mpr dist_nonneg)
    rwa [hgy]
  have hcg : c = g := by
    simpa only [sub_zero, add_zero] using
      hF.eq_timeShift_of_complete_tangent_eq hc hgEL (hci.trans htg0.symm)
  have hgd : g = fun t ↦ d (t - dist x y) := by
    simpa only [add_zero] using
      hF.eq_timeShift_of_complete_tangent_eq hgEL hd (htgy.trans hdi.symm)
  rw [hcg, hgd]
  funext t
  congr 1
  rw [← hsat]
  ring

end OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

end
end
