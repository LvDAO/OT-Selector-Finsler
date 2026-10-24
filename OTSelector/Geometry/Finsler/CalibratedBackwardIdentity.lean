import OTSelector.Analysis.Convex.Legendre.Parametric
import OTSelector.Geometry.Finsler.Basic
import OTSelector.Geometry.Finsler.CalibratedIntervalCovector
import OTSelector.Geometry.Finsler.Energy.Basic
import OTSelector.Geometry.Finsler.Energy.Chart
import OTSelector.Geometry.Finsler.Geodesic.Basic
import OTSelector.Geometry.Finsler.Geodesic.Defs
import OTSelector.Geometry.Finsler.Geodesic.Proofs.LocalEquation
import OTSelector.Geometry.Finsler.LegendreInjectivity
import OTSelector.Geometry.Finsler.LengthMetric
import OTSelector.Geometry.Finsler.ManifoldTubeCalibration
import OTSelector.Geometry.Finsler.TangentReadout
import OTSelector.Geometry.Finsler.TimeShiftUnique

/-!
# Geometry.Finsler.CalibratedBackwardIdentity

* **Conditions:** Actual chart momentum at a calibrated point equals the original potential differential.
* **Objects:** The exact complete backward-time curve and its endpoint identity.
* **Proof detail:** Transfer chart momentum to the intrinsic covector, identify the true tangent via Legendre injectivity and apply translated complete-trajectory uniqueness.

Mathematical sources:
- [Zhongmin Shen, Landsberg Curvature, S-Curvature and Riemann Curvature, MSRI Publications 50 (2004)](https://library.slmath.org/books/Book50/files/08Sh.pdf#page=6): Section 2, p. 308, Legendre transformation, inverse Legendre transformation and equation (2–12).
- [Jiří Lebl, Basic Analysis II: Introduction to Real Analysis, Volume II (version 6.3, 15 May 2026)](https://www.jirka.org/ra/realanal2.pdf#page=38): Section 8.3, Theorem 8.3.7, p. 38; Exercise 8.3.7, p. 45 (differentiate the inverse identity).
- [Gerald Teschl, Ordinary Differential Equations and Dynamical Systems (AMS 2012 author preliminary version)](https://www.mat.univie.ac.at/~gerald/ftp/book-ode/ode.pdf#page=61): Section 2.6, pp. 50–51, overlap uniqueness, equation (2.63), and Theorem 2.13 (unique maximal solution).

Source relation (derived): Derived from the cited geometric/analytic principles with the exact actual source hypotheses. The local construction and its original phase/covector data are retained, rather than asserted as a verbatim source statement.
-/

/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Geometry.FinslerCalibratedBackwardIdentity.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Geometry.FinslerCalibratedBackwardIdentity`; the selected original proof blocks follow. -/
section

/-!
# Exact backward identification of the original calibrated curve

A genuine chart momentum at a calibrated point is the intrinsic energy covector
of the original potential. Nonlinear Legendre injectivity and complete Euler--Lagrange
uniqueness then identify the same curve at every time, including its original endpoint.
-/

open Set Filter Metric Manifold Bundle
open scoped Topology ContDiff NNReal

noncomputable section
namespace OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

set_option backward.isDefEq.respectTransparency false

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [PreconnectedSpace M]
  {F : ContinuousFinslerNorm E M}

omit [T2Space M] [PreconnectedSpace M] in
/-- Actual chart momentum equal to the original potential differential determines
its intrinsic energy covector and a nonzero actual velocity at the given time. -/
theorem intrinsic_covector_of_chartMomentum
    (hF : F.IsSmoothStronglyConvex) {c : ℝ → M} {t : ℝ}
    (hc : F.IsEulerLagrangeAt c t) (old : M)
    (hx : c t ∈ (extChartAt 𝓘(ℝ, E) old).source) {u : M → ℝ}
    (hd : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ) u (c t))
    (hp : eulerLagrangePhaseLift (F.chartEnergy old)
      (extChartAt 𝓘(ℝ, E) old ∘ c) t =
        (extChartAt 𝓘(ℝ, E) old (c t),
          fderiv ℝ (u ∘ (extChartAt 𝓘(ℝ, E) old).symm)
            (extChartAt 𝓘(ℝ, E) old (c t)))) :
    mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) c t 1 ≠ 0 ∧
      mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) u (c t) =
        fderiv ℝ (F.fiberEnergy (c t)) (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) c t 1) := by
  let instBackwardCovectorFiberNorm : NormedAddCommGroup (TangentSpace 𝓘(ℝ, E) (c t)) :=
    inferInstanceAs (NormedAddCommGroup E)
  let instBackwardCovectorFiberSpace : NormedSpace ℝ (TangentSpace 𝓘(ℝ, E) (c t)) :=
    inferInstanceAs (NormedSpace ℝ E)
  have hpFiber := congrArg Prod.snd hp
  change fiberLegendre (F.chartEnergy old)
    (extChartAt 𝓘(ℝ, E) old (c t), deriv (extChartAt 𝓘(ℝ, E) old ∘ c) t) =
      fderiv ℝ (u ∘ (extChartAt 𝓘(ℝ, E) old).symm)
        (extChartAt 𝓘(ℝ, E) old (c t)) at hpFiber
  let e := extChartAt 𝓘(ℝ, E) old
  let v := mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) c t 1
  let D := mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) e (c t)
  have hcDiff := (hF.contMDiffAt_of_isEulerLagrangeAt hc).mdifferentiableAt (by simp)
  have hchart : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, E) e (c t) :=
    mdifferentiableAt_extChartAt (by simpa only [extChartAt_source] using hx)
  have hvel : deriv (e ∘ c) t = D v := by
    have h := mfderiv_comp_apply t hchart hcDiff (1 : ℝ)
    rw [mfderiv_eq_fderiv] at h
    exact (fderiv_apply_one_eq_deriv (𝕜 := ℝ)).symm.trans h
  have hz : (e (c t), D v) ∈ chartEnergyDomain old := by
    have h := (hF.chartTangent_of_isEulerLagrangeAt hc old hx).2
    change (e (c t), deriv (e ∘ c) t) ∈ chartEnergyDomain old at h
    rwa [hvel] at h
  have hv : v ≠ 0 := fun hv ↦ hz.2 (by rw [hv, _root_.map_zero])
  have hi : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, E) e.symm (e (c t)) := by
    simpa only [modelWithCornersSelf_coe, range_id, mdifferentiableWithinAt_univ] using
      mdifferentiableWithinAt_extChartAt_symm (e.map_source hx)
  have hdi : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ) u (e.symm (e (c t))) := by
    rwa [e.left_inv hx]
  have hinv : (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) e.symm (e (c t))).comp D =
      ContinuousLinearMap.id ℝ _ := by
    simpa only [modelWithCornersSelf_coe, range_id, mfderivWithin_univ] using
      mfderivWithin_extChartAt_symm_comp_mfderiv_extChartAt' hx
  have hchain : (fderiv ℝ (u ∘ e.symm) (e (c t))).comp D =
      mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) u (c t) := by
    rw [← mfderiv_eq_fderiv, mfderiv_comp (e (c t)) hdi hi,
      ContinuousLinearMap.comp_assoc, hinv, ContinuousLinearMap.comp_id, e.left_inv hx]
  have hm := hF.chartEnergy_fderiv_comp_mfderiv old hx v hz
  change (fiberLegendre (F.chartEnergy old) (e (c t), D v)).comp D = _ at hm
  have hmomentum : fiberLegendre (F.chartEnergy old) (e (c t), D v) =
      fderiv ℝ (u ∘ e.symm) (e (c t)) := by
    change fiberLegendre (F.chartEnergy old) (e (c t), deriv (e ∘ c) t) = _ at hpFiber
    rwa [hvel] at hpFiber
  rw [hmomentum] at hm
  exact ⟨hv, hchain.symm.trans hm⟩

/-- The complete original curve with actual potential momentum at a calibrated point
is exactly the original calibrated trajectory shifted to that point. Its backward
value recovers the initial endpoint; no new minimizing curve or time-shift oracle is used. -/
theorem eq_timeShift_of_chartMomentum_at_calibrated_point
    (hF : F.IsSmoothStronglyConvex) (old : M)
    {u : M → ℝ} (hu : let _instBackwardShiftLip : MetricSpace M := F.metricSpace
      LipschitzWith 1 u)
    {c d : ℝ → M} (hc : F.IsEulerLagrangeOn c univ)
    (hd : F.IsEulerLagrangeOn d univ)
    {a b t : ℝ} (hab : a < b)
    (hiso : let _instBackwardShiftIso : MetricSpace M := F.metricSpace
      Isometry (fun r : Icc a b ↦ c r))
    (hsat : u (c b) - u (c a) = b - a) (ht : t ∈ Icc a b)
    (hunit : F.toFun (tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) c ⟨t, (1 : ℝ)⟩) = 1)
    (hdu : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ) u (c t))
    (hsource : c t ∈ (extChartAt 𝓘(ℝ, E) old).source) (hd0 : d 0 = c t)
    (hp : eulerLagrangePhaseLift (F.chartEnergy old)
      (extChartAt 𝓘(ℝ, E) old ∘ d) 0 =
        (extChartAt 𝓘(ℝ, E) old (c t),
          fderiv ℝ (u ∘ (extChartAt 𝓘(ℝ, E) old).symm)
            (extChartAt 𝓘(ℝ, E) old (c t)))) :
    d = (fun r ↦ c (r + t)) ∧ d (-t) = c 0 := by
  have hdsource : d 0 ∈ (extChartAt 𝓘(ℝ, E) old).source := by rwa [hd0]
  have hddu : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ) u (d 0) := by rwa [hd0]
  obtain ⟨hvd, hcovd⟩ := hF.intrinsic_covector_of_chartMomentum (hd 0 (mem_univ _))
    old hdsource hddu (by simpa only [hd0] using hp)
  have hcovc := hF.mfderiv_eq_fiberEnergy_of_calibrated_closedInterval hu hab hiso hsat ht
    ((hF.contMDiffAt_of_isEulerLagrangeAt (hc t (mem_univ _))).mdifferentiableAt
      (by simp)) hunit hdu
  have hvc : mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) c t 1 ≠ 0 := by
    intro hz
    change F.toFun ⟨c t, mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) c t 1⟩ = 1 at hunit
    rw [hz, F.map_zero] at hunit
    exact zero_ne_one hunit
  let instBackwardIntrinsicShiftFiberNorm :
      NormedAddCommGroup (TangentSpace 𝓘(ℝ, E) (c t)) :=
    inferInstanceAs (NormedAddCommGroup E)
  let instBackwardIntrinsicShiftFiberSpace :
      NormedSpace ℝ (TangentSpace 𝓘(ℝ, E) (c t)) :=
    inferInstanceAs (NormedSpace ℝ E)
  have hdp : fderiv ℝ (F.fiberEnergyModel (c t)) (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) d 0 1) =
      mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) u (c t) := by
    change fderiv ℝ (F.fiberEnergy (c t)) _ = _
    rw [← hd0]
    exact hcovd.symm
  have hcp : fderiv ℝ (F.fiberEnergyModel (c t)) (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) c t 1) =
      mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) u (c t) := hcovc.symm
  have hvel := hF.injOn_fiberEnergy_legendre (c t) hvd hvc (hdp.trans hcp.symm)
  have htan : tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) d ⟨0, (1 : ℝ)⟩ =
      tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) c ⟨t, (1 : ℝ)⟩ :=
    TotalSpace.ext hd0 (heq_of_eq hvel)
  have hshift : d = (fun r ↦ c (r + t)) := by
    simpa only [sub_zero] using hF.eq_timeShift_of_complete_tangent_eq hd hc htan
  refine ⟨hshift, ?_⟩
  rw [hshift]
  simp only [neg_add_cancel]

end OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

end
end
