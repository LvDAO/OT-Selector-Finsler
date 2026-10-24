import OTSelector.Geometry.Finsler.AffineTime
import OTSelector.Geometry.Finsler.Basic
import OTSelector.Geometry.Finsler.CalibratedCovector
import OTSelector.Geometry.Finsler.CalibratedDistance
import OTSelector.Geometry.Finsler.CalibratedIntervalCovector
import OTSelector.Geometry.Finsler.Energy.Basic
import OTSelector.Geometry.Finsler.Geodesic.Defs
import OTSelector.Geometry.Finsler.Geodesic.SmoothMinimizer
import OTSelector.Geometry.Finsler.Geodesic.Uniqueness
import OTSelector.Geometry.Finsler.LegendreInjectivity
import OTSelector.Geometry.Finsler.LengthMetric

/-!
# Geometry.Finsler.CalibratedPartnerOrientation

* **Conditions:** Actual differentiability of the original potential and a nontrivial calibrated partner on either side.
* **Objects:** A unique oriented complete unit curve whose original energy covector is that potential differential at the base point.
* **Proof detail:** Construct a forward minimizer or translate an incoming one using its true terminal covector, then use Legendre injectivity and ODE uniqueness.

Mathematical sources:
- [Rotem Assouline, Curvature-Dimension for Autonomous Lagrangians, arXiv:2409.08001v6 (10 February 2026)](https://arxiv.org/pdf/2409.08001v6#page=29): Sections 4–4.1, Definition 4.2 and Proposition 4.3, p. 29; Lemma 4.5, pp. 30–31; Definition 4.6 and Lemma 4.8, pp. 31–32.
- [Zhongmin Shen, Landsberg Curvature, S-Curvature and Riemann Curvature, MSRI Publications 50 (2004)](https://library.slmath.org/books/Book50/files/08Sh.pdf#page=6): Section 2, p. 308, Legendre transformation, inverse Legendre transformation and equation (2–12).
- [Gerald Teschl, Ordinary Differential Equations and Dynamical Systems (AMS 2012 author preliminary version)](https://www.mat.univie.ac.at/~gerald/ftp/book-ode/ode.pdf#page=61): Section 2.6, pp. 50–51, overlap uniqueness, equation (2.63), and Theorem 2.13 (unique maximal solution).

Source relation (derived): Derived from the cited geometric/analytic principles with the exact actual source hypotheses. The local construction and its original phase/covector data are retained, rather than asserted as a verbatim source statement.
-/

/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Geometry.FinslerCalibratedPartnerOrientation.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Geometry.FinslerCalibratedPartnerOrientation`; the selected original proof blocks follow. -/
section

/-!
# The canonical oriented curve from either side of a calibrated point

At a differentiability point of an original one-Lipschitz potential, either a
nontrivial forward or backward calibrated partner constructs a complete smooth
unit curve whose original energy covector is the actual potential differential.
An incoming minimizer is translated in time, using its true right-endpoint
covector. Actual Legendre injectivity makes the resulting whole curve unique.
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

omit [PreconnectedSpace M] in
/-- The same original scalar covector at a common start identifies the complete
intrinsic Euler--Lagrange curves; no regularity of the scalar function is required. -/
theorem eq_of_complete_initial_fiberEnergy_covector (hF : F.IsSmoothStronglyConvex)
    {c d : ℝ → M} (hc : F.IsEulerLagrangeOn c univ) (hd : F.IsEulerLagrangeOn d univ)
    {x : M} (hc0 : c 0 = x) (hd0 : d 0 = x)
    (hvc : mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) c 0 1 ≠ 0)
    (hvd : mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) d 0 1 ≠ 0) {u : M → ℝ}
    (hcP : mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) u (c 0) =
      fderiv ℝ (F.fiberEnergy (c 0)) (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) c 0 1))
    (hdP : mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) u (d 0) =
      fderiv ℝ (F.fiberEnergy (d 0)) (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) d 0 1)) : c = d := by
  let instCanonicalCurveFiberNorm : NormedAddCommGroup (TangentSpace 𝓘(ℝ, E) x) :=
    inferInstanceAs (NormedAddCommGroup E)
  let instCanonicalCurveFiberSpace : NormedSpace ℝ (TangentSpace 𝓘(ℝ, E) x) :=
    inferInstanceAs (NormedSpace ℝ E)
  have hcp : fderiv ℝ (F.fiberEnergyModel x) (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) c 0 1) =
      mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) u x := by
    change fderiv ℝ (F.fiberEnergy x) _ = _
    rw [← hc0]
    exact hcP.symm
  have hdp : fderiv ℝ (F.fiberEnergyModel x) (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) d 0 1) =
      mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) u x := by
    change fderiv ℝ (F.fiberEnergy x) _ = _
    rw [← hd0]
    exact hdP.symm
  have hvel := hF.injOn_fiberEnergy_legendre x hvc hvd (hcp.trans hdp.symm)
  have htan : tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) c ⟨0, (1 : ℝ)⟩ =
      tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) d ⟨0, (1 : ℝ)⟩ :=
    TotalSpace.ext (hc0.trans hd0.symm) (heq_of_eq hvel)
  funext t
  exact hF.eqOn_of_isEulerLagrangeOn isOpen_univ isPreconnected_univ hc hd
    (mem_univ 0) htan (mem_univ t)

private theorem exists_oriented_curve_of_calibrated_partner
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    {u : M → ℝ} (hu : let _instOrientedPartnerExistLip : MetricSpace M := F.metricSpace
      LipschitzWith 1 u)
    {x y : M} (hxy : x ≠ y)
    (hsat : let _instOrientedPartnerExistSat : MetricSpace M := F.metricSpace
      u y - u x = dist x y ∨ u x - u y = dist x y)
    (hdu : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ) u x) :
    ∃ g : ℝ → M, g 0 = x ∧ F.IsEulerLagrangeOn g univ ∧
      ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞ g ∧
      (∀ t : ℝ, F.toFun (tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) g ⟨t, (1 : ℝ)⟩) = 1) ∧
      mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) u (g 0) =
        fderiv ℝ (F.fiberEnergy (g 0)) (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) g 0 1) := by
  let _instOrientedPartnerExistMetric : MetricSpace M := F.metricSpace
  let _instOrientedPartnerExistENorm :
      ∀ z : M, ENorm (TangentSpace 𝓘(ℝ, E) z) := F.enorm
  rcases hsat with hforward | hbackward
  · obtain ⟨g, ⟨hg0, hgy, hgEL, hgsm, hgs, hgi, _⟩, _⟩ :=
      hF.existsUnique_complete_calibrated_minimizer hcomplete hu hxy hforward hdu
    refine ⟨g, hg0, hgEL, hgsm, hgs, ?_⟩
    apply hF.mfderiv_eq_fiberEnergy_of_calibrated_interval hu (dist_pos.mpr hxy) hgi
    · simpa only [hgy, hg0, sub_zero] using hforward
    · exact hgsm.mdifferentiable (by simp) 0
    · exact hgs 0
    · rwa [hg0]
  · obtain ⟨c, hc0, hcx, hcEL, hcsm, hcs, hci, _⟩ :=
      hF.exists_smooth_lengthMetric_minimizer hcomplete hxy.symm
    let d := dist y x
    let g : ℝ → M := fun t ↦ c (t + d)
    have hg0 : g 0 = x := by simpa only [g, zero_add] using hcx
    have htime : ContDiff ℝ ∞ (fun t : ℝ ↦ t + d) := contDiff_id.add contDiff_const
    have hgsm : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞ g := hcsm.comp htime.contMDiff
    have hgEL : F.IsEulerLagrangeOn g univ := by
      simpa only [one_mul, sub_neg_eq_add, preimage_univ, Function.comp_def] using
        hF.isEulerLagrangeOn_affine hcEL (a := -d) (by norm_num : (0 : ℝ) < 1)
    have hgs : ∀ t : ℝ,
        F.toFun (tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) g ⟨t, (1 : ℝ)⟩) = 1 := by
      intro t
      have hspeed := F.speed_affine (a := -d) (s := 1) (t := t) (by norm_num)
        (hcsm.mdifferentiable (by simp) (1 * (t - -d)))
      have hreal : (F.toFun (tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) g ⟨t, (1 : ℝ)⟩) : ℝ) = 1 := by
        simpa only [g, one_mul, sub_neg_eq_add, Function.comp_def, hcs, NNReal.coe_one]
          using hspeed
      exact_mod_cast hreal
    have hdc : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ) u (c d) := by
      change MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ) u (c (dist y x))
      rwa [hcx]
    have hcov : mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) u (c d) =
        fderiv ℝ (F.fiberEnergy (c d)) (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) c d 1) := by
      apply hF.mfderiv_eq_fiberEnergy_of_calibrated_closedInterval hu
        (dist_pos.mpr hxy.symm) hci
      · rw [hcx, hc0, sub_zero, dist_comm]
        exact hbackward
      · exact right_mem_Icc.mpr dist_nonneg
      · exact hcsm.mdifferentiable (by simp) d
      · exact hcs d
      · exact hdc
    have hv : mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) g 0 1 =
        mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) c d 1 := by
      have hchain := mfderiv_comp_apply (I := 𝓘(ℝ, ℝ)) (I' := 𝓘(ℝ, ℝ))
        (I'' := 𝓘(ℝ, E)) (0 : ℝ)
        (hcsm.mdifferentiable (by simp) (0 + d))
        (htime.differentiable (by simp) 0).mdifferentiableAt (1 : ℝ)
      have ht : mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun t : ℝ ↦ t + d) 0 1 = 1 := by
        rw [mfderiv_eq_fderiv]
        exact (fderiv_apply_one_eq_deriv (𝕜 := ℝ)).trans
          (((hasDerivAt_id 0).add_const d).deriv)
      rw [ht, zero_add] at hchain
      exact hchain
    refine ⟨g, hg0, hgEL, hgsm, hgs, ?_⟩
    change mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) u (c (0 + d)) =
      fderiv ℝ (F.fiberEnergy (c (0 + d))) (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) g 0 1)
    rw [zero_add, hv]
    exact hcov

/-- A nontrivial calibrated partner on either side determines the unique complete
smooth unit curve whose original energy covector is the actual potential differential
at the initial point. The orientation is therefore independent of the chosen partner. -/
theorem existsUnique_oriented_curve_of_calibrated_partner (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    {u : M → ℝ} (hu : let _instOrientedPartnerUniqueLip : MetricSpace M := F.metricSpace
      LipschitzWith 1 u)
    {x y : M} (hxy : x ≠ y)
    (hsat : let _instOrientedPartnerUniqueSat : MetricSpace M := F.metricSpace
      u y - u x = dist x y ∨ u x - u y = dist x y)
    (hdu : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ) u x) :
    ∃! g : ℝ → M, g 0 = x ∧ F.IsEulerLagrangeOn g univ ∧
      ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞ g ∧
      (∀ t : ℝ, F.toFun (tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) g ⟨t, (1 : ℝ)⟩) = 1) ∧
      mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) u (g 0) =
        fderiv ℝ (F.fiberEnergy (g 0)) (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) g 0 1) := by
  obtain ⟨g, hg0, hgEL, hgsm, hgs, hgP⟩ :=
    hF.exists_oriented_curve_of_calibrated_partner hcomplete hu hxy hsat hdu
  have hn (c : ℝ → M)
      (hc : F.toFun (tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) c ⟨0, (1 : ℝ)⟩) = 1) :
      mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) c 0 1 ≠ 0 := by
    intro hz
    change F.toFun ⟨c 0, mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) c 0 1⟩ = 1 at hc
    rw [hz, F.map_zero] at hc
    exact zero_ne_one hc
  refine ⟨g, ⟨hg0, hgEL, hgsm, hgs, hgP⟩, ?_⟩
  rintro k ⟨hk0, hkEL, _, hks, hkP⟩
  exact hF.eq_of_complete_initial_fiberEnergy_covector hkEL hgEL hk0 hg0
    (hn k (hks 0)) (hn g (hgs 0)) hkP hgP

end OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

end
end
