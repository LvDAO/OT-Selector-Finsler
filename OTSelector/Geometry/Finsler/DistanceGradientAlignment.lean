import OTSelector.Geometry.Finsler.Basic
import OTSelector.Geometry.Finsler.CalibratedMinimizerUnique
import OTSelector.Geometry.Finsler.CalibratedVelocity
import OTSelector.Geometry.Finsler.Energy.Basic
import OTSelector.Geometry.Finsler.Geodesic.Basic
import OTSelector.Geometry.Finsler.Geodesic.Defs
import OTSelector.Geometry.Finsler.Geodesic.SmoothMinimizer
import OTSelector.Geometry.Finsler.Geodesic.Uniqueness
import OTSelector.Geometry.Finsler.LengthMetric
import OTSelector.Geometry.Finsler.LipschitzDifferential

/-!
# Geometry.Finsler.DistanceGradientAlignment

* **Conditions:** Two actual differentiable original-distance calibrations with the same initial differential, or equal negative-distance differentials toward two distinct targets.
* **Objects:** Equality of their whole complete unit geodesics and one complete minimizing curve reaching both targets.
* **Proof detail:** The common covector selects the same unit tangent by original Legendre injectivity; intrinsic initial-value uniqueness identifies the curves.

Mathematical sources:
- [Rotem Assouline, Curvature-Dimension for Autonomous Lagrangians, arXiv:2409.08001v6 (10 February 2026)](https://arxiv.org/pdf/2409.08001v6#page=29): Sections 4–4.1, Definition 4.2 and Proposition 4.3, p. 29; Lemma 4.5, pp. 30–31; Definition 4.6 and Lemma 4.8, pp. 31–32.
- [Zhongmin Shen, Landsberg Curvature, S-Curvature and Riemann Curvature, MSRI Publications 50 (2004)](https://library.slmath.org/books/Book50/files/08Sh.pdf#page=6): Section 2, p. 308, Legendre transformation, inverse Legendre transformation and equation (2–12).
- [Gerald Teschl, Ordinary Differential Equations and Dynamical Systems (AMS 2012 author preliminary version)](https://www.mat.univie.ac.at/~gerald/ftp/book-ode/ode.pdf#page=61): Section 2.6, pp. 50–51, overlap uniqueness, equation (2.63), and Theorem 2.13 (unique maximal solution).

Source relation (derived): The stated result is a derived local construction from the cited principles. The exact original family, branch, coordinate maps and hypotheses remain those in the full source telescope.
-/

/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Geometry.FinslerDistanceGradientAlignment.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Geometry.FinslerDistanceGradientAlignment`; the selected original proof blocks follow. -/
section

/-!
# Equal original distance differentials select the same complete geodesic

Two differentiable original-distance calibrations with the same actual differential
select the same initial unit tangent. Intrinsic Euler--Lagrange uniqueness then
identifies their entire complete curves. Applying this to negative distances gives
one actual unit minimizing geodesic through the initial point and both targets.
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

/-- Equal actual initial differentials of two metric calibrations identify complete
unit minimizing curves, even when their calibrated time intervals have different lengths. -/
theorem eq_of_complete_calibrated_initial_differential (hF : F.IsSmoothStronglyConvex)
    {u v : M → ℝ}
    (hu : letI _instAlignULipMetric : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (hv : letI _instAlignVLipMetric : MetricSpace M := F.metricSpace; LipschitzWith 1 v)
    {c d : ℝ → M} {a b e : ℝ} (hab : a < b) (hae : a < e)
    (hc : F.IsEulerLagrangeOn c univ) (hd : F.IsEulerLagrangeOn d univ)
    (hstart : c a = d a)
    (hcs : F.toFun (tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) c ⟨a, (1 : ℝ)⟩) = 1)
    (hds : F.toFun (tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) d ⟨a, (1 : ℝ)⟩) = 1)
    (hciso : letI _instAlignCIsoMetric : MetricSpace M := F.metricSpace
      Isometry (fun t : Icc a b ↦ c t))
    (hdiso : letI _instAlignDIsoMetric : MetricSpace M := F.metricSpace
      Isometry (fun t : Icc a e ↦ d t))
    (hcsat : u (c b) - u (c a) = b - a)
    (hdsat : v (d e) - v (d a) = e - a)
    (hdu : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ) u (c a))
    (hdv : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ) v (c a))
    (heq : mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) u (c a) =
      mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) v (c a)) : c = d := by
  have hct := (hF.contMDiffAt_of_isEulerLagrangeAt (hc a (mem_univ _))).mdifferentiableAt
    (by simp)
  have hdt := (hF.contMDiffAt_of_isEulerLagrangeAt (hd a (mem_univ _))).mdifferentiableAt
    (by simp)
  let p : TangentSpace 𝓘(ℝ, E) (c a) →L[ℝ] ℝ := mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) u (c a)
  let vc := mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) c a 1
  let vd := mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) d a 1
  have hdv' : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ) v (d a) := by rwa [← hstart]
  have hwd : F.toFun ⟨c a, vd⟩ = 1 := by rw [hstart]; exact hds
  have hpc : p vc = 1 :=
    hF.mfderiv_initial_eq_one_of_calibrated_interval hu hab hciso hcsat hct hdu
  have hpd : p vd = 1 := by
    change mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) u (c a) vd = 1
    rw [heq, hstart]
    exact hF.mfderiv_initial_eq_one_of_calibrated_interval hv hae hdiso hdsat hdt hdv'
  have hbound (q : TangentSpace 𝓘(ℝ, E) (c a)) :
      p q ≤ (F.toFun ⟨c a, q⟩ : ℝ) := by
    have hb := hF.abs_mfderiv_le_finsler_of_lipschitz hu hdu q
    exact (le_abs_self (p q)).trans (by simpa only [p, NNReal.coe_one, one_mul] using! hb)
  have hvel := hF.tangent_unit_velocity_eq_of_calibration (c a) p hcs hwd hbound hpc hpd
  have htan : tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) c ⟨a, (1 : ℝ)⟩ =
      tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) d ⟨a, (1 : ℝ)⟩ :=
    TotalSpace.ext hstart (heq_of_eq hvel.symm)
  funext t
  exact hF.eqOn_of_isEulerLagrangeOn isOpen_univ isPreconnected_univ hc hd
    (mem_univ a) htan (mem_univ t)

/-- Two original distance functions differentiable at a common non-target point with
identical differentials have the same complete unit minimizing geodesic from that point.
Both endpoints and both actual metric-isometry intervals are retained. -/
theorem exists_complete_minimizer_of_distance_differential_eq (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    {x y z : M} (hxy : x ≠ y) (hxz : x ≠ z)
    (hdy : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ)
      (fun q ↦ (F.lengthEDist q y).toReal) x)
    (hdz : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ)
      (fun q ↦ (F.lengthEDist q z).toReal) x)
    (heq : mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) (fun q ↦ (F.lengthEDist q y).toReal) x =
      mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) (fun q ↦ (F.lengthEDist q z).toReal) x) :
    letI _instAlignDistanceOutputMetric : MetricSpace M := F.metricSpace
    ∃ g : ℝ → M, g 0 = x ∧ g (dist x y) = y ∧ g (dist x z) = z ∧
      F.IsEulerLagrangeOn g univ ∧ ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞ g ∧
      (∀ t : ℝ, F.toFun (tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) g ⟨t, (1 : ℝ)⟩) = 1) ∧
      Isometry (fun t : Icc (0 : ℝ) (dist x y) ↦ g t) ∧
      Isometry (fun t : Icc (0 : ℝ) (dist x z) ↦ g t) := by
  let _instAlignDistanceProofMetric : MetricSpace M := F.metricSpace
  let _instAlignDistanceProofENorm : ∀ q : M, ENorm (TangentSpace 𝓘(ℝ, E) q) := F.enorm
  have hLy : LipschitzWith 1 (fun q ↦ -dist q y) := (LipschitzWith.dist_left y).neg
  have hLz : LipschitzWith 1 (fun q ↦ -dist q z) := (LipschitzWith.dist_left z).neg
  obtain ⟨c, hc0, hcy, hcEL, hcsm, hcs, hci, _⟩ :=
    hF.exists_smooth_lengthMetric_minimizer hcomplete hxy
  obtain ⟨d, hd0, hdz', hdEL, _, hds, hdi, _⟩ :=
    hF.exists_smooth_lengthMetric_minimizer hcomplete hxz
  have hdu : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ) (fun q ↦ -dist q y) (c 0) := by
    rw [hc0]
    exact hdy.neg
  have hdv : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ) (fun q ↦ -dist q z) (c 0) := by
    rw [hc0]
    exact hdz.neg
  have hneg : mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) (fun q ↦ -dist q y) (c 0) =
      mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) (fun q ↦ -dist q z) (c 0) := by
    rw [hc0]
    change mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) (-(fun q ↦ (F.lengthEDist q y).toReal)) x =
      mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) (-(fun q ↦ (F.lengthEDist q z).toReal)) x
    rw [mfderiv_neg, mfderiv_neg, heq]
  have hcd : c = d := hF.eq_of_complete_calibrated_initial_differential hLy hLz
    (dist_pos.mpr hxy) (dist_pos.mpr hxz) hcEL hdEL (hc0.trans hd0.symm)
    (hcs 0) (hds 0) hci hdi
    (by simp only [hcy, hc0, dist_self, neg_zero, zero_sub, neg_neg, sub_zero])
    (by simp only [hdz', hd0, dist_self, neg_zero, zero_sub, neg_neg, sub_zero]) hdu hdv hneg
  exact ⟨c, hc0, hcy, by rw [hcd]; exact hdz', hcEL, hcsm, hcs, hci, by rwa [hcd]⟩

end OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

end
end
