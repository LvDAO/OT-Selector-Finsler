import OTSelector.Geometry.Finsler.Basic
import OTSelector.Geometry.Finsler.CalibratedVelocity
import OTSelector.Geometry.Finsler.Energy.Basic
import OTSelector.Geometry.Finsler.Geodesic.Basic
import OTSelector.Geometry.Finsler.Geodesic.Defs
import OTSelector.Geometry.Finsler.Geodesic.SmoothMinimizer
import OTSelector.Geometry.Finsler.Geodesic.Uniqueness
import OTSelector.Geometry.Finsler.LengthMetric
import OTSelector.Geometry.Finsler.LipschitzDifferential
import OTSelector.Topology.MetricSpace.SaturatedCalibration

/-!
# Geometry.Finsler.CalibratedMinimizerUnique

* **Conditions:** Actual unit minimizing/calibrated curves have a common initial point and a global Lipschitz potential differentiable there.
* **Objects:** Equal initial tangents and uniqueness of the whole complete curves, or equality on the original isometric interval.
* **Proof detail:** Differentiate saturation at the initial point, identify unit velocities by the same supporting covector and apply intrinsic ODE uniqueness.

Mathematical sources:
- [Rotem Assouline, Curvature-Dimension for Autonomous Lagrangians, arXiv:2409.08001v6 (10 February 2026)](https://arxiv.org/pdf/2409.08001v6#page=29): Sections 4–4.1, Definition 4.2 and Proposition 4.3, p. 29; Lemma 4.5, pp. 30–31; Definition 4.6 and Lemma 4.8, pp. 31–32.
- [Zhongmin Shen, Landsberg Curvature, S-Curvature and Riemann Curvature, MSRI Publications 50 (2004)](https://library.slmath.org/books/Book50/files/08Sh.pdf#page=6): Section 2, p. 308, Legendre transformation, inverse Legendre transformation and equation (2–12).
- [Gerald Teschl, Ordinary Differential Equations and Dynamical Systems (AMS 2012 author preliminary version)](https://www.mat.univie.ac.at/~gerald/ftp/book-ode/ode.pdf#page=61): Section 2.6, pp. 50–51, overlap uniqueness, equation (2.63), and Theorem 2.13 (unique maximal solution).

Source relation (derived): The stated result is a derived local construction from the cited principles. The exact original family, branch, coordinate maps and hypotheses remain those in the full source telescope.
-/

/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Geometry.FinslerCalibratedMinimizerUnique.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Geometry.FinslerCalibratedMinimizerUnique`; the selected original proof blocks follow. -/
section

/-!
# Uniqueness of globally calibrated Finsler minimizing segments

A potential Lipschitz for the original distance and differentiable at the common initial
point saturates both actual unit initial velocities. Original strong convexity makes
those velocities equal; intrinsic Euler--Lagrange uniqueness identifies the same entire
curves. Smoothness of the potential away from the initial point is unnecessary.
-/

open Set Filter Metric Manifold Bundle
open scoped Topology ContDiff NNReal

noncomputable section
namespace OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [PreconnectedSpace M]
  {F : ContinuousFinslerNorm E M}

set_option backward.isDefEq.respectTransparency false in
/-- A globally saturated isometric interval has initial velocity calibrated by the
actual differential of the potential, requiring differentiability only at its start. -/
theorem mfderiv_initial_eq_one_of_calibrated_interval (_hF : F.IsSmoothStronglyConvex)
    {u : M → ℝ} (hu : letI : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    {c : ℝ → M} {a b : ℝ} (hab : a < b)
    (hiso : letI : MetricSpace M := F.metricSpace;
      Isometry (fun t : Icc a b ↦ c t))
    (hsat : u (c b) - u (c a) = b - a)
    (hc : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) c a)
    (hd : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ) u (c a)) :
    mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) u (c a)
      (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) c a 1) = (1 : ℝ) := by
  let : MetricSpace M := F.metricSpace
  have hg : DifferentiableAt ℝ (u ∘ c) a :=
    mdifferentiableAt_iff_differentiableAt.mp (hd.comp a hc)
  have he : deriv (u ∘ c) a = mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) u (c a)
      (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) c a 1) := by
    have h := mfderiv_comp_apply a hd hc (1 : ℝ)
    rw [mfderiv_eq_fderiv] at h
    exact h
  exact he.symm.trans
    (deriv_comp_eq_one_of_lipschitz_saturated_isometry hu hab hiso hsat hg.hasDerivAt)

set_option backward.isDefEq.respectTransparency false in
/-- Original calibrated unit minimizing intervals with the same start have the same
actual initial tangent, even if their later endpoints differ. -/
theorem tangentMap_eq_of_calibrated_intervals (hF : F.IsSmoothStronglyConvex)
    {u : M → ℝ} (hu : letI : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    {c d : ℝ → M} {a b : ℝ} (hab : a < b)
    (hc : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) c a)
    (hd : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) d a)
    (hstart : c a = d a)
    (hcs : F.toFun (tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) c ⟨a, (1 : ℝ)⟩) = 1)
    (hds : F.toFun (tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) d ⟨a, (1 : ℝ)⟩) = 1)
    (hciso : letI : MetricSpace M := F.metricSpace;
      Isometry (fun t : Icc a b ↦ c t))
    (hdiso : letI : MetricSpace M := F.metricSpace;
      Isometry (fun t : Icc a b ↦ d t))
    (hcsat : u (c b) - u (c a) = b - a)
    (hdsat : u (d b) - u (d a) = b - a)
    (hdu : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ) u (c a)) :
    tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) c ⟨a, (1 : ℝ)⟩ =
      tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) d ⟨a, (1 : ℝ)⟩ := by
  let p : TangentSpace 𝓘(ℝ, E) (c a) →L[ℝ] ℝ := mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) u (c a)
  let v := mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) c a 1
  let w := mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) d a 1
  have hdu' : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ) u (d a) := by rwa [← hstart]
  have hw : F.toFun ⟨c a, w⟩ = 1 := by
    rw [hstart]
    exact hds
  have hb : ∀ z : TangentSpace 𝓘(ℝ, E) (c a), p z ≤ (F.toFun ⟨c a, z⟩ : ℝ) := by
    intro z
    have h := hF.abs_mfderiv_le_finsler_of_lipschitz hu hdu z
    exact (le_abs_self (p z)).trans (by simpa only [p, NNReal.coe_one, one_mul] using! h)
  have hpv : p v = 1 :=
    hF.mfderiv_initial_eq_one_of_calibrated_interval hu hab hciso hcsat hc hdu
  have hpw : p w = 1 := by
    have h := hF.mfderiv_initial_eq_one_of_calibrated_interval hu hab hdiso hdsat hd hdu'
    change mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) u (c a)
      (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) d a 1) = (1 : ℝ)
    rw [hstart]
    exact h
  have hvel := hF.tangent_unit_velocity_eq_of_calibration (c a) p hcs hw hb hpv hpw
  apply TotalSpace.ext hstart
  exact heq_of_eq hvel.symm

/-- Two actual complete unit Euler--Lagrange curves calibrated on a nondegenerate
initial interval coincide if they start at the same differentiability point of u. -/
theorem eq_of_complete_calibrated_intervals (hF : F.IsSmoothStronglyConvex)
    {u : M → ℝ} (hu : letI : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    {c d : ℝ → M} {a b : ℝ} (hab : a < b)
    (hc : F.IsEulerLagrangeOn c univ) (hd : F.IsEulerLagrangeOn d univ)
    (hstart : c a = d a)
    (hcs : F.toFun (tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) c ⟨a, (1 : ℝ)⟩) = 1)
    (hds : F.toFun (tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) d ⟨a, (1 : ℝ)⟩) = 1)
    (hciso : letI : MetricSpace M := F.metricSpace;
      Isometry (fun t : Icc a b ↦ c t))
    (hdiso : letI : MetricSpace M := F.metricSpace;
      Isometry (fun t : Icc a b ↦ d t))
    (hcsat : u (c b) - u (c a) = b - a)
    (hdsat : u (d b) - u (d a) = b - a)
    (hdu : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ) u (c a)) : c = d := by
  have hct := (hF.contMDiffAt_of_isEulerLagrangeAt (hc a (mem_univ _))).mdifferentiableAt
    (by simp)
  have hdt := (hF.contMDiffAt_of_isEulerLagrangeAt (hd a (mem_univ _))).mdifferentiableAt
    (by simp)
  have hv := hF.tangentMap_eq_of_calibrated_intervals hu hab hct hdt hstart hcs hds
    hciso hdiso hcsat hdsat hdu
  funext t
  exact hF.eqOn_of_isEulerLagrangeOn isOpen_univ isPreconnected_univ hc hd
    (mem_univ a) hv (mem_univ t)

/-- Two arbitrary original-distance minimizing intervals with the same start and a
saturated Lipschitz calibration coincide on their whole interval. The potential need
only be differentiable at the start; smoothness of the minimizing curves is derived. -/
theorem eqOn_of_calibrated_isometric_intervals (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    {u : M → ℝ} (hu : letI : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    {c d : ℝ → M} {a b : ℝ} (hab : a < b)
    (hciso : letI : MetricSpace M := F.metricSpace;
      Isometry (fun t : Icc a b ↦ c t))
    (hdiso : letI : MetricSpace M := F.metricSpace;
      Isometry (fun t : Icc a b ↦ d t))
    (hstart : c a = d a)
    (hcsat : u (c b) - u (c a) = b - a)
    (hdsat : u (d b) - u (d a) = b - a)
    (hdu : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ) u (c a)) : EqOn c d (Icc a b) := by
  obtain ⟨g, hgEL, _, hgs, hgc⟩ :=
    hF.exists_complete_extension_of_isometric_interval hcomplete hab hciso
  obtain ⟨k, hkEL, _, hks, hkd⟩ :=
    hF.exists_complete_extension_of_isometric_interval hcomplete hab hdiso
  have ha : a ∈ Icc a b := left_mem_Icc.mpr hab.le
  have hb : b ∈ Icc a b := right_mem_Icc.mpr hab.le
  have hgi : letI : MetricSpace M := F.metricSpace;
      Isometry (fun t : Icc a b ↦ g t) := by
    let : MetricSpace M := F.metricSpace
    intro s t
    change edist (g s) (g t) = edist s t
    rw [hgc s.property, hgc t.property]
    exact hciso.edist_eq s t
  have hki : letI : MetricSpace M := F.metricSpace;
      Isometry (fun t : Icc a b ↦ k t) := by
    let : MetricSpace M := F.metricSpace
    intro s t
    change edist (k s) (k t) = edist s t
    rw [hkd s.property, hkd t.property]
    exact hdiso.edist_eq s t
  have hstart' : g a = k a := (hgc ha).trans (hstart.trans (hkd ha).symm)
  have hgsat : u (g b) - u (g a) = b - a := by rwa [hgc ha, hgc hb]
  have hksat : u (k b) - u (k a) = b - a := by rwa [hkd ha, hkd hb]
  have hdu' : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ) u (g a) := by rwa [hgc ha]
  have heq := hF.eq_of_complete_calibrated_intervals hu hab hgEL hkEL hstart'
    (hgs a) (hks a) hgi hki hgsat hksat hdu'
  intro t ht
  exact (hgc ht).symm.trans ((congrFun heq t).trans (hkd ht))

/-- A globally calibrated pair of distinct endpoints has a unique original-distance
isometric minimizing interval whenever the potential is differentiable at its start. -/
theorem eqOn_isometric_intervals_of_calibrated_endpoints (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    {u : M → ℝ} (hu : letI : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    {c d : ℝ → M} {a b : ℝ} (hab : a < b)
    (hciso : letI : MetricSpace M := F.metricSpace;
      Isometry (fun t : Icc a b ↦ c t))
    (hdiso : letI : MetricSpace M := F.metricSpace;
      Isometry (fun t : Icc a b ↦ d t))
    (hstart : c a = d a) (hend : c b = d b)
    (hsat : u (c b) - u (c a) = b - a)
    (hdu : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ) u (c a)) : EqOn c d (Icc a b) := by
  apply hF.eqOn_of_calibrated_isometric_intervals hcomplete hu hab hciso hdiso hstart hsat
  · rwa [← hstart, ← hend]
  · exact hdu

end OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

end
end
