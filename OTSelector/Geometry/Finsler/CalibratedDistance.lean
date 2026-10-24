import OTSelector.Geometry.Finsler.Basic
import OTSelector.Geometry.Finsler.CalibratedMinimizerUnique
import OTSelector.Geometry.Finsler.Energy.Basic
import OTSelector.Geometry.Finsler.Geodesic.Basic
import OTSelector.Geometry.Finsler.Geodesic.Defs
import OTSelector.Geometry.Finsler.Geodesic.Proofs.Continuation
import OTSelector.Geometry.Finsler.Geodesic.SmoothMinimizer
import OTSelector.Geometry.Finsler.LengthMetric

/-!
# Geometry.Finsler.CalibratedDistance

* **Conditions:** A C1 unit-speed curve with actual affine potential clock; completeness and initial potential differentiability for the constructed unique minimizer.
* **Objects:** Original-distance interval isometry and the unique complete unit Euler–Lagrange extension of a calibrated minimizing segment.
* **Proof detail:** Squeeze distance by potential change and actual length, use metric minimizing existence and apply calibrated initial-velocity uniqueness.

Mathematical sources:
- [Zhongmin Shen, Landsberg Curvature, S-Curvature and Riemann Curvature, in Riemann–Finsler Geometry, MSRI Publications 50 (2004)](https://library.slmath.org/books/Book50/files/08Sh.pdf#page=11): Section 4, p. 313: the length integral, induced distance and minimizing curves.
- [Anton Petrunin, Lectures on metric geometry](https://anton-petrunin.github.io/metric-geometry/tex/lectures.pdf#page=18): Lecture 1, Section L, Theorem 1.30 (Hopf–Rinow), Exercise 1.31 and proof, pp. 18–19.
- [Rotem Assouline, Curvature-Dimension for Autonomous Lagrangians, arXiv:2409.08001v6 (10 February 2026)](https://arxiv.org/pdf/2409.08001v6#page=29): Sections 4–4.1, Definition 4.2 and Proposition 4.3, p. 29; Lemma 4.5, pp. 30–31; Definition 4.6 and Lemma 4.8, pp. 31–32.

Source relation (derived): Uniqueness concerns this parameterized unit segment and its complete dynamics; longer complete segments are not asserted minimizing.
-/

/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Geometry.FinslerCalibratedDistance.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Geometry.FinslerCalibratedDistance`; the selected original proof blocks follow. -/
section

/-!
# Original distance realized by calibrated Finsler curves

A C1 curve of actual unit Finsler speed is an original-distance isometry on any interval
where a global one-Lipschitz potential grows at unit rate. Completeness supplies a smooth
original-length minimizer between distinct calibrated endpoints; differentiability of the
potential only at the initial point makes its complete unit Euler--Lagrange extension unique.

All metrics and lengths are those of the given Finsler norm. Uniqueness concerns complete
unit Euler--Lagrange curves with the stated minimizing segment, not arbitrary parametrizations
or global minimization on longer intervals.
-/

open Set Filter Metric Manifold Bundle
open scoped Topology ContDiff ENNReal NNReal

noncomputable section
namespace OTSelector.Geometry.ContinuousFinslerNorm

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [PreconnectedSpace M]

/-- Actual unit speed and a global metric calibration make a C1 curve an isometry
for the original length distance. Smoothness or differentiability of u is unnecessary. -/
theorem isometry_Icc_of_unitSpeed_calibration (F : ContinuousFinslerNorm E M)
    {u : M → ℝ} (hu : letI : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    {c : ℝ → M} {a b C : ℝ}
    (hc : ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, E) 1 c (Icc a b))
    (hspeed : ∀ t ∈ Ioo a b,
      F.toFun (tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) c ⟨t, (1 : ℝ)⟩) = 1)
    (hsat : ∀ t ∈ Icc a b, u (c t) = t + C) :
    letI : MetricSpace M := F.metricSpace
    Isometry (fun t : Icc a b ↦ c t) := by
  let : MetricSpace M := F.metricSpace
  let : ∀ x : M, ENorm (TangentSpace 𝓘(ℝ, E) x) := F.enorm
  let : ∀ x : M, ENormSMulClass ℝ (TangentSpace 𝓘(ℝ, E) x) := F.enormSMulClass
  have hupper (s : ℝ) (hs : s ∈ Icc a b) (t : ℝ) (ht : t ∈ Icc a b)
      (hst : s ≤ t) : edist (c s) (c t) ≤ edist s t := by
    have hsegment : Icc s t ⊆ Icc a b := Icc_subset_Icc hs.1 ht.2
    calc
      edist (c s) (c t) ≤ Manifold.pathELength 𝓘(ℝ, E) c s t :=
        Manifold.riemannianEDist_le_pathELength (hc.mono hsegment) rfl rfl hst
      _ ≤ (1 : ℝ≥0∞) * ENNReal.ofReal (t - s) :=
        F.pathELength_le_of_speed_le (C := 1) (fun r hr ↦
          (hspeed r ⟨hs.1.trans_lt hr.1, hr.2.trans_le ht.2⟩).le)
      _ = edist s t := by
        rw [one_mul, edist_dist, Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hst), neg_sub]
  intro s t
  apply le_antisymm
  · change edist (c s) (c t) ≤ edist (s : ℝ) (t : ℝ)
    rcases le_total (s : ℝ) (t : ℝ) with hst | hts
    · exact hupper s s.property t t.property hst
    · rw [edist_comm (c s) (c t), edist_comm (s : ℝ) (t : ℝ)]
      exact hupper t t.property s s.property hts
  · have h := hu (c s) (c t)
    simpa only [hsat s s.property, hsat t t.property, edist_add_right,
      NNReal.coe_one, ENNReal.coe_one, one_mul, Subtype.edist_eq] using h

namespace IsSmoothStronglyConvex

variable {F : ContinuousFinslerNorm E M}

/-- A calibrated pair of distinct endpoints has exactly one complete smooth unit
Euler--Lagrange curve realizing the original distance on the prescribed closed segment. -/
theorem existsUnique_complete_calibrated_minimizer (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    {u : M → ℝ} (hu : letI : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    {x y : M} (hxy : x ≠ y)
    (hsat : letI : MetricSpace M := F.metricSpace; u y - u x = dist x y)
    (hdu : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ) u x) :
    letI : MetricSpace M := F.metricSpace
    letI : ∀ z : M, ENorm (TangentSpace 𝓘(ℝ, E) z) := F.enorm
    ∃! g : ℝ → M, g 0 = x ∧ g (dist x y) = y ∧
      F.IsEulerLagrangeOn g univ ∧ ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞ g ∧
      (∀ t : ℝ, F.toFun (tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) g ⟨t, (1 : ℝ)⟩) = 1) ∧
      Isometry (fun t : Icc (0 : ℝ) (dist x y) ↦ g t) ∧
      ∀ s ∈ Icc (0 : ℝ) (dist x y), ∀ t ∈ Icc (0 : ℝ) (dist x y), s ≤ t →
        F.lengthEDist (g s) (g t) = Manifold.pathELength 𝓘(ℝ, E) g s t := by
  let : MetricSpace M := F.metricSpace
  let : ∀ z : M, ENorm (TangentSpace 𝓘(ℝ, E) z) := F.enorm
  obtain ⟨g, hg0, hgy, hgEL, hgsmooth, hgspeed, hgiso, hgmin⟩ :=
    hF.exists_smooth_lengthMetric_minimizer hcomplete hxy
  refine ⟨g, ⟨hg0, hgy, hgEL, hgsmooth, hgspeed, hgiso, hgmin⟩, ?_⟩
  rintro k ⟨hk0, hky, hkEL, _, hkspeed, hkiso, _⟩
  apply hF.eq_of_complete_calibrated_intervals hu (dist_pos.mpr hxy) hkEL hgEL
    (hk0.trans hg0.symm) (hkspeed 0) (hgspeed 0) hkiso hgiso
  · simpa only [hky, hk0, sub_zero] using hsat
  · simpa only [hgy, hg0, sub_zero] using hsat
  · rwa [hk0]

/-- Two complete actual unit Euler--Lagrange curves calibrated at unit rate on a
nondegenerate interval are identical when they start at the same differentiability point.
Their original-distance isometry is derived from actual speed and calibration. -/
theorem eq_of_complete_unitSpeed_calibrated_curves (hF : F.IsSmoothStronglyConvex)
    {u : M → ℝ} (hu : letI : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    {c d : ℝ → M} {a b C D : ℝ} (hab : a < b)
    (hc : F.IsEulerLagrangeOn c univ) (hd : F.IsEulerLagrangeOn d univ)
    (hstart : c a = d a)
    (hcs : ∀ t : ℝ, F.toFun (tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) c ⟨t, (1 : ℝ)⟩) = 1)
    (hds : ∀ t : ℝ, F.toFun (tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) d ⟨t, (1 : ℝ)⟩) = 1)
    (hca : ∀ t ∈ Icc a b, u (c t) = t + C)
    (hda : ∀ t ∈ Icc a b, u (d t) = t + D)
    (hdu : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ) u (c a)) : c = d := by
  have hcc : ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, E) 1 c (Icc a b) :=
    ((hF.contMDiffOn_of_isEulerLagrangeOn hc).mono (subset_univ _)).of_le (by simp)
  have hdc : ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, E) 1 d (Icc a b) :=
    ((hF.contMDiffOn_of_isEulerLagrangeOn hd).mono (subset_univ _)).of_le (by simp)
  apply hF.eq_of_complete_calibrated_intervals hu hab hc hd hstart (hcs a) (hds a)
    (F.isometry_Icc_of_unitSpeed_calibration hu hcc (fun t _ ↦ hcs t) hca)
    (F.isometry_Icc_of_unitSpeed_calibration hu hdc (fun t _ ↦ hds t) hda)
  · rw [hca b (right_mem_Icc.mpr hab.le), hca a (left_mem_Icc.mpr hab.le)]
    ring
  · rw [hda b (right_mem_Icc.mpr hab.le), hda a (left_mem_Icc.mpr hab.le)]
    ring
  · exact hdu

end IsSmoothStronglyConvex
end OTSelector.Geometry.ContinuousFinslerNorm

end
end
