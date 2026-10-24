import OTSelector.Geometry.Finsler.AffineTime
import OTSelector.Geometry.Finsler.Basic
import OTSelector.Geometry.Finsler.CalibratedMinimizerUnique
import OTSelector.Geometry.Finsler.DistanceGradientAlignment
import OTSelector.Geometry.Finsler.Energy.Basic
import OTSelector.Geometry.Finsler.Geodesic.Defs
import OTSelector.Geometry.Finsler.Geodesic.SmoothMinimizer
import OTSelector.Geometry.Finsler.Geodesic.Uniqueness
import OTSelector.Geometry.Finsler.LengthMetric
import OTSelector.Topology.MetricSpace.IsometricSplice

/-!
# Geometry.Finsler.DistanceGradientLine

* **Conditions:** Two distinct targets in complete smooth strongly convex Finsler geometry and equality of their actual differentiable distance covectors at tested points.
* **Objects:** The alignment set contained in at most two fixed complete geodesic images, one for each endpoint order.
* **Proof detail:** Splice a competing calibrated minimizing segment into a fixed base minimizer, identify initial tangent by calibration and propagate equality by ODE uniqueness.

Mathematical sources:
- [Zhongmin Shen, Landsberg Curvature, S-Curvature and Riemann Curvature, MSRI Publications 50 (2004)](https://library.slmath.org/books/Book50/files/08Sh.pdf#page=11): Section 4, Definition 4.1 and Lemma 4.2, pp. 313–314; equations (4–1), (4–2) and the canonical-lift spray interpretation.
- [Zhongmin Shen, Landsberg Curvature, S-Curvature and Riemann Curvature, MSRI Publications 50 (2004)](https://library.slmath.org/books/Book50/files/08Sh.pdf#page=6): Section 2, p. 308, Legendre transformation, inverse Legendre transformation and equation (2–12).
- [Gerald Teschl, Ordinary Differential Equations and Dynamical Systems (AMS 2012 author preliminary version)](https://www.mat.univie.ac.at/~gerald/ftp/book-ode/ode.pdf#page=61): Section 2.6, pp. 50–51, overlap uniqueness, equation (2.63), and Theorem 2.13 (unique maximal solution).

Source relation (derived): A project geometric containment lemma derived from actual minimizing/calibrated uniqueness; no generic book theorem is claimed with this exact two-curve conclusion.
-/

/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Geometry.FinslerDistanceGradientLine.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Geometry.FinslerDistanceGradientLine`; the selected original proof blocks follow. -/
section

/-!
# At most two complete geodesics contain equal-distance-differential points

For fixed distinct targets, each of the two possible endpoint orders determines at
most one complete geodesic image containing points with equal actual distance
differentials. A competing minimizing target segment is spliced into a fixed base
minimizer; calibration uniqueness at its initial differentiability point identifies
the segments, and Euler--Lagrange uniqueness propagates equality for all times.
-/

open Set Filter Metric Manifold Bundle
open scoped Topology ContDiff NNReal

noncomputable section
namespace OTSelector.Geometry.ContinuousFinslerNorm

set_option backward.isDefEq.respectTransparency false

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [PreconnectedSpace M]

/-- Non-target points where both original distance functions are differentiable and
have the same actual manifold differential. -/
def distanceDifferentialAlignmentSet (F : ContinuousFinslerNorm E M) (y z : M) : Set M :=
  {x | x ≠ y ∧ x ≠ z ∧
    MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ) (fun q ↦ (F.lengthEDist q y).toReal) x ∧
    MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ) (fun q ↦ (F.lengthEDist q z).toReal) x ∧
    mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) (fun q ↦ (F.lengthEDist q y).toReal) x =
      mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) (fun q ↦ (F.lengthEDist q z).toReal) x}

namespace IsSmoothStronglyConvex
variable {F : ContinuousFinslerNorm E M}

/-- If a minimizing segment admits a minimizing extension past its initial target,
differentiability of the terminal distance at that earlier point identifies every
same-oriented complete minimizing target segment, up to translation of time. -/
theorem range_subset_range_of_isometric_overlap (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    {c d : ℝ → M} {A B C D : ℝ} (hA : 0 < A) (hAB : A < B) (hCD : C < D)
    (hc : F.IsEulerLagrangeOn c univ) (hd : F.IsEulerLagrangeOn d univ)
    (hciso : letI _instLineOverlapCIsoMetric : MetricSpace M := F.metricSpace
      Isometry (fun t : Icc (0 : ℝ) B ↦ c t))
    (hdiso : letI _instLineOverlapDIsoMetric : MetricSpace M := F.metricSpace
      Isometry (fun t : Icc C D ↦ d t))
    (hleft : c A = d C) (hright : c B = d D)
    (hdu : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ)
      (fun q ↦ (F.lengthEDist q (c B)).toReal) (c 0)) : range d ⊆ range c := by
  let _instLineOverlapProofMetric : MetricSpace M := F.metricSpace
  have hB : 0 < B := hA.trans hAB
  have hAi : A ∈ Icc (0 : ℝ) B := ⟨hA.le, hAB.le⟩
  have hBi : B ∈ Icc (0 : ℝ) B := ⟨hB.le, le_rfl⟩
  have h0i : (0 : ℝ) ∈ Icc (0 : ℝ) B := ⟨le_rfl, hB.le⟩
  have hlen : B - A = D - C := by
    have h₁ := hciso.dist_eq ⟨A, hAi⟩ ⟨B, hBi⟩
    have h₂ := hdiso.dist_eq ⟨C, ⟨le_rfl, hCD.le⟩⟩ ⟨D, ⟨hCD.le, le_rfl⟩⟩
    simp only [Subtype.dist_eq, Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hAB.le),
      abs_of_nonpos (sub_nonpos.mpr hCD.le), neg_sub] at h₁ h₂
    rw [hleft, hright] at h₁
    exact h₁.symm.trans h₂
  let k : ℝ → M := fun t ↦ d (t + C - A)
  have hka : k A = d C := by simp [k]
  have hkb : k B = d D := by
    change d (B + C - A) = d D
    congr 1
    linarith
  have hkEL : F.IsEulerLagrangeOn k univ := by
    have he : k = d ∘ (fun r ↦ (1 : ℝ) * (r - (A - C))) := by
      funext t
      dsimp [k]
      congr 1
      ring
    rw [he]
    simpa only [preimage_univ] using
      hF.isEulerLagrangeOn_affine hd (s := 1) (a := A - C) zero_lt_one
  have hkiso : Isometry (fun t : Icc A B ↦ k t) := by
    apply Isometry.of_dist_eq
    intro s t
    have hmap (r : Icc A B) : (r : ℝ) + C - A ∈ Icc C D := by
      constructor <;> linarith [r.property.1, r.property.2]
    have he := hdiso.dist_eq ⟨(s : ℝ) + C - A, hmap s⟩
      ⟨(t : ℝ) + C - A, hmap t⟩
    change dist (d ((s : ℝ) + C - A)) (d ((t : ℝ) + C - A)) = dist s t
    rw [he]
    simp only [Subtype.dist_eq, Real.dist_eq]
    congr 1
    ring
  have hshort : Isometry (fun t : Icc (0 : ℝ) A ↦ c t) := by
    intro s t
    exact hciso.edist_eq ⟨s, ⟨s.property.1, s.property.2.trans hAB.le⟩⟩
      ⟨t, ⟨t.property.1, t.property.2.trans hAB.le⟩⟩
  have hend : dist (c 0) (k B) = B - 0 := by
    rw [hkb, ← hright]
    have he := hciso.dist_eq ⟨0, h0i⟩ ⟨B, hBi⟩
    simpa only [Subtype.dist_eq, Real.dist_eq, zero_sub, abs_neg,
      abs_of_nonneg hB.le, sub_zero] using he
  let p : ℝ → M := fun t ↦ if t ≤ A then c t else k t
  have hpiso : Isometry (fun t : Icc (0 : ℝ) B ↦ p t) :=
    isometry_Icc_splice_of_dist_eq hA.le hAB.le hshort hkiso
      (hleft.trans hka.symm) hend
  have hp0 : p 0 = c 0 := by simp only [p, ite_eq_left hA.le]
  have hpB : p B = c B := by rw [show p B = k B from ite_eq_right (not_le.mpr hAB), hkb, hright]
  have hLip : LipschitzWith 1 (fun q ↦ -dist q (c B)) :=
    (LipschitzWith.dist_left (c B)).neg
  have hsat : -dist (c B) (c B) - -dist (c 0) (c B) = B - 0 := by
    simpa only [dist_self, neg_zero, zero_sub, neg_neg] using
      (by simpa only [hkb, ← hright] using hend : dist (c 0) (c B) = B - 0)
  have hcp := hF.eqOn_isometric_intervals_of_calibrated_endpoints hcomplete hLip hB
    hciso hpiso hp0.symm hpB.symm hsat hdu.neg
  let t₀ := (A + B) / 2
  have ht₀ : t₀ ∈ Ioo A B := ⟨by dsimp [t₀]; linarith, by dsimp [t₀]; linarith⟩
  have hnear : c =ᶠ[𝓝 t₀] k := by
    filter_upwards [isOpen_Ioo.mem_nhds ht₀] with t ht
    exact (hcp ⟨hA.le.trans ht.1.le, ht.2.le⟩).trans (ite_eq_right (not_le.mpr ht.1))
  have htan : tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) c ⟨t₀, (1 : ℝ)⟩ =
      tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) k ⟨t₀, (1 : ℝ)⟩ := by
    refine TotalSpace.ext hnear.eq_of_nhds ?_
    rw [tangentMap, hnear.eq_of_nhds, tangentMap, hnear.mfderiv_eq]
  have heq : c = k := by
    funext t
    exact hF.eqOn_of_isEulerLagrangeOn isOpen_univ isPreconnected_univ hc hkEL
      (mem_univ t₀) htan (mem_univ t)
  rintro q ⟨t, rfl⟩
  refine ⟨t - C + A, ?_⟩
  rw [heq]
  change d (t - C + A + C - A) = d t
  congr 1
  ring

/-- With a fixed endpoint order, the entire equal-differential set is contained in
one fixed smooth complete geodesic image. The curve is selected once, independently of x. -/
theorem exists_ordered_distance_alignment_curve (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    {y z : M} (hyz : y ≠ z) :
    letI _instLineOrderedOutputMetric : MetricSpace M := F.metricSpace
    ∃ c : ℝ → M, F.IsEulerLagrangeOn c univ ∧
      ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞ c ∧
      ∀ x ∈ F.distanceDifferentialAlignmentSet y z,
        dist x y < dist x z → x ∈ range c := by
  classical
  let _instLineOrderedProofMetric : MetricSpace M := F.metricSpace
  let _instLineOrderedProofENorm : ∀ q : M, ENorm (TangentSpace 𝓘(ℝ, E) q) := F.enorm
  by_cases hnon : ∃ x ∈ F.distanceDifferentialAlignmentSet y z, dist x y < dist x z
  · obtain ⟨x₀, hx₀, hord₀⟩ := hnon
    obtain ⟨c, hc0, hcy, hcz, hcEL, hcsm, _, _, hci⟩ :=
      hF.exists_complete_minimizer_of_distance_differential_eq hcomplete
        hx₀.1 hx₀.2.1 hx₀.2.2.1 hx₀.2.2.2.1 hx₀.2.2.2.2
    refine ⟨c, hcEL, hcsm, ?_⟩
    intro x hx hord
    obtain ⟨d, hd0, hdy, hdz, hdEL, _, _, _, hdi⟩ :=
      hF.exists_complete_minimizer_of_distance_differential_eq hcomplete
        hx.1 hx.2.1 hx.2.2.1 hx.2.2.2.1 hx.2.2.2.2
    have hdshort : Isometry (fun t : Icc (dist x y) (dist x z) ↦ d t) := by
      intro s t
      exact hdi.edist_eq ⟨s, ⟨dist_nonneg.trans s.property.1, s.property.2⟩⟩
        ⟨t, ⟨dist_nonneg.trans t.property.1, t.property.2⟩⟩
    have hdstart : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ)
        (fun q ↦ (F.lengthEDist q (c (dist x₀ z))).toReal) (c 0) := by
      simpa only [hcz, hc0] using hx₀.2.2.2.1
    have hsub := hF.range_subset_range_of_isometric_overlap hcomplete
      (dist_pos.mpr hx₀.1) hord₀ hord hcEL hdEL hci hdshort
      (hcy.trans hdy.symm) (hcz.trans hdz.symm) hdstart
    exact hsub ⟨0, hd0⟩
  · obtain ⟨c, _, _, hcEL, hcsm, _⟩ :=
      hF.exists_smooth_lengthMetric_minimizer hcomplete hyz
    exact ⟨c, hcEL, hcsm, fun x hx hord ↦ (hnon ⟨x, hx, hord⟩).elim⟩

/-- For fixed distinct targets, every point of equality of the two actual distance
differentials lies in the union of at most two fixed smooth complete geodesic images. -/
theorem distance_alignment_subset_two_complete_curves (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    {y z : M} (hyz : y ≠ z) :
    ∃ c d : ℝ → M, F.IsEulerLagrangeOn c univ ∧ F.IsEulerLagrangeOn d univ ∧
      ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞ c ∧ ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞ d ∧
      F.distanceDifferentialAlignmentSet y z ⊆ range c ∪ range d := by
  let _instLineTwoCurvesProofMetric : MetricSpace M := F.metricSpace
  obtain ⟨c, hcEL, hcsm, hc⟩ := hF.exists_ordered_distance_alignment_curve hcomplete hyz
  obtain ⟨d, hdEL, hdsm, hd⟩ := hF.exists_ordered_distance_alignment_curve hcomplete hyz.symm
  refine ⟨c, d, hcEL, hdEL, hcsm, hdsm, ?_⟩
  intro x hx
  have hne : dist x y ≠ dist x z := by
    intro he
    obtain ⟨g, _, hgy, hgz, _⟩ :=
      hF.exists_complete_minimizer_of_distance_differential_eq hcomplete
        hx.1 hx.2.1 hx.2.2.1 hx.2.2.2.1 hx.2.2.2.2
    exact hyz (hgy.symm.trans ((congrArg g he).trans hgz))
  rcases lt_or_gt_of_ne hne with hord | hord
  · exact Or.inl (hc x hx hord)
  · exact Or.inr (hd x ⟨hx.2.1, hx.1, hx.2.2.2.1, hx.2.2.1, hx.2.2.2.2.symm⟩ hord)

end IsSmoothStronglyConvex
end OTSelector.Geometry.ContinuousFinslerNorm

end
end
