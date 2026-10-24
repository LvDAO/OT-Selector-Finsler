import OTSelector.Geometry.Finsler.Basic
import OTSelector.Geometry.Finsler.Energy.Basic
import OTSelector.Geometry.Finsler.Geodesic.Basic
import OTSelector.Geometry.Finsler.Geodesic.Complete
import OTSelector.Geometry.Finsler.Geodesic.Defs
import OTSelector.Geometry.Finsler.Geodesic.MetricMinimizerEnergy
import OTSelector.Geometry.Finsler.Geodesic.MetricSmoothness
import OTSelector.Geometry.Finsler.Geodesic.MetricVelocity
import OTSelector.Geometry.Finsler.Geodesic.Uniqueness
import OTSelector.Geometry.Finsler.HopfRinow
import OTSelector.Geometry.Finsler.LengthMetric
import OTSelector.Geometry.Finsler.MetricDifferential
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Geometry.FinslerSmoothMinimizer.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Geometry.FinslerSmoothMinimizer`; the selected original proof blocks follow. -/
section

/-!
# Geometry.Finsler.Geodesic.SmoothMinimizer

* **Conditions:** A complete original Finsler length metric with smooth strong convexity; a nondegenerate isometric interval, or two distinct points, is specified.
* **Objects:** A complete smooth unit-speed Euler–Lagrange curve extending the whole given closed interval, and a genuine minimizing segment between distinct points.
* **Proof detail:** Combine metric Hopf–Rinow with interior regularity, extend by complete Euler–Lagrange continuation, and recover agreement at both endpoints by continuity.

Mathematical sources:
- [Anton Petrunin, Lectures on metric geometry](https://anton-petrunin.github.io/metric-geometry/tex/lectures.pdf#page=18): Lecture 1, Section L, Theorem 1.30 (Hopf–Rinow), Exercise 1.31 and proof, pp. 18–19.
- [Anton Petrunin, Lectures on metric geometry](https://anton-petrunin.github.io/metric-geometry/tex/lectures.pdf#page=18): Lecture 1, Section L, Proposition 1.29 and its preceding compact approximate-midpoint argument, p. 18; Section I, p. 13, defines a geodesic as an isometric interval.
- [Zhongmin Shen, Landsberg Curvature, S-Curvature and Riemann Curvature, MSRI Publications 50 (2004)](https://library.slmath.org/books/Book50/files/08Sh.pdf#page=11): Section 4, Definition 4.1 and Lemma 4.2, pp. 313–314; equations (4–1), (4–2) and the canonical-lift spray interpretation.
- [Gerald Teschl, Ordinary Differential Equations and Dynamical Systems (AMS 2012 author preliminary version)](https://www.mat.univie.ac.at/~gerald/ftp/book-ode/ode.pdf#page=61): Section 2.6, pp. 50–51, overlap uniqueness, equation (2.63), and Theorem 2.13 (unique maximal solution).

Source relation (derived): The minimality assertion is on the prescribed distance-length interval; the complete extension is not claimed globally minimizing for arbitrary longer intervals.
-/

/-!
# Complete smooth geodesics extending original metric minimizing intervals

Completeness of the original Finsler metric extends every nondegenerate original-
distance isometric interval to a smooth, unit-speed intrinsic Euler--Lagrange curve
on all real times, preserving the entire closed interval including its endpoints.
Consequently any two distinct points admit a genuinely smooth original-length
minimizing segment. Minimality is asserted on the prescribed distance-length interval;
the complete curve is not asserted to minimize on arbitrary longer intervals.
-/

open Set Filter Metric Manifold
open scoped Topology ContDiff NNReal

noncomputable section

namespace OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [PreconnectedSpace M]
  {F : ContinuousFinslerNorm E M}

set_option backward.isDefEq.respectTransparency false in
/-- An original-distance isometric interval extends to a complete smooth unit-speed
intrinsic Euler--Lagrange curve agreeing at every point of the original closed interval. -/
theorem exists_complete_extension_of_isometric_interval (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    {c : ℝ → M} {a b : ℝ} (hab : a < b)
    (hiso : letI : MetricSpace M := F.metricSpace
      Isometry (fun t : Icc a b ↦ c t)) :
    ∃ g : ℝ → M, F.IsEulerLagrangeOn g univ ∧
      ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞ g ∧
      (∀ t : ℝ, F.toFun (tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) g ⟨t, (1 : ℝ)⟩) = 1) ∧
      EqOn g c (Icc a b) := by
  let : MetricSpace M := F.metricSpace
  let : ∀ x : M, ENorm (TangentSpace 𝓘(ℝ, E) x) := F.enorm
  let t₀ := (a + b) / 2
  have ht₀ : t₀ ∈ Ioo a b := ⟨by dsimp [t₀]; linarith, by dsimp [t₀]; linarith⟩
  have hcEL := hF.isEulerLagrangeOn_of_isometric_interval hiso
  have hmdiff : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) c t₀ :=
    (hF.contMDiffAt_of_isEulerLagrangeAt (hcEL t₀ ht₀)).mdifferentiableAt (by simp)
  have hv := F.mfderiv_apply_one_ne_zero_of_isometry ht₀ hmdiff hiso
  have hunit := hF.speed_eq_one_of_isometry ht₀ hmdiff hiso
  obtain ⟨g, _, hgstart, hgEL, hgsmooth, hgspeed, _, _⟩ :=
    hF.exists_complete_eulerLagrange hcomplete (c t₀) hv t₀
  have hstart : tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) g ⟨t₀, (1 : ℝ)⟩ =
      tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) c ⟨t₀, (1 : ℝ)⟩ := hgstart
  have heq : EqOn g c (Ioo a b) :=
    hF.eqOn_of_isEulerLagrangeOn isOpen_Ioo isPreconnected_Ioo
      (hgEL.mono (subset_univ _)) hcEL ht₀ hstart
  have hc : ContinuousOn c (Icc a b) :=
    continuousOn_iff_continuous_domRestrict.mpr hiso.continuous
  refine ⟨g, hgEL, hgsmooth, ?_, ?_⟩
  · intro t
    exact (hgspeed t).trans hunit
  · apply heq.of_subset_closure hgsmooth.continuous.continuousOn hc Ioo_subset_Icc_self
    rw [closure_Ioo hab.ne]

set_option backward.isDefEq.respectTransparency false in
/-- Distinct points in the complete original metric are joined by a smooth unit-speed
segment which realizes the actual Finsler length distance on all its ordered subsegments.
The containing intrinsic Euler--Lagrange curve is defined for all real times. -/
theorem exists_smooth_lengthMetric_minimizer (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    {x y : M} (hxy : x ≠ y) :
    letI : MetricSpace M := F.metricSpace
    letI : ∀ u : M, ENorm (TangentSpace 𝓘(ℝ, E) u) := F.enorm
    ∃ g : ℝ → M, g 0 = x ∧ g (dist x y) = y ∧
      F.IsEulerLagrangeOn g univ ∧ ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞ g ∧
      (∀ t : ℝ, F.toFun (tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) g ⟨t, (1 : ℝ)⟩) = 1) ∧
      Isometry (fun t : Icc (0 : ℝ) (dist x y) ↦ g t) ∧
      ∀ s ∈ Icc (0 : ℝ) (dist x y), ∀ t ∈ Icc (0 : ℝ) (dist x y), s ≤ t →
        F.lengthEDist (g s) (g t) = pathELength 𝓘(ℝ, E) g s t := by
  let : MetricSpace M := F.metricSpace
  let : ∀ u : M, ENorm (TangentSpace 𝓘(ℝ, E) u) := F.enorm
  have hdist : 0 < dist x y := dist_pos.mpr hxy
  obtain ⟨γ, hγ, hγ0, hγ1⟩ := F.exists_lengthMetric_isometric_interval hcomplete x y
  let c : ℝ → M := γ ∘ projIcc 0 (dist x y) dist_nonneg
  have heq (t : ℝ) (ht : t ∈ Icc (0 : ℝ) (dist x y)) : c t = γ ⟨t, ht⟩ := by
    simp only [c, Function.comp_apply, projIcc_of_mem _ ht]
  have hiso : Isometry (fun t : Icc (0 : ℝ) (dist x y) ↦ c t) := by
    intro s t
    change edist (c s) (c t) = edist s t
    rw [heq s s.property, heq t t.property]
    exact hγ.edist_eq s t
  obtain ⟨g, hgEL, hgsmooth, hgspeed, hg⟩ :=
    hF.exists_complete_extension_of_isometric_interval hcomplete hdist hiso
  have hgiso : Isometry (fun t : Icc (0 : ℝ) (dist x y) ↦ g t) := by
    intro s t
    change edist (g s) (g t) = edist s t
    rw [hg s.property, hg t.property]
    exact hiso.edist_eq s t
  refine ⟨g, ?_, ?_, hgEL, hgsmooth, hgspeed, hgiso, ?_⟩
  · exact (hg (left_mem_Icc.mpr hdist.le)).trans ((heq 0 (left_mem_Icc.mpr hdist.le)).trans hγ0)
  · exact (hg (right_mem_Icc.mpr hdist.le)).trans
      ((heq (dist x y) (right_mem_Icc.mpr hdist.le)).trans hγ1)
  · intro s hs t ht hst
    apply hF.lengthEDist_eq_pathELength_of_isometric_interval hst
    intro u v
    exact hgiso.edist_eq ⟨u, (Icc_subset_Icc hs.1 ht.2) u.property⟩
      ⟨v, (Icc_subset_Icc hs.1 ht.2) v.property⟩

end OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

end
end
