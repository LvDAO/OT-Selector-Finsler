import OTSelector.Analysis.Calculus.AffineEndpointVariation
import OTSelector.Analysis.Calculus.Variational.AffinePhaseIntegralHessian
import OTSelector.Analysis.Calculus.Variational.CompactAffineEndpointPhase
import OTSelector.Geometry.Finsler.Basic
import OTSelector.Geometry.Finsler.Calibration.Chart
import OTSelector.Geometry.Finsler.CompactUnitTrace
import OTSelector.Geometry.Finsler.EndpointLengthSupport
import OTSelector.Geometry.Finsler.Energy.Basic
import OTSelector.Geometry.Finsler.Energy.Chart
import OTSelector.Geometry.Finsler.Geodesic.Defs
import OTSelector.Geometry.Finsler.Geodesic.Energy
import OTSelector.Geometry.Finsler.LengthHessian
import OTSelector.Geometry.Finsler.LengthMetric

/-!
# Geometry.Finsler.UniformEndpointLengthSupport

* **Conditions:** A compact actual coordinate core and the entire unit-speed phase layer, with smooth strong convexity.
* **Objects:** Uniform time, endpoint radius and Hessian bounds for true endpoint-length upper supports of every corresponding complete unit curve.
* **Proof detail:** Use compact flow traces, keep affine endpoint perturbations in a common slit neighborhood and bound their actual length Hessians there.

Mathematical sources:
- [Rotem Assouline, Curvature-Dimension for Autonomous Lagrangians, arXiv:2409.08001v6 (10 February 2026)](https://arxiv.org/pdf/2409.08001v6#page=33): Section 4.2, Theorem 4.11, p. 33, Lemmas 4.12–4.13, pp. 34–36, proof of Theorem 4.11, p. 36; Lemma 4.15, p. 37.
- [Jiří Lebl, Basic Analysis II: Introduction to Real Analysis, Volume II](https://www.jirka.org/ra/realanal2.pdf): Sections 8.3–8.4, total derivative, chain rule and mean-value bounds; Section 8.6, higher derivatives.
- [Terence Tao, An Epsilon of Room, I: Real Analysis (author preliminary version)](https://terrytao.wordpress.com/wp-content/uploads/2012/12/gsm-117-tao3-epsilon1.pdf#page=110): Sections 1.6.2 and 1.8.1, compactness by finite subcovers, pp. 78 and 101–102; Section 1.8.3, Proposition 1.8.10, pp. 107–108 (finite products).
- [Zhongmin Shen, Landsberg Curvature, S-Curvature and Riemann Curvature, in Riemann–Finsler Geometry, MSRI Publications 50 (2004)](https://library.slmath.org/books/Book50/files/08Sh.pdf#page=11): Section 4, p. 313: the length integral, induced distance and minimizing curves.

Source relation (derived): Derived from the cited geometric/analytic principles with the exact actual source hypotheses. The local construction and its original phase/covector data are retained, rather than asserted as a verbatim source statement.
-/

/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Geometry.FinslerUniformEndpointLengthSupport.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Geometry.FinslerUniformEndpointLengthSupport`; the selected original proof blocks follow. -/
section

/-!
# Uniform original endpoint-length upper supports

Compact coordinate cores admit common time, endpoint radius, and actual Hessian bounds
for the explicit original lengths of affine endpoint perturbations of every complete
unit-speed Euler--Lagrange curve. The same costs dominate original distance and touch
it on minimizing central segments.
-/

open Set Filter Manifold Bundle MeasureTheory Metric
open scoped Topology ContDiff ENNReal NNReal

noncomputable section
namespace OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [PreconnectedSpace M]
  {F : ContinuousFinslerNorm E M}

/-- Every common endpoint domain of actual legal slit perturbations supplies smooth
original length costs and upper bounds for the original endpoint distance. -/
theorem endpointLengthSupport_properties_of_phase_domain
    (hF : F.IsSmoothStronglyConvex) (old : M)
    {x : ℝ → E} {I : Set ℝ} (hI : IsOpen I) (hx : ContDiffOn ℝ ∞ x I)
    {a b : ℝ} (hab : a < b) (hseg : Icc a b ⊆ I)
    {U : Set E} (hU : IsOpen U)
    (hphase : ∀ z ∈ U, ∀ t ∈ Icc a b,
      affineEndpointPhase x a b (z, t) ∈ chartEnergyDomain old) :
    let _instUniformEndpointDomainMetric : MetricSpace M := F.metricSpace
    U ⊆ (extChartAt 𝓘(ℝ, E) old).target ∧
      ContDiffOn ℝ ∞ (F.chartEndpointLengthSupport old x a b) U ∧
      ∀ z ∈ U, dist ((extChartAt 𝓘(ℝ, E) old).symm (x a))
        ((extChartAt 𝓘(ℝ, E) old).symm z) ≤
          F.chartEndpointLengthSupport old x a b z := by
  let _instUniformEndpointDomainMetric : MetricSpace M := F.metricSpace
  have hpath (z : E) : ContDiffOn ℝ 1
      (fun t ↦ affineEndpointVariation x a b (z, t)) I :=
    ((contDiffOn_affineEndpointVariation hx a b).comp
      (contDiffOn_const.prodMk contDiffOn_id) (fun _ ht ↦ ⟨mem_univ _, ht⟩)).of_le
        (by simp)
  have hderiv (z : E) (t : ℝ) (ht : t ∈ I) :
      deriv (fun s ↦ affineEndpointVariation x a b (z, s)) t =
        (affineEndpointPhase x a b (z, t)).2 :=
    (hasDerivAt_affineEndpointVariation
      ((hx.contDiffAt (hI.mem_nhds ht)).differentiableAt (by simp)) z).deriv
  have hbase (z : E) (hz : z ∈ U) (t : ℝ) (ht : t ∈ Icc a b) :
      affineEndpointVariation x a b (z, t) ∈ (extChartAt 𝓘(ℝ, E) old).target :=
    (hphase z hz t ht).1
  refine ⟨?_, ?_, ?_⟩
  · intro z hz
    have hh := hbase z hz b (right_mem_Icc.mpr hab.le)
    rwa [(affineEndpointVariation_endpoints x hab z).2] at hh
  · exact contDiffOn_intervalIntegral_affineEndpointPhase hI hx
      (isOpen_chartEnergyDomain old) (hF.contDiffOn_chartLength old) hab.le hseg hU hphase
  · intro z hz
    have hb := F.dist_chart_le_integral_chartLength old hI (hpath z) hab.le hseg
      (hbase z hz)
    rw [(affineEndpointVariation_endpoints x hab z).1,
      (affineEndpointVariation_endpoints x hab z).2] at hb
    refine hb.trans_eq ?_
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le hab.le] at ht
    dsimp only
    rw [hderiv z t (hseg ht)]
    rfl

omit [FiniteDimensional ℝ E] [T2Space M] [PreconnectedSpace M] in
/-- For a genuine unit-speed curve the central affine support is its elapsed time,
without requiring its central segment to be minimizing. -/
theorem endpointLengthSupport_center_eq_of_unit
    (hF : F.IsSmoothStronglyConvex) (old : M) {c : ℝ → M}
    (hc : F.IsEulerLagrangeOn c univ)
    (hunit : F.toFun (tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) c ⟨0, (1 : ℝ)⟩) = 1)
    {I : Set ℝ} (hI : IsOpen I)
    (hmap : MapsTo c I (extChartAt 𝓘(ℝ, E) old).source)
    (hx : ContDiffOn ℝ ∞ (extChartAt 𝓘(ℝ, E) old ∘ c) I)
    {a b : ℝ} (hab : a ≤ b) (hseg : Icc a b ⊆ I) :
    F.chartEndpointLengthSupport old (extChartAt 𝓘(ℝ, E) old ∘ c) a b
      (extChartAt 𝓘(ℝ, E) old (c b)) = b - a := by
  change (∫ t in a..b,
    (F.chartLength old (affineEndpointPhase (extChartAt 𝓘(ℝ, E) old ∘ c) a b
      ((extChartAt 𝓘(ℝ, E) old ∘ c) b, t)) : ℝ)) = b - a
  calc
    _ = ∫ _t in a..b, (1 : ℝ) := by
      apply intervalIntegral.integral_congr
      intro t ht
      rw [uIcc_of_le hab] at ht
      dsimp only
      rw [affineEndpointPhase_center]
      have hs := hF.speed_eq_of_isEulerLagrangeOn hc isPreconnected_univ
        (mem_univ t) (mem_univ (0 : ℝ))
      rw [hunit, F.speed_eq_chartLength old hI (hseg ht) hmap
        ((hx.contDiffAt (hI.mem_nhds (hseg ht))).differentiableAt (by simp))] at hs
      exact_mod_cast hs
    _ = b - a := by simp

/-- One compact chart core has uniform smooth original endpoint-length supports for
all complete curves of original unit speed. The original Hessian bound and distance
upper support are constructed from the actual geometry; a minimizing segment gives
central touching. No regularity of any selected initial direction is required. -/
theorem exists_uniform_endpointLengthSupport
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace) (old : M)
    {K : Set E} (hK : IsCompact K)
    (hKtarget : K ⊆ (extChartAt 𝓘(ℝ, E) old).target) {ε : ℝ} (hε : 0 < ε) :
    let _instUniformEndpointSupportMetric : MetricSpace M := F.metricSpace
    ∃ (τ r : ℝ) (C : ℝ≥0), 0 < τ ∧ τ ≤ ε ∧ 0 < r ∧
      ∀ (c : ℝ → M), F.IsEulerLagrangeOn c univ →
        F.toFun (tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) c ⟨0, (1 : ℝ)⟩) = 1 →
        c 0 ∈ (extChartAt 𝓘(ℝ, E) old).source → extChartAt 𝓘(ℝ, E) old (c 0) ∈ K →
        let x := extChartAt 𝓘(ℝ, E) old ∘ c
        let S := F.chartEndpointLengthSupport old x (-τ) 0
        ball (x 0) (2 * r) ⊆ (extChartAt 𝓘(ℝ, E) old).target ∧
        ContDiffOn ℝ ∞ S (ball (x 0) (2 * r)) ∧
        (∀ z ∈ closedBall (x 0) r, ‖fderiv ℝ (fderiv ℝ S) z‖ ≤ (C : ℝ)) ∧
        (∀ z ∈ ball (x 0) (2 * r),
          dist (c (-τ)) ((extChartAt 𝓘(ℝ, E) old).symm z) ≤ S z) ∧
        S (x 0) = τ ∧
        (Isometry (fun t : Icc (-τ) 0 ↦ c t) → dist (c (-τ)) (c 0) = τ) := by
  let _instUniformEndpointSupportMetric : MetricSpace M := F.metricSpace
  obtain ⟨τ, I, P, hτ, hτε, hI, hseg, hP, hPD, htrace⟩ :=
    hF.exists_compact_unit_chartTrace hcomplete old hK hKtarget hε
  have hab : -τ < 0 := by linarith
  obtain ⟨r, hr, Q, C₀, _hQ, hQD, _hPQ, hH, hphase⟩ :=
    exists_compact_affineEndpointPhase_hessian_bound hP (isOpen_chartEnergyDomain old)
      hPD (hF.contDiffOn_chartLength old) hab
  let C : ℝ≥0 := ⟨τ * (C₀ : ℝ) * (1 + τ⁻¹) ^ 2, by positivity⟩
  refine ⟨τ, r, C, hτ, hτε, hr, ?_⟩
  intro c hc hunit hsource hbase
  obtain ⟨hmap, hx, htP⟩ := htrace c hc hunit hsource hbase
  let x := extChartAt 𝓘(ℝ, E) old ∘ c
  have hphaseD (z : E) (hz : z ∈ ball (x 0) (2 * r))
      (t : ℝ) (ht : t ∈ Icc (-τ) 0) :
      affineEndpointPhase x (-τ) 0 (z, t) ∈ chartEnergyDomain old :=
    hQD (hphase x htP z (ball_subset_closedBall hz) t ht)
  obtain ⟨htarget, hsmooth, hdom⟩ := hF.endpointLengthSupport_properties_of_phase_domain
    old hI hx hab hseg isOpen_ball hphaseD
  refine ⟨htarget, hsmooth, ?_, ?_, ?_, ?_⟩
  · intro z hz
    have hzr : z ∈ ball (x 0) (2 * r) :=
      mem_ball.mpr ((mem_closedBall.mp hz).trans_lt (by linarith))
    have hh := norm_fderiv_fderiv_intervalIntegral_affineEndpointPhase_le
      hI hx (isOpen_chartEnergyDomain old) (hF.contDiffOn_chartLength old)
      hab hseg isOpen_ball hphaseD hzr C₀.coe_nonneg
      (fun t ht ↦ hH _ (hphase x htP z (ball_subset_closedBall hzr) t ht))
    change ‖fderiv ℝ (fderiv ℝ (fun w : E ↦ ∫ t in -τ..0,
      (F.chartLength old (affineEndpointPhase
        (extChartAt 𝓘(ℝ, E) old ∘ c) (-τ) 0 (w, t)) : ℝ))) z‖ ≤
        τ * (C₀ : ℝ) * (1 + τ⁻¹) ^ 2
    simpa only [zero_sub, neg_neg] using hh
  · intro z hz
    have hh := hdom z hz
    simp only [Function.comp_apply] at hh
    rw [(extChartAt 𝓘(ℝ, E) old).left_inv
      (hmap (hseg (left_mem_Icc.mpr hab.le)))] at hh
    exact hh
  · simpa only [Function.comp_apply, zero_sub, neg_neg] using
      hF.endpointLengthSupport_center_eq_of_unit old hc hunit hI hmap hx hab.le hseg
  · intro hiso
    have hd := hiso.dist_eq ⟨-τ, le_rfl, hab.le⟩ ⟨0, hab.le, le_rfl⟩
    simpa only [Subtype.dist_eq, Real.dist_eq, sub_zero, abs_neg, abs_of_pos hτ] using hd

end OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

end
end
