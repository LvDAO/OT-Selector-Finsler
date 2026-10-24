import OTSelector.Analysis.Calculus.Whitney.MetricPotentialFiniteC11Cover
import OTSelector.Geometry.Finsler.AffineTime
import OTSelector.Geometry.Finsler.Basic
import OTSelector.Geometry.Finsler.EndpointLengthSupport
import OTSelector.Geometry.Finsler.Energy.Basic
import OTSelector.Geometry.Finsler.Geodesic.ConstantSpeedDistance
import OTSelector.Geometry.Finsler.Geodesic.Defs
import OTSelector.Geometry.Finsler.LengthMetric
import OTSelector.Geometry.Finsler.UniformEndpointLengthSupport

/-!
# Geometry.Finsler.CalibratedC11

* **Conditions:** A compact legal core with uniform positive two-sided calibrated reach.
* **Objects:** A finite cover by compact pieces with global C1,1 extensions matching the original potential and its true first differential.
* **Proof detail:** Construct uniform smooth touching endpoint costs, derive quantitative Whitney contact estimates and apply the C1,1 extension construction piecewise.

Mathematical sources:
- [Rotem Assouline, Curvature-Dimension for Autonomous Lagrangians, arXiv:2409.08001v6 (10 February 2026)](https://arxiv.org/pdf/2409.08001v6#page=33): Section 4.2, Theorem 4.11, p. 33, Lemmas 4.12–4.13, pp. 34–36, proof of Theorem 4.11, p. 36; Lemma 4.15, p. 37.
- [Hassler Whitney, Analytic Extensions of Differentiable Functions Defined in Closed Sets, Transactions of the AMS 36(1), 63–89 (1934)](https://www.ams.org/journals/tran/1934-036-01/S0002-9947-1934-1501735-3/S0002-9947-1934-1501735-3.pdf#page=2): Section 3, pp. 64–65, equations (3.1)–(3.2); Section 6, p. 66, equations (6.1)–(6.3).
- [Terence Tao, An Epsilon of Room, I: Real Analysis (author preliminary version)](https://terrytao.wordpress.com/wp-content/uploads/2012/12/gsm-117-tao3-epsilon1.pdf#page=110): Sections 1.6.2 and 1.8.1, compactness by finite subcovers, pp. 78 and 101–102; Section 1.8.3, Proposition 1.8.10, pp. 107–108 (finite products).
- [Aris Daniilidis; Mounir Haddou; Erwan Le Gruyer; Olivier Ley, Explicit formulas for C1,1 Glaeser-Whitney extensions of 1-Taylor fields in Hilbert spaces (author manuscript)](https://www.arisdaniilidis.at/DHLL.pdf#page=2): Introduction, equation (1.1), pp. 1–2; Section 3, Theorem 3.1, pp. 6–7.

Source relation (derived): Assouline supplies the precise geometric C1,1 theorem/estimate; Whitney1934 is cited for jet compatibility only, not as a verbatim quantitative Lipschitz-gradient theorem. The scalar Hilbert C1,1 theorem of Daniilidis–Haddou–Le Gruyer–Ley supplies a precise quantitative comparison; finite-dimensional normed/cutoff details are locally derived and no optimal gradient constant or explicit formula is claimed.
-/

/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Geometry.FinslerCalibratedC11.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Geometry.FinslerCalibratedC11`; the selected original proof blocks follow. -/
section

/-!
# Finite C1,1 covers from original two-sided Finsler calibration

A compact legal coordinate core with a common positive calibrated reach has a finite
cover by compact pieces carrying C1,1 extensions of the original potential and its
actual first derivative. The smooth minimizing curves and uniform original-distance
upper costs are constructed internally. No regularity of endpoint choices is assumed.
-/

open Set Filter Metric Manifold
open scoped Topology ContDiff NNReal

noncomputable section
namespace OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [PreconnectedSpace M]
  {F : ContinuousFinslerNorm E M}

private theorem exists_uniform_distance_costs_on_compact
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace) (old : M)
    {K : Set E} (hK : IsCompact K)
    (hKtarget : K ⊆ (extChartAt 𝓘(ℝ, E) old).target) {δ : ℝ} (hδ : 0 < δ) :
    let _instCalibratedCostMetric : MetricSpace M := F.metricSpace
    ∃ (r : ℝ) (C : ℝ≥0), 0 < r ∧
      ∀ x ∈ K, ∀ p : M, dist p ((extChartAt 𝓘(ℝ, E) old).symm x) = δ →
        ∃ A : E → ℝ,
          (∀ z ∈ ball x (2 * r),
            dist p ((extChartAt 𝓘(ℝ, E) old).symm z) ≤ A z) ∧
          A x = dist p ((extChartAt 𝓘(ℝ, E) old).symm x) ∧
          ContDiffOn ℝ ∞ A (ball x (2 * r)) ∧
          ∀ z ∈ closedBall x r, ‖fderiv ℝ (fderiv ℝ A) z‖ ≤ (C : ℝ) := by
  let _instCalibratedCostMetric : MetricSpace M := F.metricSpace
  let _instCalibratedCostENorm : ∀ z : M, ENorm (TangentSpace 𝓘(ℝ, E) z) := F.enorm
  obtain ⟨τ, r, C, hτ, hτδ, hr, hcost⟩ :=
    hF.exists_uniform_endpointLengthSupport hcomplete old hK hKtarget hδ
  refine ⟨r, C, hr, ?_⟩
  intro x hx p hdist
  have hp : p ≠ (extChartAt 𝓘(ℝ, E) old).symm x := by
    apply dist_pos.mp
    rwa [hdist]
  obtain ⟨c, hstart, hend, hEL, _, hspeed, hmin⟩ :=
    hF.exists_smooth_lengthMetric_minimizer_fixedTime hcomplete
      (a := -δ) (b := 0) (by linarith) hp
  have hunit (t : ℝ) :
      F.toFun (tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) c ⟨t, (1 : ℝ)⟩) = 1 := by
    apply NNReal.coe_injective
    simpa only [hdist, zero_sub, neg_neg, div_self hδ.ne', NNReal.coe_one] using hspeed t
  have hsource : c 0 ∈ (extChartAt 𝓘(ℝ, E) old).source := by
    rw [hend]
    exact (extChartAt 𝓘(ℝ, E) old).map_target (hKtarget hx)
  have hbase : extChartAt 𝓘(ℝ, E) old (c 0) = x := by
    rw [hend]
    exact (extChartAt 𝓘(ℝ, E) old).right_inv (hKtarget hx)
  obtain ⟨_, hS, hH, hdom, htouch, _⟩ :=
    hcost c hEL (hunit 0) hsource (by rwa [hbase])
  simp only [Function.comp_apply, hbase] at hS hH hdom htouch
  have hprefix : dist p (c (-τ)) = δ - τ := by
    have hh := F.dist_eq_mul_sub_of_constant_speed (s := 1)
      (show -δ ≤ -τ by linarith) (fun t _ ↦ hunit t)
      (hmin (-δ) ⟨le_rfl, by linarith⟩ (-τ) ⟨by linarith, by linarith⟩
        (by linarith))
    rw [hstart] at hh
    simp only [NNReal.coe_one, one_mul] at hh
    linarith
  let S : E → ℝ := F.chartEndpointLengthSupport old
    (extChartAt 𝓘(ℝ, E) old ∘ c) (-τ) 0
  let A : E → ℝ := fun z ↦ dist p (c (-τ)) + S z
  refine ⟨A, ?_, ?_, contDiffOn_const.add hS, ?_⟩
  · intro z hz
    exact (dist_triangle p (c (-τ)) ((extChartAt 𝓘(ℝ, E) old).symm z)).trans
      (add_le_add le_rfl (hdom z hz))
  · change dist p (c (-τ)) + S x = _
    rw [hprefix, hdist]
    change δ - τ + F.chartEndpointLengthSupport old
      (extChartAt 𝓘(ℝ, E) old ∘ c) (-τ) 0 x = δ
    rw [htouch]
    ring
  · have he : fderiv ℝ A = fderiv ℝ S :=
      funext (fun z ↦ fderiv_const_add (dist p (c (-τ))))
    rw [he]
    exact hH

/-- Original positive two-sided calibrated reach on a compact legal chart core yields
finite compact C1,1 extension pieces matching both the potential and its actual first
jet. Completeness supplies the actual smooth minimizers; all upper costs and Hessian
bounds are derived from the given smooth strongly convex Finsler structure. -/
theorem exists_finite_calibrated_C11_cover (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace) (old : M)
    {K : Set E} (hK : IsCompact K)
    (hKtarget : K ⊆ (extChartAt 𝓘(ℝ, E) old).target)
    {u : M → ℝ} {δ : ℝ} (hδ : 0 < δ) :
    let _instCalibratedC11Metric : MetricSpace M := F.metricSpace
    LipschitzWith 1 u →
    (∀ x ∈ K, ∃ a b : M,
      dist a ((extChartAt 𝓘(ℝ, E) old).symm x) = δ ∧
      u ((extChartAt 𝓘(ℝ, E) old).symm x) - u a = δ ∧
      dist ((extChartAt 𝓘(ℝ, E) old).symm x) b = δ ∧
      u b - u ((extChartAt 𝓘(ℝ, E) old).symm x) = δ) →
    ∃ r : ℝ, 0 < r ∧ ∃ J : Finset E,
      K ⊆ ⋃ q ∈ J, closedBall q (r / 8) ∧
      ∀ q ∈ J, IsCompact (K ∩ closedBall q (r / 8)) ∧
        ∃ (G : E → ℝ) (L : ℝ≥0), ContDiff ℝ 1 G ∧ HasCompactSupport G ∧
          ContDiffOn ℝ ∞ G (K ∩ closedBall q (r / 8))ᶜ ∧
          LipschitzWith L (fderiv ℝ G) ∧
          EqOn G (u ∘ (extChartAt 𝓘(ℝ, E) old).symm) (K ∩ closedBall q (r / 8)) ∧
          EqOn (fderiv ℝ G) (fderiv ℝ (u ∘ (extChartAt 𝓘(ℝ, E) old).symm))
            (K ∩ closedBall q (r / 8)) ∧
          ∀ x ∈ K ∩ closedBall q (r / 8),
            HasFDerivAt (u ∘ (extChartAt 𝓘(ℝ, E) old).symm) (fderiv ℝ G x) x := by
  classical
  let _instCalibratedC11Metric : MetricSpace M := F.metricSpace
  change LipschitzWith 1 u → _
  intro hu hreach
  let Y : E → M := (extChartAt 𝓘(ℝ, E) old).symm
  obtain ⟨r, C, hr, hcost⟩ :=
    exists_uniform_distance_costs_on_compact hF hcomplete old hK hKtarget hδ
  have hendpoints : ∀ x : E, ∃ a b : M, x ∈ K →
      dist a (Y x) = δ ∧ u (Y x) - u a = δ ∧
      dist (Y x) b = δ ∧ u b - u (Y x) = δ := by
    intro x
    by_cases hx : x ∈ K
    · obtain ⟨a, b, hab⟩ := hreach x hx
      exact ⟨a, b, fun _ ↦ hab⟩
    · exact ⟨Y x, Y x, fun h ↦ (hx h).elim⟩
  choose a b hab using hendpoints
  have hAcost : ∀ x : E, ∃ A : E → ℝ, x ∈ K →
      (∀ z ∈ ball x (2 * r), dist (a x) (Y z) ≤ A z) ∧
      A x = dist (a x) (Y x) ∧ ContDiffOn ℝ ∞ A (ball x (2 * r)) ∧
      ∀ z ∈ closedBall x r, ‖fderiv ℝ (fderiv ℝ A) z‖ ≤ (C : ℝ) := by
    intro x
    by_cases hx : x ∈ K
    · obtain ⟨A, hA⟩ := hcost x hx (a x) (hab x hx).1
      exact ⟨A, fun _ ↦ hA⟩
    · exact ⟨0, fun h ↦ (hx h).elim⟩
  have hBcost : ∀ x : E, ∃ B : E → ℝ, x ∈ K →
      (∀ z ∈ ball x (2 * r), dist (Y z) (b x) ≤ B z) ∧
      B x = dist (Y x) (b x) ∧ ContDiffOn ℝ ∞ B (ball x (2 * r)) ∧
      ∀ z ∈ closedBall x r, ‖fderiv ℝ (fderiv ℝ B) z‖ ≤ (C : ℝ) := by
    intro x
    by_cases hx : x ∈ K
    · obtain ⟨B, hdom, htouch, hsmooth, hH⟩ :=
        hcost x hx (b x) (by rw [dist_comm]; exact (hab x hx).2.2.1)
      exact ⟨B, fun _ ↦ ⟨fun z hz ↦ by simpa only [dist_comm] using hdom z hz,
        by simpa only [dist_comm] using htouch, hsmooth, hH⟩⟩
    · exact ⟨0, fun h ↦ (hx h).elim⟩
  choose cA hA using hAcost
  choose cB hB using hBcost
  refine ⟨r, hr, ?_⟩
  exact exists_finite_metric_potential_C11_cover_of_upper_costs hu Y hK hr C a b cA cB
    (fun x hx ↦ (hab x hx).2.1.trans (hab x hx).1.symm)
    (fun x hx ↦ (hab x hx).2.2.2.trans (hab x hx).2.2.1.symm)
    (fun x hx ↦ (hA x hx).1) (fun x hx ↦ (hB x hx).1)
    (fun x hx ↦ (hA x hx).2.1) (fun x hx ↦ (hB x hx).2.1)
    (fun x hx ↦ (hA x hx).2.2.1) (fun x hx ↦ (hB x hx).2.2.1)
    (fun x hx ↦ (hA x hx).2.2.2) (fun x hx ↦ (hB x hx).2.2.2)

end OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

end
end
