import OTSelector.Analysis.Convex.Legendre.Parametric
import OTSelector.Geometry.Finsler.Basic
import OTSelector.Geometry.Finsler.C11FiniteTimeLipschitz
import OTSelector.Geometry.Finsler.C11ShortTranslation
import OTSelector.Geometry.Finsler.CalibratedBackwardIdentity
import OTSelector.Geometry.Finsler.CalibratedC11
import OTSelector.Geometry.Finsler.CalibratedCovector
import OTSelector.Geometry.Finsler.CalibratedInterior
import OTSelector.Geometry.Finsler.CalibratedTranslation
import OTSelector.Geometry.Finsler.CompleteHamiltonianFamily
import OTSelector.Geometry.Finsler.Energy.Basic
import OTSelector.Geometry.Finsler.Energy.Chart
import OTSelector.Geometry.Finsler.Geodesic.Defs
import OTSelector.Geometry.Finsler.Geodesic.Proofs.LocalEquation
import OTSelector.Geometry.Finsler.LengthMetric
import OTSelector.Topology.FiniteClosedCoverLowerBound

/-!
# Geometry.Finsler.CalibratedLowerBound

* **Conditions:** An actual compact calibrated C1,1 core translated strictly within its positive reach.
* **Objects:** A positive centered lower norm bound for the original translated coordinate readout.
* **Proof detail:** Cover the compact translated core by finite reverse C1,1 families, use their actual finite-time Lipschitz estimates and exact return identities.

Mathematical sources:
- [Rotem Assouline, Curvature-Dimension for Autonomous Lagrangians, arXiv:2409.08001v6 (10 February 2026)](https://arxiv.org/pdf/2409.08001v6#page=39): Section 4.3, Lemma 4.21(i)–(iii), p. 39, and proof pp. 40–42.
- [Gerald Teschl, Ordinary Differential Equations and Dynamical Systems (AMS 2012 author preliminary version)](https://www.mat.univie.ac.at/~gerald/ftp/book-ode/ode.pdf#page=56): Section 2.4, pp. 45–47, equations (2.46)–(2.50), Theorem 2.10.
- [Terence Tao, An Epsilon of Room, I: Real Analysis (author preliminary version)](https://terrytao.wordpress.com/wp-content/uploads/2012/12/gsm-117-tao3-epsilon1.pdf#page=110): Sections 1.6.2 and 1.8.1, compactness by finite subcovers, pp. 78 and 101–102; Section 1.8.3, Proposition 1.8.10, pp. 107–108 (finite products).

Source relation (derived): The lower bound is constructed; no derivative-rank hypothesis is supplied.
-/

/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Geometry.FinslerCalibratedLowerBound.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Geometry.FinslerCalibratedLowerBound`; the selected original proof blocks follow. -/
section

/-!
# Centered lower bounds for original calibrated geodesic translations

A compact calibrated core moves into a compact set with positive calibrated reach.
Finite C1,1 extension pieces there construct actual reverse geodesic families.
Their finite-time Lipschitz readouts and exact return identities yield a positive
centered lower bound for the original translation, without an assumed rank condition.
-/

open Set Filter Metric Manifold Bundle
open scoped Topology ContDiff NNReal

noncomputable section
namespace OTSelector.Geometry

private theorem lowerBound_shifted_calibrated_partners
    {M : Type*} [PseudoMetricSpace M] {c : ℝ → M} {u : M → ℝ} {δ t : ℝ}
    (hclock : ∀ s ∈ Icc (-δ) δ, u (c s) = u (c 0) + s)
    (hiso : Isometry (fun s : Icc (-δ) δ ↦ c s)) (ht : |t| < δ) :
    let η := (δ - |t|) / 2
    0 < η ∧ ∃ a b, dist a (c t) = η ∧ u (c t) - u a = η ∧
      dist (c t) b = η ∧ u b - u (c t) = η := by
  let η := (δ - |t|) / 2
  have hη : 0 < η := by dsimp [η]; linarith
  have htlo := neg_abs_le t
  have hthi := le_abs_self t
  have htI : t ∈ Icc (-δ) δ := ⟨by linarith, by linarith⟩
  have hlo : t - η ∈ Icc (-δ) δ := by
    dsimp [η]
    constructor <;> linarith
  have hhi : t + η ∈ Icc (-δ) δ := by
    dsimp [η]
    constructor <;> linarith
  refine ⟨hη, c (t - η), c (t + η), ?_, ?_, ?_, ?_⟩
  · have hd := hiso.dist_eq ⟨t - η, hlo⟩ ⟨t, htI⟩
    change dist (c (t - η)) (c t) = dist (t - η) t at hd
    rw [hd, Real.dist_eq, abs_of_nonpos (by linarith : t - η - t ≤ 0)]
    ring
  · rw [hclock t htI, hclock (t - η) hlo]
    ring
  · have hd := hiso.dist_eq ⟨t, htI⟩ ⟨t + η, hhi⟩
    change dist (c t) (c (t + η)) = dist t (t + η) at hd
    rw [hd, Real.dist_eq, abs_of_nonpos (by linarith : t - (t + η) ≤ 0)]
    ring
  · rw [hclock (t + η) hhi, hclock t htI]
    ring

namespace ContinuousFinslerNorm.IsSmoothStronglyConvex

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [PreconnectedSpace M]
  {F : ContinuousFinslerNorm E M}

private theorem exists_centered_return_estimate_on_core
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace) (initial terminal : M)
    {u : M → ℝ} (hu : let _instLowerReturnLip : MetricSpace M := F.metricSpace
      LipschitzWith 1 u)
    {S P : Set E} (hS : S ⊆ (extChartAt 𝓘(ℝ, E) initial).target)
    {Γ : E → ℝ → M} {x₀ : E} (hx₀ : x₀ ∈ S) {δ t : ℝ} (hδ : 0 < δ)
    (ht : t ∈ Icc (-δ) δ)
    (hEL : ∀ x ∈ S, F.IsEulerLagrangeOn (Γ x) univ)
    (hinit : ∀ x ∈ S, Γ x 0 = (extChartAt 𝓘(ℝ, E) initial).symm x)
    (hsource : ∀ x ∈ S, Γ x t ∈ (extChartAt 𝓘(ℝ, E) terminal).source)
    (hunit : ∀ x ∈ S,
      F.toFun (tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (Γ x) ⟨t, (1 : ℝ)⟩) = 1)
    (hiso : let _instLowerReturnIso : MetricSpace M := F.metricSpace
      ∀ x ∈ S, Isometry (fun s : Icc (-δ) δ ↦ Γ x s))
    (hsat : ∀ x ∈ S, u (Γ x δ) - u (Γ x (-δ)) = δ - (-δ))
    {H : E → ℝ} {L : ℝ≥0} (hH : ContDiff ℝ 1 H)
    (hLip : LipschitzWith L (fderiv ℝ H))
    (hmatch : EqOn (fderiv ℝ H)
      (fderiv ℝ (u ∘ (extChartAt 𝓘(ℝ, E) terminal).symm)) P)
    (hdu : ∀ z ∈ P,
      MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ) u ((extChartAt 𝓘(ℝ, E) terminal).symm z))
    {v₀ : E} (hz₀ : (extChartAt 𝓘(ℝ, E) terminal (Γ x₀ t), v₀) ∈
      chartEnergyDomain terminal)
    (hp₀ : fiberLegendre (F.chartEnergy terminal)
      (extChartAt 𝓘(ℝ, E) terminal (Γ x₀ t), v₀) =
        fderiv ℝ H (extChartAt 𝓘(ℝ, E) terminal (Γ x₀ t)))
    (hxP : extChartAt 𝓘(ℝ, E) terminal (Γ x₀ t) ∈ P) :
    ∃ (ε : ℝ) (C : ℝ≥0), 0 < ε ∧ ∀ x ∈ S,
      extChartAt 𝓘(ℝ, E) terminal (Γ x t) ∈ P →
      extChartAt 𝓘(ℝ, E) terminal (Γ x t) ∈
        closedBall (extChartAt 𝓘(ℝ, E) terminal (Γ x₀ t)) ε →
      ‖x - x₀‖ ≤ C * ‖extChartAt 𝓘(ℝ, E) terminal (Γ x t) -
        extChartAt 𝓘(ℝ, E) terminal (Γ x₀ t)‖ := by
  let T : E → E := fun x ↦ extChartAt 𝓘(ℝ, E) terminal (Γ x t)
  obtain ⟨R, τ, Λ, hR, _, hball, hi, _, _⟩ :=
    hF.exists_C11_short_geodesic_translation hcomplete terminal hH hLip hz₀ hp₀
  have hΛEL : ∀ z ∈ ball (T x₀) R, F.IsEulerLagrangeOn (Λ z) univ :=
    fun z hz ↦ (hi z (ball_subset_closedBall hz)).2.1
  have hΛinit : ∀ z ∈ ball (T x₀) R,
      Λ z 0 = (extChartAt 𝓘(ℝ, E) terminal).symm z :=
    fun z hz ↦ (hi z (ball_subset_closedBall hz)).1
  have hΛp : ∀ z ∈ ball (T x₀) R,
      F.chartMomentumFamily terminal Λ (z, 0) = (z, fderiv ℝ H z) :=
    fun z hz ↦ (hi z (ball_subset_closedBall hz)).2.2.2
  have hreturn (x : E) (hx : x ∈ S) (hxP : T x ∈ P)
      (hxR : T x ∈ ball (T x₀) R) :
      Λ (T x) (-t) = (extChartAt 𝓘(ℝ, E) initial).symm x := by
    have hback : (extChartAt 𝓘(ℝ, E) terminal).symm (T x) = Γ x t :=
      (extChartAt 𝓘(ℝ, E) terminal).left_inv (hsource x hx)
    have hd : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ) u (Γ x t) := by
      rw [← hback]
      exact hdu (T x) hxP
    have hp : eulerLagrangePhaseLift (F.chartEnergy terminal)
        (extChartAt 𝓘(ℝ, E) terminal ∘ Λ (T x)) 0 =
          (T x, fderiv ℝ (u ∘ (extChartAt 𝓘(ℝ, E) terminal).symm) (T x)) := by
      exact (hΛp (T x) hxR).trans (Prod.ext rfl (hmatch hxP))
    exact (hF.eq_timeShift_of_chartMomentum_at_calibrated_point terminal hu
      (hEL x hx) (hΛEL (T x) hxR) (by linarith) (hiso x hx) (hsat x hx) ht
      (hunit x hx) hd (hsource x hx) ((hΛinit (T x) hxR).trans hback) hp).2.trans
        (hinit x hx)
  have hxR : T x₀ ∈ ball (T x₀) R := mem_ball_self hR
  have hlegal : Λ (T x₀) (-t) ∈ (extChartAt 𝓘(ℝ, E) initial).source := by
    rw [hreturn x₀ hx₀ hxP hxR]
    exact (extChartAt 𝓘(ℝ, E) initial).map_target (hS hx₀)
  obtain ⟨ε, C, hε, hεR, _, hread⟩ :=
    hF.exists_lipschitz_chart_readout_of_C11_initial_momentum hcomplete terminal hH hLip
      isOpen_ball (fun _ hz ↦ hball (ball_subset_closedBall hz)) hΛEL hΛinit hΛp
      hxR initial (-t) hlegal
  refine ⟨ε, C, hε, fun x hx hxpiece hxε ↦ ?_⟩
  have hh := hread.dist_le_mul (T x) hxε (T x₀) (mem_closedBall_self hε.le)
  rw [hreturn x hx hxpiece (hεR hxε), hreturn x₀ hx₀ hxP (hεR
    (mem_closedBall_self hε.le)), (extChartAt 𝓘(ℝ, E) initial).right_inv (hS hx),
    (extChartAt 𝓘(ℝ, E) initial).right_inv (hS hx₀)] at hh
  simpa only [dist_eq_norm] using hh


/-- A genuine calibrated C1,1 geodesic translation has a positive centered local
lower bound at every time strictly inside its uniform calibrated interval. Target
C1,1 pieces and actual backward families are constructed from the original geometry;
no target-piece regularity or derivative-rank assumption is supplied. -/
theorem exists_centered_lower_bound_of_calibrated_C11_translation
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace) (initial terminal : M)
    {K U : Set E} (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U)
    (hUt : U ⊆ (extChartAt 𝓘(ℝ, E) initial).target)
    {u : M → ℝ} (hu : let _instCenteredLowerLip : MetricSpace M := F.metricSpace
      LipschitzWith 1 u)
    {G : E → ℝ} {L : ℝ≥0} (hG : ContDiff ℝ 1 G)
    (hLip : LipschitzWith L (fderiv ℝ G))
    (hmatch : EqOn (fderiv ℝ G)
      (fderiv ℝ (u ∘ (extChartAt 𝓘(ℝ, E) initial).symm)) K)
    {Γ : E → ℝ → M} (hEL : ∀ x ∈ U, F.IsEulerLagrangeOn (Γ x) univ)
    (hinit : ∀ x ∈ U, Γ x 0 = (extChartAt 𝓘(ℝ, E) initial).symm x)
    (hp : ∀ x ∈ U, F.chartMomentumFamily initial Γ (x, 0) = (x, fderiv ℝ G x))
    {δ : ℝ} (hδ : 0 < δ)
    (hpartners : let _instCenteredLowerPartners : MetricSpace M := F.metricSpace
      ∀ x ∈ K, ∃ a b : M,
        dist a ((extChartAt 𝓘(ℝ, E) initial).symm x) = δ ∧
        u ((extChartAt 𝓘(ℝ, E) initial).symm x) - u a = δ ∧
        dist ((extChartAt 𝓘(ℝ, E) initial).symm x) b = δ ∧
        u b - u ((extChartAt 𝓘(ℝ, E) initial).symm x) = δ)
    {x₀ : E} (hx₀ : x₀ ∈ K) {t : ℝ} (ht : |t| < δ)
    (hlegal : Γ x₀ t ∈ (extChartAt 𝓘(ℝ, E) terminal).source) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ x in 𝓝[K] x₀,
      Γ x t ∈ (extChartAt 𝓘(ℝ, E) terminal).source ∧
      c * ‖x - x₀‖ ≤ ‖extChartAt 𝓘(ℝ, E) terminal (Γ x t) -
        extChartAt 𝓘(ℝ, E) terminal (Γ x₀ t)‖ := by
  classical
  let _instCenteredLowerMetric : MetricSpace M := F.metricSpace
  have hd : ∀ x ∈ K, MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ) u
      ((extChartAt 𝓘(ℝ, E) initial).symm x) := by
    intro x hx
    obtain ⟨a, b, hax, ha, hxb, hb⟩ := hpartners x hx
    apply hF.mdifferentiableAt_of_mem_calibratedInterior hcomplete hu
    exact ⟨⟨a, dist_pos.mp (hax.symm ▸ hδ), ha.trans hax.symm⟩,
      ⟨b, dist_pos.mp (hxb.symm ▸ hδ), hb.trans hxb.symm⟩⟩
  have hcal : ∀ x ∈ K,
      (∀ s : ℝ, F.toFun (tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (Γ x) ⟨s, (1 : ℝ)⟩) = 1) ∧
      (∀ s ∈ Icc (-δ) δ, u (Γ x s) = u (Γ x 0) + s) ∧
      Isometry (fun s : Icc (-δ) δ ↦ Γ x s) := by
    intro x hx
    obtain ⟨a, b, hax, ha, hxb, hb⟩ := hpartners x hx
    have hpx : F.chartMomentumFamily initial Γ (x, 0) =
        (x, fderiv ℝ (u ∘ (extChartAt 𝓘(ℝ, E) initial).symm) x) :=
      (hp x (hKU hx)).trans (Prod.ext rfl (hmatch hx))
    obtain ⟨hunit, _, _, hclock, hiso, _⟩ :=
      hF.calibrated_translation_of_chartMomentum hcomplete initial hu (hUt (hKU hx))
        (hEL x (hKU hx)) (hinit x (hKU hx)) hpx (hd x hx) hδ ⟨hax, ha⟩ ⟨hxb, hb⟩
    exact ⟨hunit, fun s hs ↦ by rw [hinit x (hKU hx)]; exact hclock s hs, hiso⟩
  obtain ⟨r₀, C₀, hr₀, hballU, hmap, hTLip⟩ :=
    hF.exists_lipschitz_chart_readout_of_C11_initial_momentum hcomplete initial hG hLip
      hU hUt hEL hinit hp (hKU hx₀) terminal t hlegal
  let T : E → E := fun x ↦ extChartAt 𝓘(ℝ, E) terminal (Γ x t)
  let S := K ∩ closedBall x₀ r₀
  let Q := T '' S
  have hxS : x₀ ∈ S := ⟨hx₀, mem_closedBall_self hr₀.le⟩
  have hScompact : IsCompact S := hK.inter_right isClosed_closedBall
  have hTcont : ContinuousOn T S := hTLip.continuousOn.mono inter_subset_right
  have hQcompact : IsCompact Q := hScompact.image_of_continuousOn hTcont
  have hQt : Q ⊆ (extChartAt 𝓘(ℝ, E) terminal).target := by
    rintro z ⟨x, hx, rfl⟩
    exact (extChartAt 𝓘(ℝ, E) terminal).map_source (hmap hx.2)
  let η := (δ - |t|) / 2
  have hη : 0 < η := by dsimp [η]; linarith
  have hreachQ : ∀ z ∈ Q, ∃ a b : M,
      dist a ((extChartAt 𝓘(ℝ, E) terminal).symm z) = η ∧
      u ((extChartAt 𝓘(ℝ, E) terminal).symm z) - u a = η ∧
      dist ((extChartAt 𝓘(ℝ, E) terminal).symm z) b = η ∧
      u b - u ((extChartAt 𝓘(ℝ, E) terminal).symm z) = η := by
    rintro z ⟨x, hx, rfl⟩
    change ∃ a b, dist a ((extChartAt 𝓘(ℝ, E) terminal).symm
      (extChartAt 𝓘(ℝ, E) terminal (Γ x t))) = η ∧ _
    rw [(extChartAt 𝓘(ℝ, E) terminal).left_inv (hmap hx.2)]
    exact (lowerBound_shifted_calibrated_partners (hcal x hx.1).2.1
      (hcal x hx.1).2.2 ht).2
  have hdQ : ∀ z ∈ Q, MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ) u
      ((extChartAt 𝓘(ℝ, E) terminal).symm z) := by
    intro z hz
    obtain ⟨a, b, hax, ha, hxb, hb⟩ := hreachQ z hz
    apply hF.mdifferentiableAt_of_mem_calibratedInterior hcomplete hu
    exact ⟨⟨a, dist_pos.mp (hax.symm ▸ hη), ha.trans hax.symm⟩,
      ⟨b, dist_pos.mp (hxb.symm ▸ hη), hb.trans hxb.symm⟩⟩
  have hforwardQ : ∀ z ∈ Q, ∃ b : M,
      (extChartAt 𝓘(ℝ, E) terminal).symm z ≠ b ∧
      u b - u ((extChartAt 𝓘(ℝ, E) terminal).symm z) =
        dist ((extChartAt 𝓘(ℝ, E) terminal).symm z) b := by
    intro z hz
    obtain ⟨a, b, _, _, hxb, hb⟩ := hreachQ z hz
    exact ⟨b, dist_pos.mp (hxb.symm ▸ hη), hb.trans hxb.symm⟩
  have hunitQ := hF.chart_unit_legendre_on_of_calibrated_endpoints
    hcomplete terminal hQt hu hdQ hforwardQ
  obtain ⟨r, _, J, hcover, hpieces⟩ :=
    hF.exists_finite_calibrated_C11_cover hcomplete terminal hQcompact hQt hη hu hreachQ
  let P : ↥J → Set E := fun j ↦ Q ∩ closedBall (j : E) (r / 8)
  have hclosed : ∀ j, IsClosed (P j) := fun j ↦ (hpieces j j.property).1.isClosed
  have hcoverS : ∀ᶠ x in 𝓝[S] x₀, ∃ j : ↥J, T x ∈ P j := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    have hxQ : T x ∈ Q := mem_image_of_mem T hx
    obtain ⟨j, hj, hxj⟩ := mem_iUnion₂.mp (hcover hxQ)
    exact ⟨⟨j, hj⟩, hxQ, hxj⟩
  have hbound : ∀ j : ↥J, T x₀ ∈ P j → ∃ C : ℝ, 0 ≤ C ∧
      ∀ᶠ x in 𝓝[S] x₀, T x ∈ P j → ‖x - x₀‖ ≤ C * ‖T x - T x₀‖ := by
    intro j hxj
    obtain ⟨_, H, D, hH, _, _, hD, _, hmatching, _⟩ := hpieces j j.property
    obtain ⟨v₀, hv₀, hp₀, _⟩ := hunitQ (T x₀) hxj.1
    have htI : t ∈ Icc (-δ) δ :=
      ⟨(neg_lt_of_abs_lt ht).le, (lt_of_abs_lt ht).le⟩
    have hsat : ∀ x ∈ S, u (Γ x δ) - u (Γ x (-δ)) = δ - (-δ) := by
      intro x hx
      rw [(hcal x hx.1).2.1 δ ⟨by linarith, le_rfl⟩,
        (hcal x hx.1).2.1 (-δ) ⟨le_rfl, by linarith⟩]
      ring
    obtain ⟨ε, C, hε, hreturn⟩ := exists_centered_return_estimate_on_core hF hcomplete
      initial terminal hu (fun _ hx ↦ hUt (hKU hx.1)) hxS hδ htI
      (fun x hx ↦ hEL x (hKU hx.1)) (fun x hx ↦ hinit x (hKU hx.1))
      (fun _ hx ↦ hmap hx.2) (fun x hx ↦ (hcal x hx.1).1 t)
      (fun x hx ↦ (hcal x hx.1).2.2) hsat hH hD hmatching
      (fun z hz ↦ hdQ z hz.1) hv₀ (hp₀.trans (hmatching hxj).symm) hxj
    refine ⟨C, C.coe_nonneg, ?_⟩
    have hnear : ∀ᶠ x in 𝓝[S] x₀, T x ∈ closedBall (T x₀) ε :=
      (hTcont x₀ hxS).eventually (closedBall_mem_nhds _ hε)
    filter_upwards [self_mem_nhdsWithin, hnear] with x hx hxε
    exact fun hxj ↦ hreturn x hx hxj hxε
  obtain ⟨c, hc, hlower⟩ :=
    exists_pos_eventually_norm_sub_le_of_finite_closed_cover P hclosed (hTcont x₀ hxS)
      hcoverS hbound
  have hfilter : 𝓝[K] x₀ = 𝓝[S] x₀ := by
    exact (nhdsWithin_inter_of_mem' (mem_nhdsWithin_of_mem_nhds
      (closedBall_mem_nhds x₀ hr₀))).symm
  refine ⟨c, hc, ?_⟩
  rw [hfilter]
  filter_upwards [self_mem_nhdsWithin, hlower] with x hx hxlower
  exact ⟨hmap hx.2, hxlower⟩

end ContinuousFinslerNorm.IsSmoothStronglyConvex
end OTSelector.Geometry

end
end
