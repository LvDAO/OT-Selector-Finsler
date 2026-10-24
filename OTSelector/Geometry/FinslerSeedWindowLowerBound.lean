import OTSelector.Geometry.Finsler.CalibratedLowerBound
import OTSelector.Transport.Kantorovich.CalibratedEndpointWindow

/-!
# Actual reverse-flow bounds inside calibrated seed windows

Compact original calibrated families have positive centered inverse bounds at every
interior time. Genuine target C1,1 pieces construct their reverse flows, and a finite
closed cover combines the resulting estimates. The label space and the two endpoint
times are arbitrary; an initial section estimate recovers the original labels.
-/

open Set Filter Metric Manifold Bundle
open scoped Topology ContDiff NNReal

noncomputable section
namespace OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

variable {E W M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup W] [NormedSpace ℝ W]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] {F : ContinuousFinslerNorm E M}

omit [NormedAddCommGroup W] [NormedSpace ℝ W] in
private theorem exists_centered_return_estimate_of_calibrated_window
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace) (initial terminal : M)
    {u : M → ℝ} (hu : let _instLowerReturnLip : MetricSpace M := F.metricSpace
      LipschitzWith 1 u)
    {S : Set W} {P : Set E} {σ : W → E}
    (hS : MapsTo σ S (extChartAt 𝓘(ℝ, E) initial).target)
    {Γ : W → ℝ → M} {x₀ : W} (hx₀ : x₀ ∈ S) {a b t : ℝ}
    (hab : a < b) (ht : t ∈ Icc a b)
    (hEL : ∀ x ∈ S, F.IsEulerLagrangeOn (Γ x) univ)
    (hinit : ∀ x ∈ S, Γ x 0 = (extChartAt 𝓘(ℝ, E) initial).symm (σ x))
    (hsource : ∀ x ∈ S, Γ x t ∈ (extChartAt 𝓘(ℝ, E) terminal).source)
    (hunit : ∀ x ∈ S,
      F.toFun (tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (Γ x) ⟨t, (1 : ℝ)⟩) = 1)
    (hiso : let _instLowerReturnIso : MetricSpace M := F.metricSpace
      ∀ x ∈ S, Isometry (fun s : Icc a b ↦ Γ x s))
    (hsat : ∀ x ∈ S, u (Γ x b) - u (Γ x a) = b - a)
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
      ‖σ x - σ x₀‖ ≤ C * ‖extChartAt 𝓘(ℝ, E) terminal (Γ x t) -
        extChartAt 𝓘(ℝ, E) terminal (Γ x₀ t)‖ := by
  let T : W → E := fun x ↦ extChartAt 𝓘(ℝ, E) terminal (Γ x t)
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
  have hreturn (x : W) (hx : x ∈ S) (hxP : T x ∈ P)
      (hxR : T x ∈ ball (T x₀) R) :
      Λ (T x) (-t) = (extChartAt 𝓘(ℝ, E) initial).symm (σ x) := by
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
      (hEL x hx) (hΛEL (T x) hxR) hab (hiso x hx) (hsat x hx) ht
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

omit [NormedSpace ℝ W] in
/-- Actual compact calibrated families inherit a centered inverse bound at every
interior time, from their original initial section bound. -/
theorem exists_centered_lower_bound_of_compact_calibrated_window
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace) (initial terminal : M)
    {u : M → ℝ} (hu : let _instCompactWindowLip : MetricSpace M := F.metricSpace
      LipschitzWith 1 u)
    {K : Set W} (hK : IsCompact K) {w₀ : W} (hw₀ : w₀ ∈ K)
    {σ : W → E} (hσtarget : MapsTo σ K (extChartAt 𝓘(ℝ, E) initial).target)
    {C₀ : ℝ} (hC₀ : 0 ≤ C₀)
    (hσlower : ∀ w ∈ K, ‖w - w₀‖ ≤ C₀ * ‖σ w - σ w₀‖)
    {Γ : W → ℝ → M} {a b t q : ℝ} (ht : t ∈ Ioo a b)
    (hEL : ∀ w ∈ K, F.IsEulerLagrangeOn (Γ w) univ)
    (hinit : ∀ w ∈ K, Γ w 0 = (extChartAt 𝓘(ℝ, E) initial).symm (σ w))
    (hsource : ∀ w ∈ K, Γ w t ∈ (extChartAt 𝓘(ℝ, E) terminal).source)
    (hunit : ∀ w ∈ K,
      F.toFun (tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (Γ w) ⟨t, (1 : ℝ)⟩) = 1)
    (hiso : let _instCompactWindowIso : MetricSpace M := F.metricSpace
      ∀ w ∈ K, Isometry (fun s : Icc a b ↦ Γ w s))
    (hclock : ∀ w ∈ K, ∀ s ∈ Icc a b, u (Γ w s) = q + s)
    (hT : ContinuousOn (fun w ↦ extChartAt 𝓘(ℝ, E) terminal (Γ w t)) K) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ w in 𝓝[K] w₀,
      c * ‖w - w₀‖ ≤ ‖extChartAt 𝓘(ℝ, E) terminal (Γ w t) -
        extChartAt 𝓘(ℝ, E) terminal (Γ w₀ t)‖ := by
  classical
  let _instCompactWindowMetric : MetricSpace M := F.metricSpace
  let T : W → E := fun w ↦ extChartAt 𝓘(ℝ, E) terminal (Γ w t)
  let Q := T '' K
  have hQcompact : IsCompact Q := hK.image_of_continuousOn hT
  have hQt : Q ⊆ (extChartAt 𝓘(ℝ, E) terminal).target := by
    rintro z ⟨w, hw, rfl⟩
    exact (extChartAt 𝓘(ℝ, E) terminal).map_source (hsource w hw)
  let η := min (t - a) (b - t) / 2
  have hη : 0 < η := div_pos (lt_min (sub_pos.mpr ht.1) (sub_pos.mpr ht.2))
    (by norm_num)
  have hseg : Icc (t - η) (t + η) ⊆ Icc a b := by
    intro s hs
    have hleft := min_le_left (t - a) (b - t)
    have hright := min_le_right (t - a) (b - t)
    dsimp only [η] at hs
    constructor <;> linarith [hs.1, hs.2]
  have hreachQ : ∀ z ∈ Q, ∃ l r : M,
      dist l ((extChartAt 𝓘(ℝ, E) terminal).symm z) = η ∧
      u ((extChartAt 𝓘(ℝ, E) terminal).symm z) - u l = η ∧
      dist ((extChartAt 𝓘(ℝ, E) terminal).symm z) r = η ∧
      u r - u ((extChartAt 𝓘(ℝ, E) terminal).symm z) = η := by
    rintro z ⟨w, hw, rfl⟩
    change ∃ l r, dist l ((extChartAt 𝓘(ℝ, E) terminal).symm
      (extChartAt 𝓘(ℝ, E) terminal (Γ w t))) = η ∧ _
    rw [(extChartAt 𝓘(ℝ, E) terminal).left_inv (hsource w hw)]
    obtain ⟨⟨r, hr, hur⟩, ⟨l, hl, hul⟩⟩ :=
      mem_two_sided_calibratedReach_of_isometry (hiso w hw) (hclock w hw) hη.le hseg
    refine ⟨l, r, ?_, ?_, hr, hur⟩
    · simpa only [dist_comm] using hl
    · simpa only [Pi.neg_apply, neg_sub_neg] using hul
  have hdQ : ∀ z ∈ Q, MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ) u
      ((extChartAt 𝓘(ℝ, E) terminal).symm z) := by
    intro z hz
    obtain ⟨l, r, hl, hul, hr, hur⟩ := hreachQ z hz
    apply hF.mdifferentiableAt_of_mem_calibratedInterior hcomplete hu
    exact ⟨⟨l, dist_pos.mp (hl.symm ▸ hη), hul.trans hl.symm⟩,
      ⟨r, dist_pos.mp (hr.symm ▸ hη), hur.trans hr.symm⟩⟩
  have hforwardQ : ∀ z ∈ Q, ∃ r : M,
      (extChartAt 𝓘(ℝ, E) terminal).symm z ≠ r ∧
      u r - u ((extChartAt 𝓘(ℝ, E) terminal).symm z) =
        dist ((extChartAt 𝓘(ℝ, E) terminal).symm z) r := by
    intro z hz
    obtain ⟨_, r, _, _, hr, hur⟩ := hreachQ z hz
    exact ⟨r, dist_pos.mp (hr.symm ▸ hη), hur.trans hr.symm⟩
  have hunitQ := hF.chart_unit_legendre_on_of_calibrated_endpoints
    hcomplete terminal hQt hu hdQ hforwardQ
  obtain ⟨r, _, J, hcover, hpieces⟩ :=
    hF.exists_finite_calibrated_C11_cover hcomplete terminal hQcompact hQt hη hu hreachQ
  let P : ↥J → Set E := fun j ↦ Q ∩ closedBall (j : E) (r / 8)
  have hclosed : ∀ j, IsClosed (P j) := fun j ↦ (hpieces j j.property).1.isClosed
  have hcoverK : ∀ᶠ w in 𝓝[K] w₀, ∃ j : ↥J, T w ∈ P j := by
    filter_upwards [self_mem_nhdsWithin] with w hw
    have hwQ : T w ∈ Q := mem_image_of_mem T hw
    obtain ⟨j, hj, hwj⟩ := mem_iUnion₂.mp (hcover hwQ)
    exact ⟨⟨j, hj⟩, hwQ, hwj⟩
  have hbound : ∀ j : ↥J, T w₀ ∈ P j → ∃ C : ℝ, 0 ≤ C ∧
      ∀ᶠ w in 𝓝[K] w₀, T w ∈ P j → ‖w - w₀‖ ≤ C * ‖T w - T w₀‖ := by
    intro j hwj
    obtain ⟨_, H, L, hH, _, _, hL, _, hmatching, _⟩ := hpieces j j.property
    obtain ⟨v₀, hv₀, hp₀, _⟩ := hunitQ (T w₀) hwj.1
    have hsat : ∀ w ∈ K, u (Γ w b) - u (Γ w a) = b - a := by
      intro w hw
      rw [hclock w hw b ⟨ht.1.le.trans ht.2.le, le_rfl⟩,
        hclock w hw a ⟨le_rfl, ht.1.le.trans ht.2.le⟩]
      ring
    obtain ⟨ε, C, hε, hreturn⟩ :=
      exists_centered_return_estimate_of_calibrated_window hF hcomplete initial terminal hu
        hσtarget hw₀ (ht.1.trans ht.2) ⟨ht.1.le, ht.2.le⟩ hEL hinit hsource hunit
        hiso hsat hH hL hmatching (fun z hz ↦ hdQ z hz.1)
        hv₀ (hp₀.trans (hmatching hwj).symm) hwj
    refine ⟨C₀ * C, mul_nonneg hC₀ C.coe_nonneg, ?_⟩
    have hnear : ∀ᶠ w in 𝓝[K] w₀, T w ∈ closedBall (T w₀) ε :=
      (hT w₀ hw₀).eventually (closedBall_mem_nhds _ hε)
    filter_upwards [self_mem_nhdsWithin, hnear] with w hw hwε hwj
    calc
      ‖w - w₀‖ ≤ C₀ * ‖σ w - σ w₀‖ := hσlower w hw
      _ ≤ C₀ * ((C : ℝ) * ‖T w - T w₀‖) :=
        mul_le_mul_of_nonneg_left (hreturn w hw hwj hwε) hC₀
      _ = (C₀ * C) * ‖T w - T w₀‖ := (mul_assoc _ _ _).symm
  exact exists_pos_eventually_norm_sub_le_of_finite_closed_cover P hclosed (hT w₀ hw₀)
    hcoverK hbound

end OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex
