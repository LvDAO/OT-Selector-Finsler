import OTSelector.Geometry.FinslerSeedEndpointGraphData
import OTSelector.Topology.Real.OpenTimeInterval
import OTSelector.Geometry.Finsler.SeedSupportEndpoints

/-!
# Actual endpoint charts in the original countable seed cover

Each endpoint uses a center from the original seed's coordinate cover. The same
complete comparison chooses its adapted clock there and retains one graph, phase
and regular-source bundle. Closed one-sided neighborhoods stay inside the original
chart ball, so they can use the simultaneous fixed-center conditional densities.
-/

open Set Filter Metric MeasureTheory Manifold
open scoped Topology ContDiff

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OTSelector.Geometry.ContinuousFinslerNorm

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}

/-- One endpoint graph retains an original countable chart center and its full ball
constraints, along with the same selected raw Jacobi and positive-speed source data. -/
structure SeedEndpointChart (S : CalibratedLevelSeedPatch F u)
    {initial : M} {t₀ : ℝ} {w : S.covector.ker} {z₀ : E × (E →L[ℝ] ℝ)}
    {R : S.covector.ker →L[ℝ] E} {Q : S.covector.ker →L[ℝ] E →L[ℝ] ℝ}
    (C : F.SmoothPhaseJetComparison initial t₀ w z₀ R Q) (t : ℝ) where
  center : S.centers
  label_mem : w ∈ ball center.1.2 (S.radius center)
  time_mem : t ∈ ball center.1.1 (S.radius center)
  A : E ≃L[ℝ] (ℝ ×
    (F.chartMomentumFamily (S.curve center.1.2 center.1.1) C.curve (w, t)).2.ker)
  velocity : A (deriv
    (extChartAt 𝓘(ℝ, E) (S.curve center.1.2 center.1.1) ∘ C.curve w) t) = (1, 0)
  geometry : EndpointGraphData F A C.curve C.labels w (S.curve center.1.2 center.1.1) t
  within_ball : ∀ q ∈ geometry.U, (q.2, q.1) ∈ ball center.1 (S.radius center)

namespace SeedEndpointChart

variable {S : CalibratedLevelSeedPatch F u}
  {initial : M} {t₀ : ℝ} {w : S.covector.ker} {z₀ : E × (E →L[ℝ] ℝ)}
  {R : S.covector.ker →L[ℝ] E} {Q : S.covector.ker →L[ℝ] E →L[ℝ] ℝ}
  {C : F.SmoothPhaseJetComparison initial t₀ w z₀ R Q} {t : ℝ}

omit [BorelSpace E] in
/-- The original parameter normalization identifies the endpoint spatial dimension
with the fixed original label dimension. -/
theorem spatial_finrank_eq (G : SeedEndpointChart S C t) :
    Module.finrank ℝ S.covector.ker = Module.finrank ℝ
      (F.chartMomentumFamily (S.curve G.center.1.2 G.center.1.1) C.curve (w, t)).2.ker := by
  have h := S.normalization.toLinearEquiv.finrank_eq.trans G.A.toLinearEquiv.finrank_eq
  simpa only [Module.finrank_prod, Module.finrank_self, Nat.add_left_cancel_iff] using h

/-- An actual endpoint spatial basis with exactly the original label indexing. -/
def spatialBasis {ι : Type*} (G : SeedEndpointChart S C t)
    (bW : Module.Basis ι ℝ S.covector.ker) :
    Module.Basis ι ℝ
      (F.chartMomentumFamily (S.curve G.center.1.2 G.center.1.1) C.curve (w, t)).2.ker :=
  bW.map (ContinuousLinearEquiv.ofFinrankEq G.spatial_finrank_eq).toLinearEquiv

omit [BorelSpace E] in
/-- Every central time in the selected source lies in the same original chart's
physical time ball used by the simultaneous conditional density formula. -/
theorem time_mem_ball_of_mem_source (G : SeedEndpointChart S C t) {s : ℝ}
    (hs : (w, s) ∈ G.geometry.U) : s ∈ ball G.center.1.1 (S.radius G.center) := by
  have h := G.within_ball (w, s) hs
  exact (max_lt_iff.mp
    (show max (dist s G.center.1.1) (dist w G.center.1.2) < S.radius G.center from h)).1

end SeedEndpointChart

namespace CalibratedLevelSeedPatch

omit [BorelSpace E] in
/-- At every finite endpoint, the original cover and actual comparison construct
an endpoint graph without a supplied chart, positive coordinate or source witness. -/
theorem nonempty_seedEndpointChart (S : CalibratedLevelSeedPatch F u)
    {initial : M} {t₀ : ℝ} {w : S.covector.ker} {z₀ : E × (E →L[ℝ] ℝ)}
    {R : S.covector.ker →L[ℝ] E} {Q : S.covector.ker →L[ℝ] E →L[ℝ] ℝ}
    (C : F.SmoothPhaseJetComparison initial t₀ w z₀ R Q)
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    (hcurve : S.curve w = C.curve w) (t : ℝ) :
    Nonempty (SeedEndpointChart S C t) := by
  have hcover : (t, w) ∈ ⋃ q ∈ S.centers, ball q (S.radius q) := by
    rw [S.local_cover]
    exact ⟨mem_univ _, S.labels_subset hw⟩
  obtain ⟨q, hq, hball⟩ := mem_iUnion₂.mp hcover
  let c : S.centers := ⟨q, hq⟩
  let old := S.curve q.2 q.1
  have hx : C.curve w t ∈ (extChartAt 𝓘(ℝ, E) old).source := by
    rw [← hcurve]
    exact (S.local_data q hq).2.2.1 (ball_subset_closedBall hball)
  have hz := (hF.chartTangent_of_isEulerLagrangeAt
    (C.complete w C.anchor_mem t (mem_univ _)) old hx).2
  obtain ⟨_, A, hAv, _, hpositive⟩ := hF.exists_positive_chartClock old hz
  let N : Set (S.covector.ker × ℝ) :=
    (fun p : S.covector.ker × ℝ ↦ (p.2, p.1)) ⁻¹' ball q (S.radius q)
  have hN : IsOpen N := isOpen_ball.preimage (continuous_snd.prodMk continuous_fst)
  obtain ⟨G, hGN⟩ := C.exists_endpointGraphData hF old A t hx hpositive hN hball
  have hballs : dist t q.1 < S.radius q ∧ dist w q.2 < S.radius q := by
    exact max_lt_iff.mp (show max (dist t q.1) (dist w q.2) < S.radius q from hball)
  exact ⟨{
    center := c
    label_mem := hballs.2
    time_mem := hballs.1
    A := A
    velocity := hAv
    geometry := G
    within_ball := hGN }⟩

omit [BorelSpace E] in
/-- The same complete comparison has actual left and right endpoint graph bundles,
with closed neighborhoods reaching the true endpoints inside their original chart balls. -/
theorem exists_seedEndpointCharts (S : CalibratedLevelSeedPatch F u)
    {initial : M} {t₀ : ℝ} {w : S.covector.ker} {z₀ : E × (E →L[ℝ] ℝ)}
    {R : S.covector.ker →L[ℝ] E} {Q : S.covector.ker →L[ℝ] E →L[ℝ] ℝ}
    (C : F.SmoothPhaseJetComparison initial t₀ w z₀ R Q)
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    (hcurve : S.curve w = C.curve w) {a b : ℝ} (hab : a < b) :
    ∃ (L : SeedEndpointChart S C a) (H : SeedEndpointChart S C b) (l h : ℝ),
      a < l ∧ l < b ∧ a < h ∧ h < b ∧
      (∀ t ∈ Icc a l, (w, t) ∈ L.geometry.U) ∧
      ∀ t ∈ Icc h b, (w, t) ∈ H.geometry.U := by
  obtain ⟨L⟩ := S.nonempty_seedEndpointChart C hF hw hcurve a
  obtain ⟨H⟩ := S.nonempty_seedEndpointChart C hF hw hcurve b
  obtain ⟨l, hal, hlb, hleft⟩ := exists_left_endpoint_interval_in_open_domain
    L.geometry.open_U L.geometry.anchor_U hab
  obtain ⟨h, hah, hhb, hright⟩ := exists_right_endpoint_interval_in_open_domain
    H.geometry.open_U H.geometry.anchor_U hab
  exact ⟨L, H, l, h, hal, hlb, hah, hhb, hleft, hright⟩

variable [T2Space M] [PreconnectedSpace M]

omit [BorelSpace E] in
/-- Compact conditional support produces its true finite endpoints and both actual
original-chart graph bundles of the same comparison, including closed physical windows. -/
theorem exists_compact_support_seedEndpointCharts (S : CalibratedLevelSeedPatch F u)
    {initial : M} {t₀ : ℝ} {w : S.covector.ker} {z₀ : E × (E →L[ℝ] ℝ)}
    {R : S.covector.ker →L[ℝ] E} {Q : S.covector.ker →L[ℝ] E →L[ℝ] ℝ}
    (C : F.SmoothPhaseJetComparison initial t₀ w z₀ R Q)
    (hF : F.IsSmoothStronglyConvex)
    (hu : let _instEndpointChartLip : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (hw : w ∈ S.labels) (hcurve : S.curve w = C.curve w)
    (μ : Measure ℝ) [NullSingletonClass μ] (hμ : μ ≠ 0)
    (hcompact : IsCompact μ.support) (u₀ : ℝ)
    (hclock : ∀ᵐ x ∂μ, x - u₀ ∈ S.calibrationTimes w) :
    ∃ a b : ℝ, a < b ∧ u₀ + a ∈ μ.support ∧ u₀ + b ∈ μ.support ∧
      (∀ x ∈ μ.support, x - u₀ ∈ Icc a b) ∧
      (∀ᵐ x ∂μ, x - u₀ ∈ Ioo a b) ∧ Icc a b ⊆ S.calibrationTimes w ∧
      ∃ (L : SeedEndpointChart S C a) (H : SeedEndpointChart S C b) (l h : ℝ),
        a < l ∧ l < b ∧ a < h ∧ h < b ∧
        (∀ t ∈ Icc a l, (w, t) ∈ L.geometry.U) ∧
        ∀ t ∈ Icc h b, (w, t) ∈ H.geometry.U := by
  obtain ⟨a, b, hab, ha, hb, hbound, hμinside, hspan, _, _⟩ :=
    S.exists_compact_support_calibrated_span hF hu hw μ hμ hcompact u₀ hclock
  exact ⟨a, b, hab, ha, hb, hbound, hμinside, hspan,
    S.exists_seedEndpointCharts C hF hw hcurve hab⟩

end CalibratedLevelSeedPatch
end OTSelector.Geometry.ContinuousFinslerNorm
