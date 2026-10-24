import OTSelector.Reconstruction.MarkedStationaryValueLegalOptimalClockCarrier
import OTSelector.Reconstruction.MarkedStationaryValueLegalOptimalRootedTail

/-!
# Actual compact target cutoffs for rooted legal optimal plans

The original closed clock carriers survive rooting. A bounded source position
and a bounded full displacement therefore put the target in an explicit compact
spatial-clock set. Its escape estimate uses the same original legal optimum.
-/
open Set Function MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace Metric
open scoped ENNReal NNReal
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
local instance markedStationaryValueLegalOptimalCompactEscapeLocalPolish (q : ℕ) : PolishSpace
    (LocalFiniteMeasure (LegalMarkedPhysicalEdge q)) := LocalFiniteMeasure.instPolishSpace

/-- A bounded source and an original retained target clock turn compact target
escape into an actual full-displacement tail. -/
theorem measure_legalMarked_sourceWindow_target_escape_le_long
    (q : ℕ) (Γ : Measure (LegalMarkedPhysicalEdge q))
    {U : Set (Fin q → ℝ)} {J : Set ℝ} {b R : ℝ}
    (hU : ∀ x ∈ U, ‖x‖ ≤ b) (hclock : ∀ᵐ e ∂Γ, e.2.2 ∈ J) :
    Γ {e | e.1.1 ∈ U ∧ e.2 ∉ closedBall (0 : Fin q → ℝ) (b + R) ×ˢ J} ≤
      Γ {e | e.1.1 ∈ U ∧ R ≤ ‖e.2.1 - e.1.1‖} := by
  apply measure_mono_ae
  filter_upwards [hclock] with e he hp
  refine ⟨hp.1, ?_⟩
  have hfar : b + R < ‖e.2.1‖ := by
    by_contra hn
    apply hp.2
    refine ⟨?_, he⟩
    simpa only [mem_closedBall, dist_zero_right] using le_of_not_gt hn
  have htri : ‖e.2.1‖ ≤ ‖e.2.1 - e.1.1‖ + ‖e.1.1‖ := by
    simpa only [sub_add_cancel] using norm_add_le (e.2.1 - e.1.1) e.1.1
  linarith [hU e.1.1 hp.1]

/-- Original independent clock carrying, not any selected-point law, supplies
the exact zero clock escape event of the actual rooted optimum. -/
theorem ae_clock_carriers_legalMarkedOptimalRootedSceneLaw
    (q : ℕ) (hq : 0 < q)
    (α β : Measure ℝ) [IsProbabilityMeasure α] [IsProbabilityMeasure β]
    (kin : ℝ → ℝ → (Fin q → ℝ) → ℝ)
    (hk : Measurable (Function.uncurry (fun p : ℝ × ℝ ↦ kin p.1 p.2)))
    (g : ℝ → ℝ → ℝ) (hg : Measurable (Function.uncurry g)) (t L : ℝ) (hL : 0 < L)
    {A B : Set ℝ} (hA : IsClosed A) (hB : IsClosed B)
    (hα : α Aᶜ = 0) (hβ : β Bᶜ = 0) :
    ∀ᵐ scene ∂(legalMarkedOptimalRootedSceneLaw q hq α β kin hk g hg t L hL : Measure
      (CavityLocalScene (LegalMarkedPhysicalPoint q) (LegalMarkedPhysicalPoint q))),
      ∀ᵐ e ∂(scene.1 : Measure (LegalMarkedPhysicalEdge q)), e.1.2 ∈ A ∧ e.2.2 ∈ B := by
  have hαae : ∀ᵐ a ∂α, a ∈ A := ae_iff.mpr hα
  have hβae : ∀ᵐ b ∂β, b ∈ B := ae_iff.mpr hβ
  have hpair : ∀ᵐ w ∂α.prod β, w ∈ A ×ˢ B :=
    (ae_fst_of_ae hαae).and (ae_snd_of_ae hβae)
  exact (ae_cubePalm_clockPair_mem_of_legalMarkedOptimalRootedSceneLaw_tendsto q hq α β
    kin hk g hg t (fun _ : ℕ ↦ L) (fun _ ↦ hL) tendsto_const_nhds (hA.prod hB) hpair).1

/-- Genuine original compact clocks, compact positive coefficients and the
actual legal pressure limit produce compact target cutoffs uniformly over all
large physical scales. No target-tail or selected-endpoint-law premise remains. -/
theorem exists_uniform_legalMarkedOptimalRootedSceneLaw_target_compact_bound
    (q : ℕ) (hq : 0 < q)
    (α β : Measure ℝ) [IsProbabilityMeasure α] [IsProbabilityMeasure β]
    {C G : ℝ} (hC : 0 ≤ C) (hG : 0 ≤ G)
    {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ}
    (hk : Measurable (Function.uncurry (fun p : ℝ × ℝ ↦ kin p.1 p.2)))
    (hkn : ∀ a b v, 0 ≤ kin a b v)
    (hkb : ∀ a b v, |kin a b v| ≤ C * ∑ l, v l ^ 2)
    (hhom : ∀ a b (c : ℝ), 0 ≤ c → ∀ v : Fin q → ℝ,
      kin a b (fun l ↦ c * v l) = c ^ 2 * kin a b v)
    {g : ℝ → ℝ → ℝ} (hg : Measurable (Function.uncurry g))
    (hgb : ∀ a b, |g a b| ≤ G) (t p : ℝ)
    (hp : Tendsto (fun L ↦ legalMarkedScalePressure q id id α β kin g L t) atTop (𝓝 p))
    {A B : Set ℝ} (hA : IsCompact A) (hB : IsCompact B)
    (hα : α Aᶜ = 0) (hβ : β Bᶜ = 0)
    {K : Set (ℝ × ℝ)} (hK : IsCompact K)
    (matrix : (ℝ × ℝ) → Matrix (Fin q) (Fin q) ℝ)
    (hmatrix : ContinuousOn matrix K) (hpos : ∀ w ∈ K, (matrix w).PosDef)
    (hlegal : ∀ a ∈ A, ∀ b ∈ B, a < b → (a, b) ∈ K)
    (hactual : ∀ w ∈ K, ∀ v, kin w.1 w.2 v = matrixQuadratic (matrix w) v)
    {U : Set (Fin q → ℝ)} (hU : MeasurableSet U) (hUfin : volume U ≠ ∞)
    {b : ℝ} (hbounded : ∀ x ∈ U, ‖x‖ ≤ b) :
    ∃ L₀ : ℝ, ∀ ε : ℝ≥0∞, 0 < ε →
      ∃ T : Set (LegalMarkedPhysicalPoint q), IsCompact T ∧
        ∀ L : ℝ, ∀ hL : 0 < L, L₀ ≤ L →
          (∫⁻ scene, (scene.1 : Measure (LegalMarkedPhysicalEdge q))
            {e | e.1.1 ∈ U ∧ e.2 ∉ T}
            ∂(legalMarkedOptimalRootedSceneLaw q hq α β kin hk g hg t L hL : Measure
              (CavityLocalScene (LegalMarkedPhysicalPoint q) (LegalMarkedPhysicalPoint q)))) ≤ ε := by
  obtain ⟨L₀, hlong⟩ := exists_uniform_legalMarkedOptimalRootedSceneLaw_long_bound q hq α β
    hC hG hk hkn hkb hhom hg hgb t p hp hA.measurableSet hB.measurableSet hα hβ
    hK matrix hmatrix hpos hlegal hactual hU hUfin
  refine ⟨L₀, fun ε hε ↦ ?_⟩
  obtain ⟨R, hR, hbound⟩ := hlong ε hε
  refine ⟨closedBall (0 : Fin q → ℝ) (b + R) ×ˢ B,
    (isCompact_closedBall 0 (b + R)).prod hB, fun L hL hlarge ↦ ?_⟩
  apply (lintegral_mono_ae ?_).trans (hbound L hL hlarge)
  filter_upwards [ae_clock_carriers_legalMarkedOptimalRootedSceneLaw q hq α β kin hk
    g hg t L hL hA.isClosed hB.isClosed hα hβ] with scene hscene
  exact measure_legalMarked_sourceWindow_target_escape_le_long q _ hbounded (hscene.mono (fun e he ↦ he.2))

end OTSelector.Reconstruction
