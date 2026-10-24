import OTSelector.Reconstruction.SeedEndpointJacobiDensity

/-!
# Physical population bounds in actual endpoint charts

Continuity of the original physical density supplies its bound on each compact
time interval of the actual complete seed. The original continuous chart density
of volume, multiplied by the fixed label Radon--Nikodym factor, supplies the
continuous nonnegative weight required by the endpoint moment construction.
-/

open Set MeasureTheory Manifold Metric OTSelector.Geometry
open scoped Topology ContDiff ENNReal NNReal

noncomputable section
namespace OTSelector.Reconstruction

set_option backward.isDefEq.respectTransparency false

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}

omit [BorelSpace E] [T2Space M] [PreconnectedSpace M]
  [MeasurableSpace M] [BorelSpace M] in
/-- An original continuous physical density is measurable along the complete seed
and bounded on every compact physical-time interval, including zeros and holes. -/
theorem populationSeed_density_on_interval (S : F.CalibratedLevelSeedPatch u)
    (hF : F.IsSmoothStronglyConvex) {w : S.covector.ker} (hw : w ∈ S.labels)
    {ρ : M → ℝ} (hρ : Continuous ρ) (hρ0 : ∀ x, 0 ≤ ρ x) (l h : ℝ) :
    Measurable (fun t ↦ ρ (S.curve w t)) ∧ ∃ Rρ : ℝ, 0 ≤ Rρ ∧
      ∀ t ∈ Icc l h, 0 ≤ ρ (S.curve w t) ∧ ρ (S.curve w t) ≤ Rρ := by
  have hc : Continuous (S.curve w) := continuous_iff_continuousAt.mpr fun t ↦
    (hF.contMDiffAt_of_isEulerLagrangeAt (S.complete w hw t (mem_univ _))).continuousAt
  have hd : Continuous (fun t ↦ ρ (S.curve w t)) := hρ.comp hc
  obtain ⟨Rρ, hRρ⟩ := isCompact_Icc.bddAbove_image hd.continuousOn
  refine ⟨hd.measurable, max Rρ 0, le_max_right _ _, ?_⟩
  intro t ht
  exact ⟨hρ0 _, (hRρ (mem_image_of_mem _ ht)).trans (le_max_left _ _)⟩

omit [BorelSpace E] [MeasurableSpace M] [BorelSpace M] in
/-- The original Lipschitz population hypothesis automatically supplies the complete-seed
measurability and compact-time bound. -/
theorem populationSeed_lipschitz_density_on_interval (S : F.CalibratedLevelSeedPatch u)
    (hF : F.IsSmoothStronglyConvex) {w : S.covector.ker} (hw : w ∈ S.labels)
    {ρ : M → ℝ} {K : ℝ≥0}
    (hρ : let _instPopulationDensityMetric : MetricSpace M := F.metricSpace
      LipschitzWith K ρ) (hρ0 : ∀ x, 0 ≤ ρ x) (l h : ℝ) :
    Measurable (fun t ↦ ρ (S.curve w t)) ∧ ∃ Rρ : ℝ, 0 ≤ Rρ ∧
      ∀ t ∈ Icc l h, 0 ≤ ρ (S.curve w t) ∧ ρ (S.curve w t) ≤ Rρ := by
  let _instPopulationDensityMetric : MetricSpace M := F.metricSpace
  exact populationSeed_density_on_interval S hF hw hρ.continuous hρ0 l h

end OTSelector.Reconstruction

namespace OTSelector.Geometry.ContinuousFinslerNorm.SeedEndpointChart

open OTSelector.Reconstruction

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ} {S : CalibratedLevelSeedPatch F u}
  {initial : M} {t₀ : ℝ} {w : S.covector.ker} {z₀ : E × (E →L[ℝ] ℝ)}
  {R : S.covector.ker →L[ℝ] E} {Q : S.covector.ker →L[ℝ] E →L[ℝ] ℝ}
  {C : F.SmoothPhaseJetComparison initial t₀ w z₀ R Q} {endpoint : ℝ}

omit [BorelSpace E] [T2Space M] [PreconnectedSpace M]
  [MeasurableSpace M] [BorelSpace M] in
/-- Actual endpoint charts turn the original continuous population and volume densities
into all density and weight inputs for the physical moment window. -/
theorem population_density_weight_data (G : SeedEndpointChart S C endpoint)
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {ρ : M → ℝ} (hρ : Continuous ρ) (hρ0 : ∀ x, 0 ≤ ρ x)
    {v : M → E → ℝ}
    (hv : ContinuousOn (v G.old) (extChartAt 𝓘(ℝ, E) G.old).target)
    (hv0 : ∀ y ∈ (extChartAt 𝓘(ℝ, E) G.old).target, 0 ≤ v G.old y)
    {l h : ℝ} (hI : ∀ t ∈ Icc l h, (w, t) ∈ G.geometry.U) (c : ℝ≥0∞) :
    Measurable (fun t ↦ ρ (S.curve w t)) ∧ ∃ Rρ : ℝ, 0 ≤ Rρ ∧
      (∀ t ∈ Ioo l h, 0 ≤ ρ (S.curve w t)) ∧
      (∀ t ∈ Ioo l h, ρ (S.curve w t) ≤ Rρ) ∧
      ContinuousOn (fun t ↦ c.toReal * v G.old
        (populationSeedChartReadout S G.center (t, w))) (Icc l h) ∧
      ∀ t ∈ Ioo l h, 0 ≤ c.toReal * v G.old
        (populationSeedChartReadout S G.center (t, w)) := by
  obtain ⟨hρm, Rρ, hRρ0, hRρ⟩ := populationSeed_density_on_interval S hF hw hρ hρ0 l h
  have hc : Continuous (S.curve w) := continuous_iff_continuousAt.mpr fun t ↦
    (hF.contMDiffAt_of_isEulerLagrangeAt (S.complete w hw t (mem_univ _))).continuousAt
  have hsource : MapsTo (S.curve w) (Icc l h) (extChartAt 𝓘(ℝ, E) G.old).source := by
    intro t ht
    exact (S.local_data G.center.val G.center.property).2.2.1
      (ball_subset_closedBall (G.within_ball (w, t) (hI t ht)))
  have hreadout : ContinuousOn
      (fun t ↦ populationSeedChartReadout S G.center (t, w)) (Icc l h) :=
    (continuousOn_extChartAt G.old).comp hc.continuousOn hsource
  have htarget : MapsTo (fun t ↦ populationSeedChartReadout S G.center (t, w))
      (Icc l h) (extChartAt 𝓘(ℝ, E) G.old).target := by
    intro t ht
    exact (extChartAt 𝓘(ℝ, E) G.old).map_source (hsource ht)
  refine ⟨hρm, Rρ, hRρ0, fun t _ ↦ hρ0 _,
    fun t ht ↦ (hRρ t (Ioo_subset_Icc_self ht)).2,
    continuousOn_const.mul (hv.comp hreadout htarget), ?_⟩
  intro t ht
  exact mul_nonneg ENNReal.toReal_nonneg (hv0 _ (htarget (Ioo_subset_Icc_self ht)))

end OTSelector.Geometry.ContinuousFinslerNorm.SeedEndpointChart
