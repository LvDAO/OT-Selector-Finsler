import OTSelector.Geometry.Finsler.Basic
import OTSelector.Geometry.Finsler.Energy.Basic
import OTSelector.Geometry.Finsler.Geodesic.Basic
import OTSelector.Geometry.Finsler.Geodesic.Complete
import OTSelector.Geometry.Finsler.Geodesic.ConstantSpeedDistance
import OTSelector.Geometry.Finsler.Geodesic.Defs
import OTSelector.Geometry.Finsler.Geodesic.Energy
import OTSelector.Geometry.Finsler.Geodesic.MetricMinimizerRegularity
import OTSelector.Geometry.Finsler.Geodesic.TangentMetricComparison
import OTSelector.Geometry.Finsler.LengthMetric
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Geometry.FinslerMetricDifferential.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Geometry.FinslerMetricDifferential`; the selected original proof blocks follow. -/
section

/-!
# Geometry.Finsler.MetricDifferential

* **Conditions:** A smooth strongly convex Finsler norm and manifold differentiability at a time; isometric-interval conclusions use the explicit isometry premise.
* **Objects:** The actual metric difference quotient equals the Finsler norm of velocity, and isometric intervals have unit speed almost everywhere.
* **Proof detail:** Compare the tangent with a smooth constant-speed locally minimizing geodesic, transfer the metric slope by first-order agreement, then apply Rademacher.

Mathematical sources:
- [Zhongmin Shen, Landsberg Curvature, S-Curvature and Riemann Curvature, MSRI Publications 50 (2004)](https://library.slmath.org/books/Book50/files/08Sh.pdf#page=11): Section 4, Definition 4.1 and Lemma 4.2, pp. 313–314; equations (4–1), (4–2) and the canonical-lift spray interpretation.
- [Zhongmin Shen, Landsberg Curvature, S-Curvature and Riemann Curvature, in Riemann–Finsler Geometry, MSRI Publications 50 (2004)](https://library.slmath.org/books/Book50/files/08Sh.pdf#page=11): Section 4, p. 313: the length integral, induced distance and minimizing curves.
- [D. H. Fremlin, Measure Theory, Volume 2, Chapter 26](https://www1.essex.ac.uk/maths/people/fremlin/chap26.pdf#page=18): Section 262Q, Rademacher theorem and proof, pp. 18–20; Section 262B(c), p. 10 (Lipschitz implies absolutely continuous on bounded intervals).

Source relation (derived): The metric differential formula is proved from a smooth comparison curve and local metric bounds; the almost-everywhere claim is a derived application.
-/

/-!
# The metric differential of the original smooth Finsler length distance

At each manifold-differentiable time of a curve, its original-distance quotient
converges to the original Finsler norm of its actual tangent. Nonzero tangents
are compared with the constructed local constant-speed minimizing EL germ, and
zero tangents with a constant curve. Thus differentiable interior points of an
original-distance isometric interval have unit Finsler speed, almost everywhere.
No completeness or additional geometric premise is needed.
-/

open Set Filter Metric Manifold MeasureTheory
open scoped Topology ContDiff NNReal ENNReal

noncomputable section

namespace OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [PreconnectedSpace M]
  {F : ContinuousFinslerNorm E M}

set_option backward.isDefEq.respectTransparency false in
/-- At any manifold-differentiable time, the two-sided punctured original-distance
quotient converges to the Finsler norm of the actual tangent, including zero tangents. -/
theorem tendsto_dist_div_abs_sub_of_mdifferentiableAt (hF : F.IsSmoothStronglyConvex)
    {c : ℝ → M} {t₀ : ℝ}
    (hc : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) c t₀) :
    letI : MetricSpace M := F.metricSpace
    Tendsto (fun t ↦ dist (c t₀) (c t) / |t - t₀|) (𝓝[≠] t₀)
      (𝓝 (F.toFun (tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) c ⟨t₀, (1 : ℝ)⟩) : ℝ)) := by
  let : MetricSpace M := F.metricSpace
  let : ∀ x : M, ENorm (TangentSpace 𝓘(ℝ, E) x) := F.enorm
  by_cases hv : mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) c t₀ 1 = 0
  · let d : ℝ → M := fun _ ↦ c t₀
    have hd : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) d t₀ := mdifferentiableAt_const
    have heq : tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) c ⟨t₀, (1 : ℝ)⟩ =
        tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) d ⟨t₀, (1 : ℝ)⟩ := by
      simp only [tangentMap, d, mfderiv_const, zero_apply, hv]
    have hs : F.toFun (tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) c ⟨t₀, (1 : ℝ)⟩) = 0 := by
      simp only [tangentMap, hv, F.map_zero]
    apply F.tendsto_dist_div_abs_sub_of_tangentMap_eq hc hd heq
    simpa only [d, dist_self, zero_div, hs, NNReal.coe_zero] using
      (tendsto_const_nhds : Tendsto (fun _ : ℝ ↦ (0 : ℝ)) (𝓝[≠] t₀) (𝓝 0))
  · obtain ⟨ε, hε, d, hd₀, hdv, hdEL⟩ :=
      hF.exists_local_eulerLagrange_of_tangent (c t₀) hv t₀
    have ht₀ : t₀ ∈ Ioo (t₀ - ε) (t₀ + ε) := ⟨by linarith, by linarith⟩
    have hdAt := hdEL t₀ ht₀
    have hd : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) d t₀ :=
      (hF.contMDiffAt_of_isEulerLagrangeAt hdAt).mdifferentiableAt (by simp)
    change tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) d ⟨t₀, (1 : ℝ)⟩ =
      tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) c ⟨t₀, (1 : ℝ)⟩ at hdv
    obtain ⟨δ, hδ, hmin⟩ := hF.locally_minimizing_of_isEulerLagrangeAt hdAt
    let r := min ε δ
    have hr : 0 < r := lt_min hε hδ
    have hrε : r ≤ ε := min_le_left _ _
    have hrδ : r ≤ δ := min_le_right _ _
    have hspeed : ∀ t ∈ Ioo (t₀ - r) (t₀ + r),
        F.toFun (tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) d ⟨t, (1 : ℝ)⟩) =
          F.toFun (tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) c ⟨t₀, (1 : ℝ)⟩) := by
      intro t ht
      have htε : t ∈ Ioo (t₀ - ε) (t₀ + ε) := ⟨by linarith [ht.1], by linarith [ht.2]⟩
      exact (hF.speed_eq_of_isEulerLagrangeOn hdEL isPreconnected_Ioo htε ht₀).trans
        (congrArg F.toFun hdv)
    have hsmall : Icc (t₀ - r) (t₀ + r) ⊆ Icc (t₀ - δ) (t₀ + δ) :=
      Icc_subset_Icc (by linarith) (by linarith)
    have hdist := F.dist_eq_mul_abs_sub_of_locally_minimizing hr hspeed
      (fun u hu v hv huv ↦ hmin u (hsmall hu) v (hsmall hv) huv)
    have hlim : Tendsto (fun t ↦ dist (d t₀) (d t) / |t - t₀|) (𝓝[≠] t₀)
        (𝓝 (F.toFun (tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) c ⟨t₀, (1 : ℝ)⟩) : ℝ)) := by
      apply tendsto_const_nhds.congr'
      have hnear : ∀ᶠ t in 𝓝 t₀, t ∈ Icc (t₀ - r) (t₀ + r) :=
        Icc_mem_nhds (by linarith) (by linarith)
      filter_upwards [hnear.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with t ht hne
      rw [hdist t ht, mul_div_cancel_right₀ _ (abs_ne_zero.mpr (sub_ne_zero.mpr hne))]
    exact F.tendsto_dist_div_abs_sub_of_tangentMap_eq hc hd hdv.symm hlim

set_option backward.isDefEq.respectTransparency false in
/-- At every manifold-differentiable interior point of an original-distance isometric
interval, the actual Finsler speed equals one. -/
theorem speed_eq_one_of_isometry (hF : F.IsSmoothStronglyConvex)
    {c : ℝ → M} {a b t₀ : ℝ} (ht₀ : t₀ ∈ Ioo a b)
    (hc : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) c t₀)
    (hiso : letI : MetricSpace M := F.metricSpace
      Isometry (fun t : Icc a b ↦ c t)) :
    F.toFun (tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) c ⟨t₀, (1 : ℝ)⟩) = 1 := by
  let : MetricSpace M := F.metricSpace
  have hlim : Tendsto (fun t ↦ dist (c t₀) (c t) / |t - t₀|) (𝓝[≠] t₀) (𝓝 (1 : ℝ)) := by
    apply tendsto_const_nhds.congr'
    have hnear : ∀ᶠ t in 𝓝 t₀, t ∈ Icc a b := Icc_mem_nhds ht₀.1 ht₀.2
    filter_upwards [hnear.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with t ht hne
    have hdist := hiso.dist_eq (⟨t₀, ht₀.1.le, ht₀.2.le⟩ : Icc a b) ⟨t, ht⟩
    change dist (c t₀) (c t) = dist t₀ t at hdist
    rw [hdist, Real.dist_eq, abs_sub_comm, div_self (abs_ne_zero.mpr (sub_ne_zero.mpr hne))]
  have heq := tendsto_nhds_unique (hF.tendsto_dist_div_abs_sub_of_mdifferentiableAt hc) hlim
  exact_mod_cast heq

/-- An arbitrary original-distance isometric interval has an actual nonzero tangent
and unit Finsler speed almost everywhere in its interior. -/
theorem ae_unit_speed_of_isometric_interval (hF : F.IsSmoothStronglyConvex)
    {c : ℝ → M} {a b : ℝ}
    (hiso : letI : MetricSpace M := F.metricSpace
      Isometry (fun t : Icc a b ↦ c t)) :
    ∀ᵐ t ∂volume.restrict (Ioo a b),
      MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) c t ∧
      mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) c t 1 ≠ 0 ∧
      F.toFun (tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) c ⟨t, (1 : ℝ)⟩) = 1 := by
  filter_upwards [F.ae_nonzero_velocity_of_isometric_interval hiso,
    ae_restrict_mem measurableSet_Ioo] with t ht htin
  exact ⟨ht.1, ht.2.1, hF.speed_eq_one_of_isometry htin ht.1 hiso⟩

end OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

end
end
