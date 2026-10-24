import OTSelector.Geometry.Finsler.Basic
import OTSelector.Geometry.Finsler.Coordinates.InverseChartLipschitz
import OTSelector.Geometry.Finsler.LengthMetric
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Geometry.FinslerTangentMetricComparison.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Geometry.FinslerTangentMetricComparison`; the selected original proof blocks follow. -/
section

/-!
# Geometry.Finsler.Geodesic.TangentMetricComparison

* **Conditions:** Two manifold-differentiable curves have the same tangent at the comparison time; one metric slope is known for the transfer theorem.
* **Objects:** Their mutual distance is o(|t−t0|), and equality of their metric derivatives whenever the reference limit exists.
* **Proof detail:** Subtract equal first-order coordinate expansions, apply an inverse-chart Lipschitz bound, then squeeze distance quotients with the triangle inequality.

Mathematical sources:
- [Jiří Lebl, Basic Analysis II: Introduction to Real Analysis, Volume II](https://www.jirka.org/ra/realanal2.pdf): Sections 8.3–8.4, total derivative, chain rule and mean-value bounds; Section 8.6, higher derivatives.
- [Zhongmin Shen, Landsberg Curvature, S-Curvature and Riemann Curvature, in Riemann–Finsler Geometry, MSRI Publications 50 (2004)](https://library.slmath.org/books/Book50/files/08Sh.pdf#page=11): Section 4, p. 313: the length integral, induced distance and minimizing curves.

Source relation (derived): A first-order comparison lemma derived in the length metric; no global smoothness of either curve is used.
-/

/-!
# First-order metric comparison of curves with the same actual tangent

A local inverse-chart Lipschitz bound converts equal coordinate derivatives into
an original-metric separation which is negligible relative to elapsed time. The
reverse triangle inequality then transfers any existing metric speed limit between
the two curves. Only differentiability at the reference time is required.
-/

open Set Filter Metric Manifold
open scoped Topology ContDiff NNReal

set_option backward.isDefEq.respectTransparency false

namespace OTSelector.Geometry

private theorem tendsto_dist_div_abs_sub_of_same_deriv
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {X : Type*} [MetricSpace X] {u v : ℝ → E} {c d : ℝ → X}
    {t₀ : ℝ} {w : E} {C : ℝ} (hu : HasDerivAt u w t₀) (hv : HasDerivAt v w t₀)
    (heq : u t₀ = v t₀)
    (hbound : ∀ᶠ t in 𝓝 t₀, dist (c t) (d t) ≤ C * dist (u t) (v t)) :
    Tendsto (fun t ↦ dist (c t) (d t) / |t - t₀|) (𝓝[≠] t₀) (𝓝 0) := by
  have hd : HasDerivAt (fun t ↦ u t - v t) 0 t₀ := by
    simpa only [sub_self] using hu.fun_sub hv
  have hlim : Tendsto (fun t ↦ C * ‖slope (fun s ↦ u s - v s) t₀ t‖)
      (𝓝[≠] t₀) (𝓝 0) := by
    simpa only [norm_zero, mul_zero] using hd.tendsto_slope.norm.const_mul C
  apply squeeze_zero' (Eventually.of_forall (fun t ↦ div_nonneg dist_nonneg (abs_nonneg _)))
    _ hlim
  filter_upwards [hbound.filter_mono nhdsWithin_le_nhds] with t ht
  calc
    dist (c t) (d t) / |t - t₀| ≤ C * dist (u t) (v t) / |t - t₀| :=
      div_le_div_of_nonneg_right ht (abs_nonneg _)
    _ = C * ‖slope (fun s ↦ u s - v s) t₀ t‖ := by
      rw [slope_def_module, heq, sub_self, sub_zero, norm_smul, norm_inv,
        Real.norm_eq_abs, dist_eq_norm]
      ring

namespace ContinuousFinslerNorm

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) 1 M] [FiniteDimensional ℝ E] [T2Space M]
  [PreconnectedSpace M] (F : ContinuousFinslerNorm E M)

/-- Equal actual tangents at one differentiable time give original-metric separation
which is negligible relative to the absolute time difference. -/
theorem tendsto_dist_div_abs_sub_zero_of_tangentMap_eq
    {c d : ℝ → M} {t₀ : ℝ}
    (hc : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) c t₀)
    (hd : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) d t₀)
    (hv : tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) c ⟨t₀, (1 : ℝ)⟩ =
      tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) d ⟨t₀, (1 : ℝ)⟩) :
    letI : MetricSpace M := F.metricSpace
    Tendsto (fun t ↦ dist (c t) (d t) / |t - t₀|) (𝓝[≠] t₀) (𝓝 0) := by
  let : MetricSpace M := F.metricSpace
  let χ := extChartAt 𝓘(ℝ, E) (c t₀)
  have hbase : c t₀ = d t₀ := congrArg (fun z : TangentBundle 𝓘(ℝ, E) M ↦ z.1) hv
  have hχc : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, E) χ (c t₀) :=
    mdifferentiableAt_extChartAt (mem_chart_source E (c t₀))
  have hχd : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, E) χ (d t₀) := hbase ▸ hχc
  have huc := (hχc.comp t₀ hc).differentiableAt.hasDerivAt
  have hud := (hχd.comp t₀ hd).differentiableAt.hasDerivAt
  have htangent : tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (χ ∘ c) ⟨t₀, (1 : ℝ)⟩ =
      tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (χ ∘ d) ⟨t₀, (1 : ℝ)⟩ := by
    rw [tangentMap_comp_at _ hχc hc, tangentMap_comp_at _ hχd hd, hv]
  have hderiv : deriv (χ ∘ c) t₀ = deriv (χ ∘ d) t₀ := by
    have h := congrArg (fun z : TangentBundle 𝓘(ℝ, E) E ↦ z.2) htangent
    change mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (χ ∘ c) t₀ 1 =
      mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (χ ∘ d) t₀ 1 at h
    rw [mfderiv_eq_fderiv, mfderiv_eq_fderiv] at h
    exact h
  obtain ⟨U, K, hU, hxU, _, hdist⟩ := F.exists_dist_le_mul_dist_extChartAt (c t₀)
  apply tendsto_dist_div_abs_sub_of_same_deriv (v := χ ∘ d) huc (hderiv.symm ▸ hud)
    (congrArg χ hbase)
  filter_upwards [hc.continuousAt (hU.mem_nhds hxU),
    hd.continuousAt (hU.mem_nhds (hbase ▸ hxU))] with t hct hdt
  exact hdist (c t) hct (d t) hdt

/-- A metric speed limit transfers between curves with the same actual tangent at the
reference time, using the original Finsler length distance. -/
theorem tendsto_dist_div_abs_sub_of_tangentMap_eq
    {c d : ℝ → M} {t₀ s : ℝ}
    (hc : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) c t₀)
    (hd : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) d t₀)
    (hv : tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) c ⟨t₀, (1 : ℝ)⟩ =
      tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) d ⟨t₀, (1 : ℝ)⟩)
    (hlim : letI : MetricSpace M := F.metricSpace
      Tendsto (fun t ↦ dist (d t₀) (d t) / |t - t₀|) (𝓝[≠] t₀) (𝓝 s)) :
    letI : MetricSpace M := F.metricSpace
    Tendsto (fun t ↦ dist (c t₀) (c t) / |t - t₀|) (𝓝[≠] t₀) (𝓝 s) := by
  let : MetricSpace M := F.metricSpace
  have hbase : c t₀ = d t₀ := congrArg (fun z : TangentBundle 𝓘(ℝ, E) M ↦ z.1) hv
  apply hlim.congr_dist
  apply squeeze_zero (fun _ ↦ dist_nonneg) _
    (F.tendsto_dist_div_abs_sub_zero_of_tangentMap_eq hc hd hv)
  intro t
  rw [hbase, Real.dist_eq, ← sub_div, abs_div, abs_abs]
  have hdist := dist_dist_dist_le_right (d t₀) (c t) (d t)
  rw [Real.dist_eq, abs_sub_comm] at hdist
  exact div_le_div_of_nonneg_right hdist (abs_nonneg _)

end ContinuousFinslerNorm
end OTSelector.Geometry

end
