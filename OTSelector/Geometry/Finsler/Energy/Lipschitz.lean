import OTSelector.Geometry.Finsler.Basic
import OTSelector.Geometry.Finsler.Energy.Basic
import OTSelector.Geometry.Finsler.Geodesic.Energy
import OTSelector.Geometry.Finsler.Geodesic.MetricMinimizerRegularity
import OTSelector.Geometry.Finsler.LengthMetric
import OTSelector.Geometry.Finsler.MetricDifferential
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Geometry.FinslerLipschitzEnergy.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Geometry.FinslerLipschitzEnergy`; the selected original proof blocks follow. -/
section

/-!
# Geometry.Finsler.Energy.Lipschitz

* **Conditions:** A smooth strongly convex Finsler norm and a globally or interval-wise metric Lipschitz curve with finite time endpoints.
* **Objects:** Almost-everywhere measurable bounded speed and interval-integrable actual speed and energy.
* **Proof detail:** Apply almost-everywhere differentiability and the metric differential, dominate speed by the Lipschitz constant and energy by its square, and clamp interval curves to global ones.

Mathematical sources:
- [D. H. Fremlin, Measure Theory, Volume 2, Chapter 26](https://www1.essex.ac.uk/maths/people/fremlin/chap26.pdf#page=18): Section 262Q, Rademacher theorem and proof, pp. 18–20; Section 262B(c), p. 10 (Lipschitz implies absolutely continuous on bounded intervals).
- [Sheldon Axler, Measure, Integration & Real Analysis (author PDF, 12 June 2026)](https://measure.axler.net/MIRA.pdf#page=99): Section 3A, Theorem 3.23, p. 84; Section 3B, Theorem 3.25, p. 88.
- [Zhongmin Shen, Landsberg Curvature, S-Curvature and Riemann Curvature, in Riemann–Finsler Geometry, MSRI Publications 50 (2004)](https://library.slmath.org/books/Book50/files/08Sh.pdf#page=11): Section 4, p. 313: the length integral, induced distance and minimizing curves.

Source relation (derived): Measurability and finite-measure domination yield the integrability statements; the clamped-extension implementation is proved locally.
-/

/-!
# Integrability of the actual speed and energy of Finsler Lipschitz curves

Continuous original-distance difference quotients converge almost everywhere to the
actual Finsler speed. This proves its strong measurability and Lipschitz bound without
assuming tangent measurability. On closed intervals both actual speed and kinetic
energy are integrable, also for curves which are only Lipschitz on that interval.
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
/-- The actual Finsler speed of an original-distance Lipschitz curve is almost
everywhere strongly measurable. -/
theorem aestronglyMeasurable_speed_of_lipschitzWith (hF : F.IsSmoothStronglyConvex)
    {c : ℝ → M} {K : ℝ≥0}
    (hc : letI : MetricSpace M := F.metricSpace; LipschitzWith K c) :
    AEStronglyMeasurable
      (fun t ↦ (F.toFun (tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) c ⟨t, (1 : ℝ)⟩) : ℝ)) volume := by
  let : MetricSpace M := F.metricSpace
  let q : ℝ → ℝ → ℝ := fun h t ↦ dist (c t) (c (t + h)) / |h|
  apply aestronglyMeasurable_of_tendsto_ae (𝓝[≠] (0 : ℝ)) (f := q)
  · intro h
    exact ((hc.continuous.dist (hc.continuous.comp (continuous_id.add_const h))).div_const
      |h|).aestronglyMeasurable
  · filter_upwards [F.ae_mdifferentiableAt_of_lipschitzWith hc] with t ht
    have hlim := hF.tendsto_dist_div_abs_sub_of_mdifferentiableAt ht
    have hmap : Tendsto (fun h : ℝ ↦ t + h) (𝓝[≠] 0) (𝓝[≠] t) := by
      simp [Tendsto]
    simpa only [q, Function.comp_def, add_sub_cancel_left] using hlim.comp hmap

set_option backward.isDefEq.respectTransparency false in
/-- The actual Finsler speed is bounded almost everywhere by the original-distance
Lipschitz constant. -/
theorem ae_speed_le_of_lipschitzWith (hF : F.IsSmoothStronglyConvex)
    {c : ℝ → M} {K : ℝ≥0}
    (hc : letI : MetricSpace M := F.metricSpace; LipschitzWith K c) :
    ∀ᵐ t ∂volume, F.toFun (tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) c ⟨t, (1 : ℝ)⟩) ≤ K := by
  let : MetricSpace M := F.metricSpace
  filter_upwards [F.ae_mdifferentiableAt_of_lipschitzWith hc] with t ht
  have hlim := hF.tendsto_dist_div_abs_sub_of_mdifferentiableAt ht
  have hbound : (F.toFun (tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) c ⟨t, (1 : ℝ)⟩) : ℝ) ≤ K := by
    apply le_of_tendsto hlim
    filter_upwards [self_mem_nhdsWithin] with s hs
    have hpos : 0 < |s - t| := abs_pos.mpr (sub_ne_zero.mpr hs)
    apply (div_le_iff₀ hpos).2
    simpa only [Real.dist_eq, abs_sub_comm] using hc.dist_le_mul t s
  exact_mod_cast hbound

private theorem intervalIntegrable_speed_energy_of_lipschitzWith
    (hF : F.IsSmoothStronglyConvex) {c : ℝ → M} {K : ℝ≥0} (a b : ℝ)
    (hc : letI : MetricSpace M := F.metricSpace; LipschitzWith K c) :
    IntervalIntegrable
      (fun t ↦ (F.toFun (tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) c ⟨t, (1 : ℝ)⟩) : ℝ)) volume a b ∧
    IntervalIntegrable
      (fun t ↦ F.energy (tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) c ⟨t, (1 : ℝ)⟩)) volume a b := by
  let : IsFiniteMeasure (volume.restrict (uIoc a b)) := by
    unfold uIoc
    infer_instance
  have hs := hF.aestronglyMeasurable_speed_of_lipschitzWith hc
  have hb := hF.ae_speed_le_of_lipschitzWith hc
  constructor
  · apply intervalIntegrable_iff.mpr
    apply Integrable.of_bound hs.restrict (K : ℝ)
    filter_upwards [ae_restrict_of_ae hb] with t ht
    simpa only [Real.norm_eq_abs, abs_of_nonneg (NNReal.coe_nonneg _)] using
      (show (F.toFun (tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) c ⟨t, (1 : ℝ)⟩) : ℝ) ≤ K from ht)
  · apply intervalIntegrable_iff.mpr
    apply Integrable.of_bound
      (((continuous_id.pow 2).div_const 2).comp_aestronglyMeasurable hs).restrict ((K : ℝ) ^ 2 / 2)
    filter_upwards [ae_restrict_of_ae hb] with t ht
    change ‖(F.toFun (tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) c ⟨t, (1 : ℝ)⟩) : ℝ) ^ 2 / 2‖ ≤ _
    rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (sq_nonneg _) (by norm_num))]
    exact div_le_div_of_nonneg_right (sq_le_sq₀ (NNReal.coe_nonneg _) K.coe_nonneg |>.mpr ht)
      (by norm_num)

private theorem intervalIntegrable_speed_energy_of_lipschitzOnWith
    (hF : F.IsSmoothStronglyConvex) {c : ℝ → M} {a b : ℝ} {K : ℝ≥0} (hab : a ≤ b)
    (hc : letI : MetricSpace M := F.metricSpace; LipschitzOnWith K c (Icc a b)) :
    IntervalIntegrable
      (fun t ↦ (F.toFun (tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) c ⟨t, (1 : ℝ)⟩) : ℝ)) volume a b ∧
    IntervalIntegrable
      (fun t ↦ F.energy (tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) c ⟨t, (1 : ℝ)⟩)) volume a b := by
  let : MetricSpace M := F.metricSpace
  let d : ℝ → M := (fun t : Icc a b ↦ c t) ∘ projIcc a b hab
  have hrestrict : LipschitzWith K (fun t : Icc a b ↦ c t) := by
    intro u v
    exact hc u.property v.property
  have hd : LipschitzWith K d := by
    simpa only [mul_one] using hrestrict.comp (LipschitzWith.projIcc hab)
  obtain ⟨hs, he⟩ := intervalIntegrable_speed_energy_of_lipschitzWith hF a b hd
  have heq : ∀ t ∈ uIoo a b,
      F.toFun (tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) d ⟨t, (1 : ℝ)⟩) =
        F.toFun (tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) c ⟨t, (1 : ℝ)⟩) := by
    intro t ht
    rw [uIoo_of_le hab] at ht
    apply F.speed_eq_of_eventuallyEq
    filter_upwards [Icc_mem_nhds ht.1 ht.2] with s hs
    simp only [d, Function.comp_apply, projIcc_of_mem _ hs]
  exact ⟨hs.congr_uIoo (fun t ht ↦ congrArg ((↑) : ℝ≥0 → ℝ) (heq t ht)),
    he.congr_uIoo (fun t ht ↦ by simp only [ContinuousFinslerNorm.energy, heq t ht])⟩

/-- A curve which is Lipschitz only on the closed interval has interval-integrable
actual Finsler speed; no measurability assumption is required. -/
theorem intervalIntegrable_speed_of_lipschitzOnWith (hF : F.IsSmoothStronglyConvex)
    {c : ℝ → M} {a b : ℝ} {K : ℝ≥0} (hab : a ≤ b)
    (hc : letI : MetricSpace M := F.metricSpace; LipschitzOnWith K c (Icc a b)) :
    IntervalIntegrable
      (fun t ↦ (F.toFun (tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) c ⟨t, (1 : ℝ)⟩) : ℝ)) volume a b :=
  (intervalIntegrable_speed_energy_of_lipschitzOnWith hF hab hc).1

/-- A curve which is Lipschitz only on the closed interval has interval-integrable
actual kinetic energy; no measurability assumption is required. -/
theorem intervalIntegrable_energy_of_lipschitzOnWith (hF : F.IsSmoothStronglyConvex)
    {c : ℝ → M} {a b : ℝ} {K : ℝ≥0} (hab : a ≤ b)
    (hc : letI : MetricSpace M := F.metricSpace; LipschitzOnWith K c (Icc a b)) :
    IntervalIntegrable
      (fun t ↦ F.energy (tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) c ⟨t, (1 : ℝ)⟩)) volume a b :=
  (intervalIntegrable_speed_energy_of_lipschitzOnWith hF hab hc).2

end OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

end
end
