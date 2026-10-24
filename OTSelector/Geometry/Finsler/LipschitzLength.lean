import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import OTSelector.Geometry.Finsler.Basic
import OTSelector.Geometry.Finsler.Energy.Basic
import OTSelector.Geometry.Finsler.Geodesic.MetricMinimizerRegularity
import OTSelector.Geometry.Finsler.LengthMetric
import OTSelector.Geometry.Finsler.MetricDifferential
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Geometry.FinslerLipschitzLength.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Geometry.FinslerLipschitzLength`; the selected original proof blocks follow. -/
section

/-!
# Geometry.Finsler.LipschitzLength

* **Conditions:** A smooth strongly convex Finsler norm and a globally or interval-wise original-metric Lipschitz curve, with ordered time endpoints.
* **Objects:** A scalar distance derivative bound and distance bounded by the integral of actual Finsler speed.
* **Proof detail:** Differentiate distance-to-a-fixed-point almost everywhere, bound its derivative by metric speed, and integrate its absolutely continuous representative.

Mathematical sources:
- [D. H. Fremlin, Measure Theory, Volume 2, Chapter 26](https://www1.essex.ac.uk/maths/people/fremlin/chap26.pdf#page=18): Section 262Q, Rademacher theorem and proof, pp. 18–20; Section 262B(c), p. 10 (Lipschitz implies absolutely continuous on bounded intervals).
- [D. H. Fremlin, Measure Theory, Volume 2, Chapter 22](https://www1.essex.ac.uk/maths/people/fremlin/chap22.pdf#page=29): Section 225E, p. 29 (absolute continuity and indefinite integral); Section 225F, p. 30 (integration by parts).
- [Zhongmin Shen, Landsberg Curvature, S-Curvature and Riemann Curvature, in Riemann–Finsler Geometry, MSRI Publications 50 (2004)](https://library.slmath.org/books/Book50/files/08Sh.pdf#page=11): Section 4, p. 313: the length integral, induced distance and minimizing curves.

Source relation (derived): Extends the smooth length-distance comparison to Lipschitz curves using the actual metric differential.
-/

/-!
# Length comparison for original-metric Lipschitz curves

The distance from the initial point is a real Lipschitz function. Its derivative
is bounded almost everywhere by the actual Finsler speed, using the original
metric differential. The real absolutely-continuous fundamental theorem and an
extended-norm integral estimate then bound original distance by the actual
Finsler derivative-integral length. No speed measurability or integrability is
an extra premise. Clamping time yields the same comparison for interval-Lipschitz
curves without any smoothness assumption on the curve.
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
private theorem abs_deriv_dist_le_speed (hF : F.IsSmoothStronglyConvex)
    {c : ℝ → M} {t₀ : ℝ} (x : M)
    (hc : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) c t₀)
    (hg : letI : MetricSpace M := F.metricSpace
      DifferentiableAt ℝ (fun t ↦ dist x (c t)) t₀) :
    letI : MetricSpace M := F.metricSpace
    |deriv (fun t ↦ dist x (c t)) t₀| ≤
      (F.toFun (tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) c ⟨t₀, (1 : ℝ)⟩) : ℝ) := by
  let : MetricSpace M := F.metricSpace
  have hnorm := hg.hasDerivAt.tendsto_slope.norm
  rw [Real.norm_eq_abs] at hnorm
  apply le_of_tendsto_of_tendsto' hnorm (hF.tendsto_dist_div_abs_sub_of_mdifferentiableAt hc)
  intro t
  rw [slope_def_module, norm_smul, norm_inv, Real.norm_eq_abs, Real.norm_eq_abs,
    ← div_eq_inv_mul]
  have hdist := dist_dist_dist_le_right x (c t) (c t₀)
  rw [Real.dist_eq] at hdist
  exact div_le_div_of_nonneg_right (hdist.trans_eq (dist_comm _ _)) (abs_nonneg _)

set_option backward.isDefEq.respectTransparency false in
/-- Every globally Lipschitz curve for the original Finsler metric bounds endpoint
distance by its actual derivative-integral path length, without a C1 assumption. -/
theorem lengthEDist_le_pathELength_of_lipschitzWith (hF : F.IsSmoothStronglyConvex)
    {c : ℝ → M} {a b : ℝ} {K : ℝ≥0} (hab : a ≤ b)
    (hc : letI : MetricSpace M := F.metricSpace; LipschitzWith K c) :
    letI : ∀ x : M, ENorm (TangentSpace 𝓘(ℝ, E) x) := F.enorm
    F.lengthEDist (c a) (c b) ≤ Manifold.pathELength 𝓘(ℝ, E) c a b := by
  let : MetricSpace M := F.metricSpace
  let : ∀ x : M, ENorm (TangentSpace 𝓘(ℝ, E) x) := F.enorm
  let g : ℝ → ℝ := fun t ↦ dist (c a) (c t)
  have hg : LipschitzWith K g := by
    simpa only [one_mul, g, Function.comp_def] using (LipschitzWith.dist_right (c a)).comp hc
  have hga : AbsolutelyContinuousOnInterval g a b :=
    hg.lipschitzOnWith.absolutelyContinuousOnInterval
  have hFTC : ∫ t in Ioo a b, deriv g t = dist (c a) (c b) := by
    have h := hga.integral_deriv_eq_sub
    rw [intervalIntegral.integral_of_le hab, integral_Ioc_eq_integral_Ioo] at h
    simpa only [g, dist_self, sub_zero] using h
  have hbound : ∀ᵐ t ∂volume.restrict (Ioo a b),
      ‖deriv g t‖ₑ ≤ ‖mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) c t 1‖ₑ := by
    filter_upwards [ae_restrict_of_ae (hg.ae_differentiableAt (μ := volume)),
      ae_restrict_of_ae (F.ae_mdifferentiableAt_of_lipschitzWith hc)] with t hgt hct
    change ‖deriv g t‖ₑ ≤ (F.toFun (tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) c ⟨t, (1 : ℝ)⟩) : ℝ≥0∞)
    rw [Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_coe_nnreal]
    exact ENNReal.ofReal_le_ofReal (hF.abs_deriv_dist_le_speed (c a) hct hgt)
  rw [Manifold.pathELength_eq_lintegral_mfderiv_Ioo]
  calc
    F.lengthEDist (c a) (c b) = ‖∫ t in Ioo a b, deriv g t‖ₑ := by
      change edist (c a) (c b) = _
      rw [hFTC, Real.enorm_eq_ofReal dist_nonneg, edist_dist]
    _ ≤ ∫⁻ t in Ioo a b, ‖deriv g t‖ₑ := enorm_integral_le_lintegral_enorm _
    _ ≤ ∫⁻ t in Ioo a b, ‖mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) c t 1‖ₑ :=
      lintegral_mono_ae hbound

set_option backward.isDefEq.respectTransparency false in
/-- Every curve Lipschitz on a closed time interval for the original Finsler metric
bounds endpoint distance by its actual derivative-integral path length. -/
theorem lengthEDist_le_pathELength_of_lipschitzOnWith (hF : F.IsSmoothStronglyConvex)
    {c : ℝ → M} {a b : ℝ} {K : ℝ≥0} (hab : a ≤ b)
    (hc : letI : MetricSpace M := F.metricSpace; LipschitzOnWith K c (Icc a b)) :
    letI : ∀ x : M, ENorm (TangentSpace 𝓘(ℝ, E) x) := F.enorm
    F.lengthEDist (c a) (c b) ≤ Manifold.pathELength 𝓘(ℝ, E) c a b := by
  let : MetricSpace M := F.metricSpace
  let : ∀ x : M, ENorm (TangentSpace 𝓘(ℝ, E) x) := F.enorm
  let d : ℝ → M := (fun t : Icc a b ↦ c t) ∘ projIcc a b hab
  have hrestrict : LipschitzWith K (fun t : Icc a b ↦ c t) := by
    intro u v
    exact hc u.property v.property
  have hd : LipschitzWith K d := by
    simpa only [mul_one] using hrestrict.comp (LipschitzWith.projIcc hab)
  have heq : EqOn d c (Icc a b) := by
    intro t ht
    simp only [d, Function.comp_apply, projIcc_of_mem _ ht]
  have hlength := Manifold.pathELength_congr (I := 𝓘(ℝ, E)) heq
  have h := hF.lengthEDist_le_pathELength_of_lipschitzWith hab hd
  rwa [heq (left_mem_Icc.mpr hab), heq (right_mem_Icc.mpr hab), hlength] at h

end OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

end
end
