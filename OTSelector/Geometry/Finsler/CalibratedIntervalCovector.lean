import OTSelector.Analysis.Convex.Legendre.Parametric
import OTSelector.Geometry.Finsler.Basic
import OTSelector.Geometry.Finsler.CalibratedCovector
import OTSelector.Geometry.Finsler.Energy.Basic
import OTSelector.Geometry.Finsler.Energy.Chart
import OTSelector.Geometry.Finsler.LengthMetric
import OTSelector.Geometry.Finsler.LipschitzDifferential
import OTSelector.Topology.MetricSpace.SaturatedCalibration

/-!
# Geometry.Finsler.CalibratedIntervalCovector

* **Conditions:** A nondegenerate closed isometric interval calibrated by the original 1-Lipschitz potential; differentiability and unit speed are needed only at the tested point.
* **Objects:** Actual rate-one potential differential and original energy Legendre covector, including either closed endpoint.
* **Proof detail:** Squeeze the potential to its affine clock on the interval, use uniqueness of a derivative within the nondegenerate closed interval and apply unit support saturation.

Mathematical sources:
- [Jiří Lebl, Basic Analysis II: Introduction to Real Analysis, Volume II](https://www.jirka.org/ra/realanal2.pdf): Sections 8.3–8.4, total derivative, chain rule and mean-value bounds; Section 8.6, higher derivatives.
- [Rotem Assouline, Curvature-Dimension for Autonomous Lagrangians, arXiv:2409.08001v6 (10 February 2026)](https://arxiv.org/pdf/2409.08001v6#page=29): Sections 4–4.1, Definition 4.2 and Proposition 4.3, p. 29; Lemma 4.5, pp. 30–31; Definition 4.6 and Lemma 4.8, pp. 31–32.
- [Zhongmin Shen, Landsberg Curvature, S-Curvature and Riemann Curvature, MSRI Publications 50 (2004)](https://library.slmath.org/books/Book50/files/08Sh.pdf#page=6): Section 2, p. 308, Legendre transformation, inverse Legendre transformation and equation (2–12).

Source relation (derived): Calibration outside the original closed interval is not needed.
-/

/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Geometry.FinslerCalibratedIntervalCovector.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Geometry.FinslerCalibratedIntervalCovector`; the selected original proof blocks follow. -/
section

/-!
# Original calibration covectors throughout closed minimizing intervals

An original one-Lipschitz potential saturated on an isometric closed interval is affine along
that interval. At any point, including either endpoint, an existing actual derivative therefore
has rate one: uniqueness of the derivative within a nondegenerate closed interval suffices.
At an actual unit tangent this identifies the differential of the potential with the original
fiber-energy Legendre covector. Differentiability and unit speed are required only at the chosen
point, and calibration outside the interval is unnecessary.
-/

open Set Filter Metric Manifold Bundle
open scoped Topology ContDiff NNReal

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace OTSelector.Geometry

/-- An actual derivative at any point of a nondegenerate closed affine interval has rate one. -/
theorem deriv_eq_one_of_eq_affine_on_Icc_of_mem {f : ℝ → ℝ} {a b t d : ℝ}
    (hab : a < b) (ht : t ∈ Icc a b) (hf : HasDerivAt f d t)
    (heq : ∀ r ∈ Icc a b, f r = f a + (r - a)) : d = 1 := by
  have hlin : HasDerivAt (fun r : ℝ ↦ f a + (r - a)) 1 t := by
    simpa only [Pi.add_apply, id_eq, sub_zero, zero_add] using!
      (hasDerivAt_const t (f a)).add ((hasDerivAt_id t).sub_const a)
  have hwithin : HasDerivWithinAt f 1 (Icc a b) t :=
    hlin.hasDerivWithinAt.congr_of_mem heq ht
  exact (uniqueDiffOn_Icc hab t ht).eq_deriv (Icc a b) hf.hasDerivWithinAt hwithin

namespace ContinuousFinslerNorm.IsSmoothStronglyConvex

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [PreconnectedSpace M]
  {F : ContinuousFinslerNorm E M}

/-- The actual differential calibrates the tangent at every point of the closed interval. -/
theorem mfderiv_eq_one_of_calibrated_closedInterval (_hF : F.IsSmoothStronglyConvex)
    {u : M → ℝ} (hu : let _instIntervalRateLip : MetricSpace M := F.metricSpace
      LipschitzWith 1 u)
    {c : ℝ → M} {a b t : ℝ} (hab : a < b)
    (hiso : let _instIntervalRateIso : MetricSpace M := F.metricSpace
      Isometry (fun r : Icc a b ↦ c r))
    (hsat : u (c b) - u (c a) = b - a) (ht : t ∈ Icc a b)
    (hc : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) c t)
    (hd : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ) u (c t)) :
    mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) u (c t)
      (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) c t 1) = (1 : ℝ) := by
  let _instIntervalRateMetric : MetricSpace M := F.metricSpace
  have hg : DifferentiableAt ℝ (u ∘ c) t :=
    mdifferentiableAt_iff_differentiableAt.mp (hd.comp t hc)
  have he : deriv (u ∘ c) t = mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) u (c t)
      (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) c t 1) := by
    have h := mfderiv_comp_apply t hd hc (1 : ℝ)
    rw [mfderiv_eq_fderiv] at h
    exact h
  exact he.symm.trans (deriv_eq_one_of_eq_affine_on_Icc_of_mem hab ht hg.hasDerivAt
    (eq_affine_of_lipschitz_saturated_isometry (u := u) (c := c) hu hiso hsat))

/-- At either endpoint or any interior point, the true potential differential is the
actual original energy covector of the calibrated unit tangent. -/
theorem mfderiv_eq_fiberEnergy_of_calibrated_closedInterval (hF : F.IsSmoothStronglyConvex)
    {u : M → ℝ} (hu : let _instIntervalCovectorLip : MetricSpace M := F.metricSpace
      LipschitzWith 1 u)
    {c : ℝ → M} {a b t : ℝ} (hab : a < b)
    (hiso : let _instIntervalCovectorIso : MetricSpace M := F.metricSpace
      Isometry (fun r : Icc a b ↦ c r))
    (hsat : u (c b) - u (c a) = b - a) (ht : t ∈ Icc a b)
    (hc : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) c t)
    (hunit : F.toFun (tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) c ⟨t, (1 : ℝ)⟩) = 1)
    (hd : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ) u (c t)) :
    mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) u (c t) =
      fderiv ℝ (F.fiberEnergy (c t)) (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) c t 1) := by
  apply (hF.fiberEnergy_fderiv_eq_of_unit_calibration (c t) _ hunit ?_ ?_).symm
  · intro w
    have hb := hF.abs_mfderiv_le_finsler_of_lipschitz hu hd w
    exact (le_abs_self _).trans (by simpa only [NNReal.coe_one, one_mul] using! hb)
  · exact hF.mfderiv_eq_one_of_calibrated_closedInterval hu hab hiso hsat ht hc hd

/-- The same closed-interval covector has actual unit-energy coordinates in every legal chart. -/
theorem exists_chart_unit_covector_of_calibrated_closedInterval
    (hF : F.IsSmoothStronglyConvex) (old : M)
    {u : M → ℝ} (hu : let _instIntervalChartCovectorLip : MetricSpace M := F.metricSpace
      LipschitzWith 1 u)
    {c : ℝ → M} {a b t : ℝ} (hab : a < b)
    (hiso : let _instIntervalChartCovectorIso : MetricSpace M := F.metricSpace
      Isometry (fun r : Icc a b ↦ c r))
    (hsat : u (c b) - u (c a) = b - a) (ht : t ∈ Icc a b)
    (hchart : c t ∈ (extChartAt 𝓘(ℝ, E) old).source)
    (hc : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) c t)
    (hunit : F.toFun (tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) c ⟨t, (1 : ℝ)⟩) = 1)
    (hd : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ) u (c t)) :
    ∃ w : E, (extChartAt 𝓘(ℝ, E) old (c t), w) ∈ chartEnergyDomain old ∧
      fiberLegendre (F.chartEnergy old) (extChartAt 𝓘(ℝ, E) old (c t), w) =
        fderiv ℝ (u ∘ (extChartAt 𝓘(ℝ, E) old).symm) (extChartAt 𝓘(ℝ, E) old (c t)) ∧
      F.chartEnergy old (extChartAt 𝓘(ℝ, E) old (c t), w) = (1 / 2 : ℝ) := by
  exact hF.exists_chart_unit_covector_of_intrinsic old hchart hd
    (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) c t 1) (by exact_mod_cast hunit)
    (hF.mfderiv_eq_fiberEnergy_of_calibrated_closedInterval hu hab hiso hsat ht hc hunit hd)

end ContinuousFinslerNorm.IsSmoothStronglyConvex
end OTSelector.Geometry

end
end
