import OTSelector.Geometry.Finsler.Basic
import OTSelector.Geometry.Finsler.Energy.Basic
import OTSelector.Geometry.Finsler.LengthMetric
import OTSelector.Geometry.Finsler.MetricDifferential
import OTSelector.Geometry.Finsler.Variation.First
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Geometry.FinslerMetricMinimizerEnergy.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Geometry.FinslerMetricMinimizerEnergy`; the selected original proof blocks follow. -/
section

/-!
# Geometry.Finsler.Geodesic.MetricMinimizerEnergy

* **Conditions:** A smooth strongly convex Finsler norm and an original-distance isometric closed interval.
* **Objects:** Actual integrated path length equal to duration, distance equal to path length, and energy action equal to half the duration.
* **Proof detail:** The actual speed is one almost everywhere; integrate this equality and F²/2, using the isometry for endpoint distance.

Mathematical sources:
- [Zhongmin Shen, Landsberg Curvature, S-Curvature and Riemann Curvature, in Riemann–Finsler Geometry, MSRI Publications 50 (2004)](https://library.slmath.org/books/Book50/files/08Sh.pdf#page=11): Section 4, p. 313: the length integral, induced distance and minimizing curves.
- [D. H. Fremlin, Measure Theory, Volume 2, Chapter 26](https://www1.essex.ac.uk/maths/people/fremlin/chap26.pdf#page=18): Section 262Q, Rademacher theorem and proof, pp. 18–20; Section 262B(c), p. 10 (Lipschitz implies absolutely continuous on bounded intervals).

Source relation (derived): These are exact integral consequences of the prior metric differential and the unit-speed premise.
-/

/-!
# Exact length and energy of original-distance minimizing intervals

The almost-everywhere unit speed theorem identifies the original tangent-integral
length and energy of any isometric interval. No smoothness of the minimizing curve
is assumed. The energy uses the existing action of the original Finsler norm.
-/

open Set MeasureTheory Manifold Metric
open scoped NNReal ENNReal ContDiff

noncomputable section

namespace OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [PreconnectedSpace M]
  {F : ContinuousFinslerNorm E M}

/-- The actual tangent-integral length of an arbitrary original-distance isometric
interval equals its elapsed time, without a smoothness premise. -/
theorem pathELength_eq_of_isometric_interval (hF : F.IsSmoothStronglyConvex)
    {c : ℝ → M} {a b : ℝ}
    (hiso : letI : MetricSpace M := F.metricSpace
      Isometry (fun t : Icc a b ↦ c t)) :
    letI : ∀ x : M, ENorm (TangentSpace 𝓘(ℝ, E) x) := F.enorm
    pathELength 𝓘(ℝ, E) c a b = ENNReal.ofReal (b - a) := by
  let : ∀ x : M, ENorm (TangentSpace 𝓘(ℝ, E) x) := F.enorm
  rw [pathELength_eq_lintegral_mfderiv_Ioo]
  calc
    _ = ∫⁻ _ in Ioo a b, (1 : ℝ≥0∞) := by
      apply lintegral_congr_ae
      filter_upwards [hF.ae_unit_speed_of_isometric_interval hiso] with t ht
      change (F.toFun (tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) c ⟨t, (1 : ℝ)⟩) : ℝ≥0∞) = 1
      rw [ht.2.2, ENNReal.coe_one]
    _ = ENNReal.ofReal (b - a) := by simp

/-- An original-distance isometric interval realizes its distance also through the
integral of actual Finsler tangent lengths. -/
theorem lengthEDist_eq_pathELength_of_isometric_interval (hF : F.IsSmoothStronglyConvex)
    {c : ℝ → M} {a b : ℝ} (hab : a ≤ b)
    (hiso : letI : MetricSpace M := F.metricSpace
      Isometry (fun t : Icc a b ↦ c t)) :
    letI : ∀ x : M, ENorm (TangentSpace 𝓘(ℝ, E) x) := F.enorm
    F.lengthEDist (c a) (c b) = pathELength 𝓘(ℝ, E) c a b := by
  let : MetricSpace M := F.metricSpace
  rw [hF.pathELength_eq_of_isometric_interval hiso]
  have hd := hiso.edist_eq (⟨a, le_rfl, hab⟩ : Icc a b) ⟨b, hab, le_rfl⟩
  change F.lengthEDist (c a) (c b) = edist a b at hd
  rw [hd, edist_dist, Real.dist_eq, abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr hab)]

/-- The existing original Finsler energy action of an isometric interval is half
its elapsed time, with the almost-everywhere derivative interpreted intrinsically. -/
theorem curveEnergyAction_eq_of_isometric_interval (hF : F.IsSmoothStronglyConvex)
    {c : ℝ → M} {a b : ℝ} (hab : a ≤ b)
    (hiso : letI : MetricSpace M := F.metricSpace
      Isometry (fun t : Icc a b ↦ c t)) :
    F.curveEnergyAction c a b = (b - a) / 2 := by
  unfold ContinuousFinslerNorm.curveEnergyAction
  calc
    _ = ∫ _ in a..b, (1 / 2 : ℝ) := by
      apply intervalIntegral.integral_congr_ae_restrict
      rw [uIoc_of_le hab, ← restrict_Ioo_eq_restrict_Ioc]
      filter_upwards [hF.ae_unit_speed_of_isometric_interval hiso] with t ht
      simp only [ContinuousFinslerNorm.energy, ht.2.2, NNReal.coe_one, one_pow]
    _ = (b - a) / 2 := by simp [smul_eq_mul, div_eq_mul_inv]

end OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

end
end
