import OTSelector.Geometry.Finsler.Basic
import OTSelector.Geometry.Finsler.Energy.Basic
import OTSelector.Geometry.Finsler.Energy.Lipschitz
import OTSelector.Geometry.Finsler.Geodesic.MetricMinimizerEnergy
import OTSelector.Geometry.Finsler.LengthMetric
import OTSelector.Geometry.Finsler.LipschitzLength
import OTSelector.Geometry.Finsler.Variation.First
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Geometry.FinslerMetricMinimizerComparison.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Geometry.FinslerMetricMinimizerComparison`; the selected original proof blocks follow. -/
section

/-!
# Geometry.Finsler.Geodesic.MetricMinimizerComparison

* **Conditions:** An original-metric isometric interval and an interval-Lipschitz competitor with the same endpoints.
* **Objects:** Actual length as an integral of speed, distance–action bounds, and energy minimality of the isometric interval.
* **Proof detail:** Use speed ≤ speed²/2+1/2 pointwise, integrate it, compare endpoint distance with competitor length and use the exact unit-speed energy of the isometry.

Mathematical sources:
- [Zhongmin Shen, Landsberg Curvature, S-Curvature and Riemann Curvature, in Riemann–Finsler Geometry, MSRI Publications 50 (2004)](https://library.slmath.org/books/Book50/files/08Sh.pdf#page=11): Section 4, p. 313: the length integral, induced distance and minimizing curves.
- [Stephen Boyd; Lieven Vandenberghe, Convex Optimization](https://web.stanford.edu/~boyd/cvxbook/bv_cvxbook.pdf#page=108): Section 3.3.2, Fenchel’s inequality and quadratic example, p. 94.

Source relation (derived): The scalar quadratic Young inequality is specialized and integrated; the energy-minimality conclusion is derived without a smoothness premise on the minimizer.
-/

/-!
# Original energy minimality of metric minimizing intervals

The actual Finsler speed and energy of interval-Lipschitz curves are integrable.
Their length comparison and the scalar inequality `s ≤ s² / 2 + 1 / 2` show
that every original-distance isometric interval minimizes the original energy
among all interval-Lipschitz curves with the same endpoints.
-/

open Set MeasureTheory Manifold Metric Filter
open scoped NNReal ENNReal ContDiff

noncomputable section

namespace OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [PreconnectedSpace M]
  {F : ContinuousFinslerNorm E M}

omit [FiniteDimensional ℝ E] [T2Space M] [PreconnectedSpace M] in
private theorem pathELength_eq_ofReal_integral_speed
    {c : ℝ → M} {a b : ℝ} (hab : a ≤ b)
    (hi : IntervalIntegrable
      (fun t ↦ (F.toFun (tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) c ⟨t, (1 : ℝ)⟩) : ℝ))
      volume a b) :
    letI : ∀ x : M, ENorm (TangentSpace 𝓘(ℝ, E) x) := F.enorm
    pathELength 𝓘(ℝ, E) c a b = ENNReal.ofReal
      (∫ t in a..b, (F.toFun (tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) c ⟨t, (1 : ℝ)⟩) : ℝ)) := by
  let : ∀ x : M, ENorm (TangentSpace 𝓘(ℝ, E) x) := F.enorm
  rw [pathELength_eq_lintegral_mfderiv_Ioo, intervalIntegral.integral_of_le hab,
    integral_Ioc_eq_integral_Ioo, ofReal_integral_eq_lintegral_ofReal
      (hi.1.mono_set Ioo_subset_Ioc_self) (Eventually.of_forall (fun _ ↦ NNReal.coe_nonneg _))]
  apply lintegral_congr
  intro t
  exact ENNReal.ofReal_coe_nnreal.symm

/-- Original-metric interval-Lipschitz curves bound endpoint distance by the ordinary
integral of their actual Finsler speed; integrability is derived. -/
theorem dist_le_integral_speed_of_lipschitzOnWith (hF : F.IsSmoothStronglyConvex)
    {c : ℝ → M} {a b : ℝ} {K : ℝ≥0} (hab : a ≤ b)
    (hc : letI : MetricSpace M := F.metricSpace; LipschitzOnWith K c (Icc a b)) :
    letI : MetricSpace M := F.metricSpace
    dist (c a) (c b) ≤
      ∫ t in a..b, (F.toFun (tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) c ⟨t, (1 : ℝ)⟩) : ℝ) := by
  let : MetricSpace M := F.metricSpace
  have hi := hF.intervalIntegrable_speed_of_lipschitzOnWith hab hc
  have hlength := hF.lengthEDist_le_pathELength_of_lipschitzOnWith hab hc
  rw [pathELength_eq_ofReal_integral_speed hab hi] at hlength
  change edist (c a) (c b) ≤ _ at hlength
  rw [edist_dist] at hlength
  exact (ENNReal.ofReal_le_ofReal_iff
    (intervalIntegral.integral_nonneg hab (fun _ _ ↦ NNReal.coe_nonneg _))).mp hlength

/-- The original energy action of every interval-Lipschitz curve controls its endpoint
distance up to half the elapsed time, with no extra integrability assumption. -/
theorem dist_le_curveEnergyAction_add_half_of_lipschitzOnWith
    (hF : F.IsSmoothStronglyConvex) {c : ℝ → M} {a b : ℝ} {K : ℝ≥0} (hab : a ≤ b)
    (hc : letI : MetricSpace M := F.metricSpace; LipschitzOnWith K c (Icc a b)) :
    letI : MetricSpace M := F.metricSpace
    dist (c a) (c b) ≤ F.curveEnergyAction c a b + (b - a) / 2 := by
  let : MetricSpace M := F.metricSpace
  have hs := hF.intervalIntegrable_speed_of_lipschitzOnWith hab hc
  have he := hF.intervalIntegrable_energy_of_lipschitzOnWith hab hc
  have hconst : IntervalIntegrable (fun _ : ℝ ↦ (1 / 2 : ℝ)) volume a b :=
    intervalIntegrable_const
  have hbound := intervalIntegral.integral_mono hab hs (he.add hconst)
    (fun t ↦ show (F.toFun (tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) c ⟨t, (1 : ℝ)⟩) : ℝ) ≤
      F.energy (tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) c ⟨t, (1 : ℝ)⟩) + 1 / 2 by
        unfold ContinuousFinslerNorm.energy
        nlinarith [sq_nonneg ((F.toFun
          (tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) c ⟨t, (1 : ℝ)⟩) : ℝ) - 1)])
  rw [intervalIntegral.integral_add he hconst, intervalIntegral.integral_const,
    smul_eq_mul, ← mul_div_assoc, mul_one] at hbound
  exact (hF.dist_le_integral_speed_of_lipschitzOnWith hab hc).trans hbound

/-- Every original-distance isometric interval minimizes the original Finsler energy
among all Lipschitz curves on the same time interval with the same endpoints. -/
theorem curveEnergyAction_le_of_isometric_interval (hF : F.IsSmoothStronglyConvex)
    {c d : ℝ → M} {a b : ℝ} {K : ℝ≥0} (hab : a ≤ b)
    (hiso : letI : MetricSpace M := F.metricSpace
      Isometry (fun t : Icc a b ↦ c t))
    (hd : letI : MetricSpace M := F.metricSpace; LipschitzOnWith K d (Icc a b))
    (ha : d a = c a) (hb : d b = c b) :
    F.curveEnergyAction c a b ≤ F.curveEnergyAction d a b := by
  let : MetricSpace M := F.metricSpace
  rw [hF.curveEnergyAction_eq_of_isometric_interval hab hiso]
  have h := hF.dist_le_curveEnergyAction_add_half_of_lipschitzOnWith hab hd
  rw [ha, hb] at h
  have hdist := hiso.dist_eq (⟨a, le_rfl, hab⟩ : Icc a b) ⟨b, hab, le_rfl⟩
  change dist (c a) (c b) = dist a b at hdist
  rw [Real.dist_eq, abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr hab)] at hdist
  rw [hdist] at h
  linarith

end OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

end
end
