import OTSelector.Geometry.Finsler.Basic
import OTSelector.Geometry.Finsler.LengthMetric
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Geometry.FinslerMetricVelocity.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Geometry.FinslerMetricVelocity`; the selected original proof blocks follow. -/
section

/-!
# Geometry.Finsler.Geodesic.MetricVelocity

* **Conditions:** A differentiable interior time of a curve isometric for the original length metric on a closed interval.
* **Objects:** Nonzero centered coordinate derivative and nonzero intrinsic manifold velocity.
* **Proof detail:** The local distance upper bound gives a positive lower bound on coordinate difference quotients, contradicting a zero derivative.

Mathematical sources:
- [Zhongmin Shen, Landsberg Curvature, S-Curvature and Riemann Curvature, in Riemann–Finsler Geometry, MSRI Publications 50 (2004)](https://library.slmath.org/books/Book50/files/08Sh.pdf#page=11): Section 4, p. 313: the length integral, induced distance and minimizing curves.
- [Jiří Lebl, Basic Analysis II: Introduction to Real Analysis, Volume II](https://www.jirka.org/ra/realanal2.pdf): Sections 8.3–8.4, total derivative, chain rule and mean-value bounds; Section 8.6, higher derivatives.

Source relation (derived): An elementary corollary of local Finsler metric comparison and differentiation, rather than a quoted named theorem.
-/

/-!
# Nonzero velocities of differentiable metric isometric curves

The original Finsler length distance has a local upper bound by centered chart
displacement. An isometric curve therefore has a coordinate difference quotient
bounded away from zero. At a differentiable interior time its actual coordinate
velocity, and hence its actual manifold velocity, cannot vanish.
-/

open Set Manifold Filter Metric
open scoped NNReal ENNReal ContDiff Topology

noncomputable section

namespace OTSelector.Geometry.ContinuousFinslerNorm

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) 1 M]
  [FiniteDimensional ℝ E] [T2Space M] [PreconnectedSpace M]
  (F : ContinuousFinslerNorm E M)

set_option backward.isDefEq.respectTransparency false in
/-- An original-distance isometric curve has nonzero centered coordinate velocity at every
manifold-differentiable interior time. -/
theorem deriv_extChartAt_comp_ne_zero_of_isometry {c : ℝ → M} {a b t₀ : ℝ}
    (ht₀ : t₀ ∈ Ioo a b)
    (hc : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) c t₀)
    (hiso : letI : MetricSpace M := F.metricSpace
      Isometry (fun t : Icc a b ↦ c t)) :
    deriv (extChartAt 𝓘(ℝ, E) (c t₀) ∘ c) t₀ ≠ 0 := by
  let : MetricSpace M := F.metricSpace
  let f : ℝ → E := extChartAt 𝓘(ℝ, E) (c t₀) ∘ c
  have hχ : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, E)
      (extChartAt 𝓘(ℝ, E) (c t₀)) (c t₀) :=
    mdifferentiableAt_extChartAt (mem_chart_source E (c t₀))
  have hdf : HasDerivAt f (deriv f t₀) t₀ :=
    (hχ.comp t₀ hc).differentiableAt.hasDerivAt
  intro hzero
  change deriv f t₀ = 0 at hzero
  rw [hzero] at hdf
  obtain ⟨C, _, hC⟩ := F.eventually_edist_le_edist_extChartAt (c t₀)
  have hnear : ∀ᶠ s in 𝓝 t₀, edist (c t₀) (c s) ≤ C * edist (f t₀) (f s) :=
    hc.continuousAt.eventually hC
  have hlim : Tendsto (fun s ↦ (C : ℝ) * ‖slope f t₀ s‖) (𝓝[≠] t₀) (𝓝 0) := by
    simpa only [norm_zero, mul_zero] using hdf.tendsto_slope.norm.const_mul (C : ℝ)
  have hIcc : ∀ᶠ s in 𝓝 t₀, s ∈ Icc a b := Icc_mem_nhds ht₀.1 ht₀.2
  have hlow : ∀ᶠ s in 𝓝[≠] t₀, (1 : ℝ) ≤ (C : ℝ) * ‖slope f t₀ s‖ := by
    filter_upwards [hnear.filter_mono nhdsWithin_le_nhds,
      hIcc.filter_mono nhdsWithin_le_nhds,
      self_mem_nhdsWithin] with s hs hsI hsne
    have hsne' : s ≠ t₀ := hsne
    have hnorm : ‖s - t₀‖ ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr hsne')
    have hreal : dist (c t₀) (c s) ≤ (C : ℝ) * dist (f t₀) (f s) := by
      have h := ENNReal.toReal_mono
        (ENNReal.mul_ne_top ENNReal.coe_ne_top (edist_ne_top _ _)) hs
      simpa only [ENNReal.toReal_mul, ENNReal.coe_toReal, ← dist_edist] using h
    have hiso' := hiso.dist_eq (⟨t₀, ht₀.1.le, ht₀.2.le⟩ : Icc a b) ⟨s, hsI⟩
    change dist (c t₀) (c s) = dist t₀ s at hiso'
    rw [hiso', dist_eq_norm, dist_eq_norm, norm_sub_rev t₀ s,
      norm_sub_rev (f t₀) (f s)] at hreal
    calc
      1 = ‖s - t₀‖⁻¹ * ‖s - t₀‖ := (inv_mul_cancel₀ hnorm).symm
      _ ≤ ‖s - t₀‖⁻¹ * ((C : ℝ) * ‖f s - f t₀‖) :=
        mul_le_mul_of_nonneg_left hreal (by positivity)
      _ = (C : ℝ) * ‖slope f t₀ s‖ := by
        rw [slope_def_module, norm_smul, norm_inv]
        ring
  have hfalse : (1 : ℝ) ≤ 0 := le_of_tendsto_of_tendsto tendsto_const_nhds hlim hlow
  norm_num at hfalse

set_option backward.isDefEq.respectTransparency false in
/-- The actual tangent velocity of an original-distance isometric curve is nonzero at
any manifold-differentiable interior time. -/
theorem mfderiv_apply_one_ne_zero_of_isometry {c : ℝ → M} {a b t₀ : ℝ}
    (ht₀ : t₀ ∈ Ioo a b)
    (hc : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) c t₀)
    (hiso : letI : MetricSpace M := F.metricSpace
      Isometry (fun t : Icc a b ↦ c t)) :
    mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) c t₀ 1 ≠ 0 := by
  have hχ : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, E)
      (extChartAt 𝓘(ℝ, E) (c t₀)) (c t₀) :=
    mdifferentiableAt_extChartAt (mem_chart_source E (c t₀))
  have hd := mfderiv_comp_apply t₀ hχ hc (1 : ℝ)
  simp only [mfderiv_eq_fderiv] at hd
  have hd' : deriv (extChartAt 𝓘(ℝ, E) (c t₀) ∘ c) t₀ =
      mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (extChartAt 𝓘(ℝ, E) (c t₀)) (c t₀)
        (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) c t₀ 1) :=
    (fderiv_apply_one_eq_deriv (𝕜 := ℝ)).symm.trans hd
  intro hzero
  apply F.deriv_extChartAt_comp_ne_zero_of_isometry ht₀ hc hiso
  rw [hd', hzero, _root_.map_zero]

end OTSelector.Geometry.ContinuousFinslerNorm

end
end
