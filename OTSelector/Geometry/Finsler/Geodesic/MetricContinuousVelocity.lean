import OTSelector.Analysis.Convex.Legendre.Parametric
import OTSelector.Geometry.Finsler.Basic
import OTSelector.Geometry.Finsler.Energy.Basic
import OTSelector.Geometry.Finsler.Energy.Chart
import OTSelector.Geometry.Finsler.Geodesic.MetricMomentum
import OTSelector.Geometry.Finsler.Hamiltonian.Basic
import OTSelector.Geometry.Finsler.LegendreInjectivity
import OTSelector.Geometry.Finsler.LengthMetric
import OTSelector.Topology.CompactAEContinuousLift
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Geometry.FinslerMetricContinuousVelocity.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Geometry.FinslerMetricContinuousVelocity`; the selected original proof blocks follow. -/
section

/-!
# Geometry.Finsler.Geodesic.MetricContinuousVelocity

* **Conditions:** The continuous actual momentum and compact nonzero phase for an original-distance isometric interval, together with strong convexity.
* **Objects:** A continuous nonzero velocity lifting the position–momentum curve, equal almost everywhere to the original coordinate derivative.
* **Proof detail:** Use compact injectivity of the parametric Legendre map to get a continuous inverse on its compact image, recover velocity, and retain the forcing primitive identity.

Mathematical sources:
- [Zhongmin Shen, Landsberg Curvature, S-Curvature and Riemann Curvature, MSRI Publications 50 (2004)](https://library.slmath.org/books/Book50/files/08Sh.pdf#page=6): Section 2, p. 308, Legendre transformation, inverse Legendre transformation and equation (2–12).
- [Terence Tao, An Epsilon of Room, I: Real Analysis (author preliminary version)](https://terrytao.wordpress.com/wp-content/uploads/2012/12/gsm-117-tao3-epsilon1.pdf#page=110): Sections 1.6.2 and 1.8.1, compactness by finite subcovers, pp. 78 and 101–102; Section 1.8.3, Proposition 1.8.10, pp. 107–108 (finite products).
- [D. H. Fremlin, Measure Theory, Volume 2, Chapter 22](https://www1.essex.ac.uk/maths/people/fremlin/chap22.pdf#page=29): Section 225E, p. 29 (absolute continuity and indefinite integral); Section 225F, p. 30 (integration by parts).

Source relation (derived): Compact inverse continuity, rather than a global smooth Legendre inverse, supplies the local continuous representative.
-/

/-!
# Continuous actual velocity for original-distance minimizing intervals

The actual continuous momentum and position lift through the compact, injective
parametric Legendre map. The resulting continuous velocity is nonzero throughout
the closed local interval and agrees almost everywhere with the actual coordinate
derivative. The momentum retains its original integral formula and has the actual
continuous-phase forcing as its almost everywhere derivative.
-/

open Set Filter Metric Manifold MeasureTheory
open scoped Topology ContDiff NNReal

noncomputable section

namespace OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [PreconnectedSpace M]
  {F : ContinuousFinslerNorm E M}

set_option backward.isDefEq.respectTransparency false in
/-- The original-distance minimizing interval admits a continuous nonzero coordinate
velocity and continuous actual momentum on a closed neighborhood of each interior
time, with the actual momentum identity holding pointwise. -/
theorem exists_continuous_chartVelocity_of_isometric_interval (hF : F.IsSmoothStronglyConvex)
    {c : ℝ → M} {a b t₀ : ℝ} (ht₀ : t₀ ∈ Ioo a b)
    (hiso : letI : MetricSpace M := F.metricSpace
      Isometry (fun t : Icc a b ↦ c t)) :
    let χ := extChartAt 𝓘(ℝ, E) (c t₀)
    let x := χ ∘ c
    let q := fun t ↦ baseEnergyDifferential (F.chartEnergy (c t₀)) (x t, deriv x t)
    ∃ δ > (0 : ℝ), ∃ C : E →L[ℝ] ℝ, ∃ v : ℝ → E,
      let P := fun t ↦ C + ∫ s in (t₀ - δ)..t, q s
      Icc (t₀ - δ) (t₀ + δ) ⊆ Ioo a b ∧
      MapsTo c (Icc (t₀ - δ) (t₀ + δ)) χ.source ∧
      ContinuousOn x (Icc (t₀ - δ) (t₀ + δ)) ∧
      ContinuousOn v (Icc (t₀ - δ) (t₀ + δ)) ∧
      ContinuousOn P (Icc (t₀ - δ) (t₀ + δ)) ∧
      (∀ t ∈ Icc (t₀ - δ) (t₀ + δ), (x t, v t) ∈ chartEnergyDomain (c t₀)) ∧
      (∀ t ∈ Icc (t₀ - δ) (t₀ + δ),
        P t = fiberLegendre (F.chartEnergy (c t₀)) (x t, v t)) ∧
      IntervalIntegrable q volume (t₀ - δ) (t₀ + δ) ∧
      (v =ᵐ[volume.restrict (Ioo (t₀ - δ) (t₀ + δ))] deriv x) ∧
      (∀ᵐ t ∂volume.restrict (Ioo (t₀ - δ) (t₀ + δ)),
        HasDerivAt P (baseEnergyDifferential (F.chartEnergy (c t₀)) (x t, v t)) t) := by
  let χ := extChartAt 𝓘(ℝ, E) (c t₀)
  let x : ℝ → E := χ ∘ c
  let z : ℝ → E × E := fun t ↦ (x t, deriv x t)
  let L := F.chartEnergy (c t₀)
  let q : ℝ → E →L[ℝ] ℝ := fun t ↦ baseEnergyDifferential L (z t)
  obtain ⟨δ, hδ, K, C, hsub, hsource, hx, hK, hKU, hz, _, hq, hp, hP, hPd⟩ :=
    hF.exists_continuous_chartMomentum_of_isometric_interval ht₀ hiso
  let P : ℝ → E →L[ℝ] ℝ := fun t ↦ C + ∫ s in (t₀ - δ)..t, q s
  let α : ℝ → E × (E →L[ℝ] ℝ) := fun t ↦ (x t, P t)
  have hT : ContinuousOn (parametricLegendre L) K := by
    intro w hw
    exact (contDiffAt_parametricLegendre ((hF.contDiffOn_chartEnergy (c t₀)).contDiffAt
      ((isOpen_chartEnergyDomain (c t₀)).mem_nhds (hKU hw)))).continuousAt.continuousWithinAt
  have hinj : InjOn (parametricLegendre L) K :=
    (hF.injOn_parametricLegendre_chartEnergy (c t₀)).mono hKU
  have hα : ContinuousOn α (Icc (t₀ - δ) (t₀ + δ)) := hx.prodMk hP
  have heq : α =ᵐ[volume.restrict (Ioo (t₀ - δ) (t₀ + δ))]
      (parametricLegendre L) ∘ z := by
    filter_upwards [hp] with t ht
    exact Prod.ext rfl ht.symm
  obtain ⟨zbar, hzc, hzK, hzT, hzeq⟩ := exists_continuous_lift_of_compact_ae
    (by linarith : t₀ - δ < t₀ + δ) hK hT hinj hα hz heq
  have hzfst (t : ℝ) (ht : t ∈ Icc (t₀ - δ) (t₀ + δ)) : (zbar t).1 = x t :=
    congrArg Prod.fst (hzT ht)
  have hpair (t : ℝ) (ht : t ∈ Icc (t₀ - δ) (t₀ + δ)) :
      (x t, (zbar t).2) = zbar t := by
    rw [← hzfst t ht]
  have hv : (fun t ↦ (zbar t).2) =ᵐ[volume.restrict (Ioo (t₀ - δ) (t₀ + δ))]
      deriv x := by
    filter_upwards [hzeq] with t ht
    exact congrArg Prod.snd ht
  refine ⟨δ, hδ, C, fun t ↦ (zbar t).2, hsub, hsource, hx, hzc.snd, hP, ?_, ?_, hq, hv, ?_⟩
  · intro t ht
    rw [hpair t ht]
    exact hKU (hzK ht)
  · intro t ht
    change P t = fiberLegendre L (x t, (zbar t).2)
    rw [hpair t ht]
    exact (congrArg Prod.snd (hzT ht)).symm
  · filter_upwards [hPd, hv] with t ht hvt
    rw [hvt]
    exact ht

end OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

end
end
