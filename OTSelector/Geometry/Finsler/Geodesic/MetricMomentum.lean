import OTSelector.Analysis.Calculus.WeakDerivative.Covector
import OTSelector.Analysis.Convex.Legendre.Parametric
import OTSelector.Geometry.Finsler.Basic
import OTSelector.Geometry.Finsler.Calibration.Chart
import OTSelector.Geometry.Finsler.Energy.Basic
import OTSelector.Geometry.Finsler.Energy.Chart
import OTSelector.Geometry.Finsler.Energy.Compact
import OTSelector.Geometry.Finsler.Geodesic.Energy
import OTSelector.Geometry.Finsler.Geodesic.MetricWeakEulerLagrange
import OTSelector.Geometry.Finsler.Hamiltonian.Basic
import OTSelector.Geometry.Finsler.LengthMetric
import OTSelector.Geometry.Finsler.MetricDifferential
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Geometry.FinslerMetricMomentum.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Geometry.FinslerMetricMomentum`; the selected original proof blocks follow. -/
section

/-!
# Geometry.Finsler.Geodesic.MetricMomentum

* **Conditions:** A metric isometric interval with the compact slit phase supplied by weak Euler–Lagrange; the private integrability helper only needs finite measure and compact AE range.
* **Objects:** Integrable actual momentum and base forcing, and a continuous momentum representative C+∫q with the correct AE derivative.
* **Proof detail:** Bound continuous phase functions on the compact AE range, subtract an indefinite forcing integral, and use the weak constant principle componentwise in the finite-dimensional dual.

Mathematical sources:
- [Sheldon Axler, Measure, Integration & Real Analysis (author PDF, 12 June 2026)](https://measure.axler.net/MIRA.pdf#page=99): Section 3A, Theorem 3.23, p. 84; Section 3B, Theorem 3.25, p. 88.
- [J. M. Ball; E. C. M. Crooks, Local minimizers and planar interfaces in a phase-transition model with interfacial energy (2011)](https://people.maths.ox.ac.uk/~ball/Papers/BallAndCrooks2011.pdf#page=12): Section 3, proof of Lemma 3.1, equation (3.5), p. 512 (du Bois–Reymond constant principle).
- [D. H. Fremlin, Measure Theory, Volume 2, Chapter 22](https://www1.essex.ac.uk/maths/people/fremlin/chap22.pdf#page=29): Section 225E, p. 29 (absolute continuity and indefinite integral); Section 225F, p. 30 (integration by parts).

Source relation (derived): The weak constant principle is adapted from scalar test functions to dual-valued finite-interval L1 data; the forcing primitive is then reconstructed by FTC.
-/

/-!
# Continuous actual momentum for original-distance minimizing intervals

On the interval already provided by the weak Euler--Lagrange theorem, the original
isometry has a compact coordinate image and an almost everywhere compact unit-speed
slit phase. The actual base and fiber differentials are therefore integrable. The
covector weak derivative theorem constructs a continuous actual momentum representative
with the correct almost everywhere forcing derivative, without a regularity assumption
on the original momentum or the central curve.
-/

open Set Filter Metric Manifold MeasureTheory
open scoped Topology ContDiff NNReal

noncomputable section

namespace OTSelector.Geometry

private theorem integrable_comp_of_compact_ae
    {H V : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H] [FiniteDimensional ℝ H]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ]
    {K : Set H} (hK : IsCompact K) {f : H → V} (hf : ContinuousOn f K)
    {z : α → H} (hz : AEStronglyMeasurable z μ) (hzK : ∀ᵐ t ∂μ, z t ∈ K) :
    Integrable (fun t ↦ f (z t)) μ := by
  classical
  borelize H V
  have hm : Measurable (K.piecewise f 0) :=
    hf.measurable_piecewise continuous_zero.continuousOn hK.measurableSet
  have hmeas : AEStronglyMeasurable (fun t ↦ f (z t)) μ := by
    apply ((hm.comp_aemeasurable hz.aemeasurable).aestronglyMeasurable).congr
    filter_upwards [hzK] with t ht
    exact piecewise_eq_of_mem K f 0 ht
  obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn hf
  apply Integrable.of_bound hmeas B
  filter_upwards [hzK] with t ht
  exact hB (z t) ht

namespace ContinuousFinslerNorm.IsSmoothStronglyConvex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [PreconnectedSpace M]
  {F : ContinuousFinslerNorm E M}

set_option backward.isDefEq.respectTransparency false in
/-- Every original-distance minimizing interval has, near each interior time, a
continuous representative of its actual coordinate momentum with the actual weak
forcing derivative. The compact phase and coefficient integrability are constructed. -/
theorem exists_continuous_chartMomentum_of_isometric_interval (hF : F.IsSmoothStronglyConvex)
    {c : ℝ → M} {a b t₀ : ℝ} (ht₀ : t₀ ∈ Ioo a b)
    (hiso : letI : MetricSpace M := F.metricSpace
      Isometry (fun t : Icc a b ↦ c t)) :
    let χ := extChartAt 𝓘(ℝ, E) (c t₀)
    let x := χ ∘ c
    let z := fun t ↦ (x t, deriv x t)
    let p := fun t ↦ fiberLegendre (F.chartEnergy (c t₀)) (z t)
    let q := fun t ↦ baseEnergyDifferential (F.chartEnergy (c t₀)) (z t)
    ∃ δ > (0 : ℝ), ∃ K : Set (E × E), ∃ C : E →L[ℝ] ℝ,
      Icc (t₀ - δ) (t₀ + δ) ⊆ Ioo a b ∧
      MapsTo c (Icc (t₀ - δ) (t₀ + δ)) χ.source ∧
      ContinuousOn x (Icc (t₀ - δ) (t₀ + δ)) ∧
      IsCompact K ∧ K ⊆ chartEnergyDomain (c t₀) ∧
      (∀ᵐ t ∂volume.restrict (Ioo (t₀ - δ) (t₀ + δ)), z t ∈ K) ∧
      IntervalIntegrable p volume (t₀ - δ) (t₀ + δ) ∧
      IntervalIntegrable q volume (t₀ - δ) (t₀ + δ) ∧
      (p =ᵐ[volume.restrict (Ioo (t₀ - δ) (t₀ + δ))]
        (fun t ↦ C + ∫ s in (t₀ - δ)..t, q s)) ∧
      ContinuousOn (fun t ↦ C + ∫ s in (t₀ - δ)..t, q s)
        (Icc (t₀ - δ) (t₀ + δ)) ∧
      (∀ᵐ t ∂volume.restrict (Ioo (t₀ - δ) (t₀ + δ)),
        HasDerivAt (fun u ↦ C + ∫ s in (t₀ - δ)..u, q s) (q t) t) := by
  let : MetricSpace M := F.metricSpace
  let χ := extChartAt 𝓘(ℝ, E) (c t₀)
  let x : ℝ → E := χ ∘ c
  let z : ℝ → E × E := fun t ↦ (x t, deriv x t)
  let p : ℝ → E →L[ℝ] ℝ := fun t ↦ fiberLegendre (F.chartEnergy (c t₀)) (z t)
  let q : ℝ → E →L[ℝ] ℝ := fun t ↦ baseEnergyDifferential (F.chartEnergy (c t₀)) (z t)
  obtain ⟨δ, hδ, hsub, hsource, hweak⟩ :=
    hF.exists_chart_weak_eulerLagrange_of_isometric_interval ht₀ hiso
  have hab : t₀ - δ ≤ t₀ + δ := by linarith
  have hisolocal : Isometry (fun t : Icc (t₀ - δ) (t₀ + δ) ↦ c t) := by
    intro u v
    exact hiso.edist_eq ⟨u, Ioo_subset_Icc_self (hsub u.property)⟩
      ⟨v, Ioo_subset_Icc_self (hsub v.property)⟩
  have hc : ContinuousOn c (Icc (t₀ - δ) (t₀ + δ)) :=
    continuousOn_iff_continuous_domRestrict.mpr hisolocal.continuous
  have hx : ContinuousOn x (Icc (t₀ - δ) (t₀ + δ)) :=
    (continuousOn_extChartAt (c t₀)).comp hc hsource
  let B : Set E := x '' Icc (t₀ - δ) (t₀ + δ)
  have hB : IsCompact B := isCompact_Icc.image_of_continuousOn hx
  have hBtarget : B ⊆ χ.target := by
    rintro u ⟨t, ht, rfl⟩
    exact χ.map_source (hsource ht)
  let K : Set (E × E) := {w | w.1 ∈ B ∧
    (F.chartLength (c t₀) w : ℝ) ∈ Icc 1 1}
  have hK : IsCompact K := F.isCompact_chartSpeed_range (c t₀) hB hBtarget 1 1
  have hKU : K ⊆ chartEnergyDomain (c t₀) :=
    F.chartSpeed_range_subset_domain (c t₀) hBtarget (by norm_num)
  have hphase : ∀ᵐ t ∂volume.restrict (Ioo (t₀ - δ) (t₀ + δ)), z t ∈ K := by
    filter_upwards [hF.ae_unit_speed_of_isometric_interval hisolocal,
      ae_restrict_mem measurableSet_Ioo] with t hunit ht
    have hs : c t ∈ (chartAt E (c t₀)).source := by
      simpa only [← extChartAt_source 𝓘(ℝ, E)] using hsource (Ioo_subset_Icc_self ht)
    have hxdiff : DifferentiableAt ℝ x t := by
      exact ((mdifferentiableAt_iff_target_of_mem_source hs).mp hunit.1).2.differentiableAt
    have hspeed := F.speed_eq_chartLength (c t₀) isOpen_Ioo ht
      (fun u hu ↦ hsource (Ioo_subset_Icc_self hu)) hxdiff
    change F.toFun (tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) c ⟨t, (1 : ℝ)⟩) =
      F.chartLength (c t₀) (z t) at hspeed
    refine ⟨mem_image_of_mem x (Ioo_subset_Icc_self ht), ?_⟩
    rw [← hspeed, hunit.2.2]
    norm_num
  have hz : AEStronglyMeasurable z (volume.restrict (Ioo (t₀ - δ) (t₀ + δ))) :=
    ((hx.mono Ioo_subset_Icc_self).aestronglyMeasurable measurableSet_Ioo).prodMk
      (aestronglyMeasurable_deriv x _)
  have hpc : ContinuousOn (fiberLegendre (F.chartEnergy (c t₀))) K := by
    intro w hw
    exact (contDiffAt_fiberLegendre ((hF.contDiffOn_chartEnergy (c t₀)).contDiffAt
      ((isOpen_chartEnergyDomain (c t₀)).mem_nhds (hKU hw)))).continuousAt.continuousWithinAt
  have hqc : ContinuousOn (baseEnergyDifferential (F.chartEnergy (c t₀))) K := by
    intro w hw
    exact (contDiffAt_baseEnergyDifferential ((hF.contDiffOn_chartEnergy (c t₀)).contDiffAt
      ((isOpen_chartEnergyDomain (c t₀)).mem_nhds (hKU hw)))).continuousAt.continuousWithinAt
  have hp : IntervalIntegrable p volume (t₀ - δ) (t₀ + δ) := by
    apply (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mpr
    change Integrable _ (volume.restrict (Ioc (t₀ - δ) (t₀ + δ)))
    rw [← restrict_Ioo_eq_restrict_Ioc]
    exact integrable_comp_of_compact_ae hK hpc hz hphase
  have hq : IntervalIntegrable q volume (t₀ - δ) (t₀ + δ) := by
    apply (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mpr
    change Integrable _ (volume.restrict (Ioc (t₀ - δ) (t₀ + δ)))
    rw [← restrict_Ioo_eq_restrict_Ioc]
    exact integrable_comp_of_compact_ae hK hqc hz hphase
  obtain ⟨C, hCeq, hCcont, hCd⟩ :=
    exists_ae_eq_const_add_integral_of_covector_weak_derivative hab hp hq hweak
  exact ⟨δ, hδ, K, C, hsub, hsource, hx, hK, hKU, hphase, hp, hq, hCeq, hCcont, hCd⟩

end ContinuousFinslerNorm.IsSmoothStronglyConvex
end OTSelector.Geometry

end
end
