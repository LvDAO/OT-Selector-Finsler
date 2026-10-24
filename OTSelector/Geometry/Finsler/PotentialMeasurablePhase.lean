import OTSelector.Analysis.Convex.Legendre.Parametric
import OTSelector.Geometry.Finsler.Basic
import OTSelector.Geometry.Finsler.CalibratedCovector
import OTSelector.Geometry.Finsler.Energy.Basic
import OTSelector.Geometry.Finsler.Energy.Chart
import OTSelector.Geometry.Finsler.LegendreInjectivity
import OTSelector.Geometry.Finsler.LengthMetric
import OTSelector.Geometry.Finsler.LengthProjection
import OTSelector.Geometry.Finsler.MeasurableLegendre

/-!
# Geometry.Finsler.PotentialMeasurablePhase

* **Conditions:** An arbitrary original real potential and the actual chart Legendre range; calibration is required only for the partner/unit-energy corollaries.
* **Objects:** A Borel good phase domain and measurable actual recovered phase, whose nonzero Legendre covector forces genuine potential differentiability there.
* **Proof detail:** Use measurability of the totalized actual derivative, pull back the Borel Legendre range and compose its Borel inverse; identify derivative and energy on calibrated points.

Mathematical sources:
- [Sébastien Gouëzel; Yury Kudryashov, mathlib: Derivative is measurable (pinned formal primary source)](https://github.com/leanprover-community/mathlib4/blob/d77ef0741c6da1ff12df68fb4145ea0ae0850c54/Mathlib/Analysis/Calculus/FDeriv/Measurable.lean#L380): Mathlib/Analysis/Calculus/FDeriv/Measurable.lean, module proof description lines 17–55; measurableSet_of_differentiableAt_of_isComplete lines 362–367; measurableSet_of_differentiableAt lines 374–377; measurable_fderiv lines 380–390; measurable_fderiv_apply_const lines 393–395.
- [D. H. Fremlin, Measure Theory, Volume 4](https://www1.essex.ac.uk/maths/people/fremlin/chap42.pdf#page=22): Theorem 423I(a)–(b), pp. 22–23; Proposition 424G, p. 31.
- [Zhongmin Shen, Landsberg Curvature, S-Curvature and Riemann Curvature, MSRI Publications 50 (2004)](https://library.slmath.org/books/Book50/files/08Sh.pdf#page=6): Section 2, p. 308, Legendre transformation, inverse Legendre transformation and equation (2–12).

Source relation (derived): The arbitrary-potential derivative measurability is supported by the pinned formal proof, not misattributed to Rademacher for a measurable or continuous potential.
-/

/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Geometry.FinslerPotentialMeasurablePhase.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Geometry.FinslerPotentialMeasurablePhase`; the selected original proof blocks follow. -/
section

/-!
# Measurable actual phases of an original potential

For an arbitrary real potential, its actual chart derivative is measurable without assuming
the potential measurable. Membership of that covector in the actual slit Legendre range
defines a measurable good chart domain and a measurable recovered phase there. The nonzero
actual Legendre covector forces genuine differentiability of the original potential on this
domain. Calibrated differentiability points belong to it, and their recovered phase has unit
energy. All inverses and derivatives are those of the original Finsler structure.
-/

open Set Filter MeasureTheory Manifold
open scoped Topology ContDiff

noncomputable section
namespace OTSelector.Geometry.ContinuousFinslerNorm

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [MeasurableSpace M] [BorelSpace M]

/-- The base coordinate and actual coordinate differential of an arbitrary original potential. -/
def potentialChartMomentum (old : M) (u : M → ℝ) (x : M) : E × (E →L[ℝ] ℝ) :=
  (extChartAt 𝓘(ℝ, E) old x,
    fderiv ℝ (u ∘ (extChartAt 𝓘(ℝ, E) old).symm) (extChartAt 𝓘(ℝ, E) old x))

/-- The actual chart domain where the original potential covector has a slit Legendre inverse. -/
def potentialLegendreDomain (F : ContinuousFinslerNorm E M) (old : M) (u : M → ℝ) : Set M :=
  (extChartAt 𝓘(ℝ, E) old).source ∩
    (potentialChartMomentum (E := E) old u) ⁻¹' F.chartLegendreRange old

omit [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M] in
/-- Actual chart momentum is measurable on the chart source, with no assumption on the potential. -/
theorem measurable_potentialChartMomentum_source (old : M) (u : M → ℝ) :
    Measurable (fun x : (extChartAt 𝓘(ℝ, E) old).source ↦
      potentialChartMomentum (E := E) old u x.val) := by
  have hc : Measurable (fun x : (extChartAt 𝓘(ℝ, E) old).source ↦
      extChartAt 𝓘(ℝ, E) old x.val) :=
    (continuousOn_iff_continuous_domRestrict.mp (continuousOn_extChartAt old)).measurable
  exact hc.prodMk ((measurable_fderiv ℝ (u ∘ (extChartAt 𝓘(ℝ, E) old).symm)).comp hc)

namespace IsSmoothStronglyConvex

variable {F : ContinuousFinslerNorm E M} (hF : F.IsSmoothStronglyConvex)
include hF

/-- The good domain of the actual potential Legendre inverse is a Borel set in the manifold. -/
theorem measurableSet_potentialLegendreDomain (old : M) (u : M → ℝ) :
    MeasurableSet (F.potentialLegendreDomain old u) := by
  have hs := (isOpen_extChartAt_source (I := 𝓘(ℝ, E)) old).measurableSet
  have hm := (hF.measurableSet_chartLegendreRange old).preimage
    (measurable_potentialChartMomentum_source old u)
  have hi := hs.subtype_image hm
  convert hi using 1
  ext x
  simp [potentialLegendreDomain, and_comm]

/-- The phase is the actual inverse at the original potential's actual chart momentum. -/
def potentialLegendrePhase (old : M) (u : M → ℝ)
    (x : F.potentialLegendreDomain old u) : chartEnergyDomain (E := E) old :=
  (hF.chartLegendreEquivRange old).symm
    ⟨potentialChartMomentum (E := E) old u x.val, x.property.2⟩

/-- The actual recovered slit phase depends measurably on points of the good domain. -/
theorem measurable_potentialLegendrePhase (old : M) (u : M → ℝ) :
    Measurable (hF.potentialLegendrePhase old u) := by
  have hc : Measurable (fun x : F.potentialLegendreDomain old u ↦
      (⟨x.val, x.property.1⟩ : (extChartAt 𝓘(ℝ, E) old).source)) :=
    measurable_subtype_coe.subtype_mk
  exact (hF.chartLegendreEquivRange old).symm.measurable.comp
    ((measurable_potentialChartMomentum_source old u).comp hc).subtype_mk

/-- The velocity coordinate of the actual recovered phase is measurable. -/
theorem measurable_potentialLegendreVelocity (old : M) (u : M → ℝ) :
    Measurable (fun x : F.potentialLegendreDomain old u ↦
      (hF.potentialLegendrePhase old u x).val.2) :=
  measurable_snd.comp (measurable_subtype_coe.comp
    (hF.measurable_potentialLegendrePhase old u))

omit [MeasurableSpace M] [BorelSpace M] in
/-- The recovered phase keeps the original chart base and actual potential differential. -/
theorem potentialLegendrePhase_components (old : M) (u : M → ℝ)
    (x : F.potentialLegendreDomain old u) :
    (hF.potentialLegendrePhase old u x).val.1 = extChartAt 𝓘(ℝ, E) old x.val ∧
      fiberLegendre (F.chartEnergy old) (hF.potentialLegendrePhase old u x).val =
        fderiv ℝ (u ∘ (extChartAt 𝓘(ℝ, E) old).symm)
          (extChartAt 𝓘(ℝ, E) old x.val) ∧
      (hF.potentialLegendrePhase old u x).val.2 ≠ 0 :=
  hF.chartLegendreEquivRange_symm_components old _

omit [MeasurableSpace M] [BorelSpace M] in
/-- Inverting the base chart gives exactly the original manifold point. -/
theorem potentialLegendrePhase_base (old : M) (u : M → ℝ)
    (x : F.potentialLegendreDomain old u) :
    (extChartAt 𝓘(ℝ, E) old).symm (hF.potentialLegendrePhase old u x).val.1 = x.val := by
  rw [(hF.potentialLegendrePhase_components old u x).1]
  exact (extChartAt 𝓘(ℝ, E) old).left_inv x.property.1

omit [MeasurableSpace M] [BorelSpace M] in
/-- A genuine nonzero Legendre covector rules out the default zero derivative at a
nondifferentiability point, so every point in the good domain is actually differentiable. -/
theorem mdifferentiableAt_of_mem_potentialLegendreDomain (old : M) (u : M → ℝ)
    {x : M} (hx : x ∈ F.potentialLegendreDomain old u) :
    MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ) u x := by
  let z := hF.potentialLegendrePhase old u ⟨x, hx⟩
  have he := (hF.potentialLegendrePhase_components old u ⟨x, hx⟩).2.1
  have hp : 0 < fiberLegendre (F.chartEnergy old) z.val z.val.2 :=
    hF.chartMomentum_self_pos old z.property
  have hd : DifferentiableAt ℝ (u ∘ (extChartAt 𝓘(ℝ, E) old).symm)
      (extChartAt 𝓘(ℝ, E) old x) := by
    by_contra hn
    have hz : fiberLegendre (F.chartEnergy old) z.val = 0 :=
      he.trans (fderiv_zero_of_not_differentiableAt hn)
    rw [hz] at hp
    exact (lt_irrefl 0) hp
  apply (mdifferentiableAt_iff_source_of_mem_source
    (show x ∈ (chartAt E old).source by simpa only [extChartAt_source] using hx.1)).mpr
  simpa using hd.mdifferentiableAt.mdifferentiableWithinAt
    (s := Set.range (𝓘(ℝ, E) : E → E))

variable [T2Space M] [PreconnectedSpace M]

omit [MeasurableSpace E] [BorelSpace E] [MeasurableSpace M] [BorelSpace M] in
/-- Genuine calibrated differentiability points lie in the actual measurable good domain. -/
theorem mem_potentialLegendreDomain_of_calibrated_endpoints
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace) (old : M)
    {u : M → ℝ} (hu : let _instPotentialPhaseInclusionMetric : MetricSpace M := F.metricSpace
      LipschitzWith 1 u)
    {x y : M} (hx : x ∈ (extChartAt 𝓘(ℝ, E) old).source) (hxy : x ≠ y)
    (hsat : let _instPotentialPhaseInclusionSatMetric : MetricSpace M := F.metricSpace
      u y - u x = dist x y)
    (hd : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ) u x) :
    x ∈ F.potentialLegendreDomain old u := by
  obtain ⟨v, hv, hp, _⟩ :=
    hF.exists_chart_unit_legendre_of_calibrated_endpoints hcomplete old hx hu hxy hsat hd
  refine ⟨hx, ⟨⟨(extChartAt 𝓘(ℝ, E) old x, v), hv⟩, ?_⟩⟩
  exact Prod.ext rfl hp

omit [MeasurableSpace M] [BorelSpace M] in
/-- At a genuinely calibrated point in the good domain, the constructed same inverse phase
has unit energy. Its actual differentiability is derived from domain membership. -/
theorem potentialLegendrePhase_energy_of_calibrated_endpoints
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace) (old : M)
    {u : M → ℝ} (hu : let _instPotentialPhaseEnergyMetric : MetricSpace M := F.metricSpace
      LipschitzWith 1 u)
    (x : F.potentialLegendreDomain old u) {y : M} (hxy : x.val ≠ y)
    (hsat : let _instPotentialPhaseEnergySatMetric : MetricSpace M := F.metricSpace
      u y - u x.val = dist x.val y) :
    F.chartEnergy old (hF.potentialLegendrePhase old u x).val = (1 / 2 : ℝ) := by
  obtain ⟨v, hv, hp, hE⟩ :=
    hF.exists_chart_unit_legendre_of_calibrated_endpoints hcomplete old x.property.1
      hu hxy hsat (hF.mdifferentiableAt_of_mem_potentialLegendreDomain old u x.property)
  have hz : (hF.potentialLegendrePhase old u x).val =
      (extChartAt 𝓘(ℝ, E) old x.val, v) := by
    apply hF.injOn_parametricLegendre_chartEnergy old
      (hF.potentialLegendrePhase old u x).property hv
    exact Prod.ext (hF.potentialLegendrePhase_components old u x).1
      ((hF.potentialLegendrePhase_components old u x).2.1.trans hp.symm)
  rw [hz]
  exact hE

end IsSmoothStronglyConvex
end OTSelector.Geometry.ContinuousFinslerNorm

end
end
