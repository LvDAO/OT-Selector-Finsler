import OTSelector.Geometry.Finsler.Basic
import OTSelector.Geometry.Finsler.Energy.Basic
import OTSelector.Geometry.Finsler.Energy.Chart
import OTSelector.Geometry.Finsler.FlowLocalC2
import OTSelector.Geometry.Finsler.Geodesic.Defs
import OTSelector.Geometry.Finsler.LengthMetric
import OTSelector.Geometry.Finsler.MeasurableLegendre

/-!
# Geometry.Finsler.MeasurableGeodesic

* **Conditions:** The actual complete Finsler flow, and the actual slit or covector-range subtype initial domain.
* **Objects:** A continuous/jointly Borel complete original geodesic family and a measurable covector-indexed counterpart.
* **Proof detail:** Use constructed smooth flow dependence for position continuity, then compose with the Borel inverse Legendre equivalence.

Mathematical sources:
- [Gerald Teschl, Ordinary Differential Equations and Dynamical Systems (AMS 2012 author preliminary version)](https://www.mat.univie.ac.at/~gerald/ftp/book-ode/ode.pdf#page=56): Section 2.4, pp. 45–47, equations (2.46)–(2.50), Theorem 2.10.
- [D. H. Fremlin, Measure Theory, Volume 4, Appendix](https://www1.essex.ac.uk/maths/people/fremlin/chap4a.pdf#page=32): Sections 4A3B(a)–(c), p. 32; 4A3C(a)–(f), pp. 32–33.
- [D. H. Fremlin, Measure Theory, Volume 4](https://www1.essex.ac.uk/maths/people/fremlin/chap42.pdf#page=22): Theorem 423I(a)–(b), pp. 22–23; Proposition 424G, p. 31.

Source relation (derived): Derived from the cited geometric/analytic principles with the exact actual source hypotheses. The local construction and its original phase/covector data are retained, rather than asserted as a verbatim source statement.
-/

/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Geometry.FinslerMeasurableGeodesic.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Geometry.FinslerMeasurableGeodesic`; the selected original proof blocks follow. -/
section

/-!
# Jointly measurable complete geodesics of the original Finsler metric

The complete original flow supplies a continuous position family on the actual slit
initial-state domain and all real times. Its Borel measurability follows from that
constructed continuity; neither a measurable choice of curves nor a flow oracle is assumed.
-/

open Set Filter Metric MeasureTheory Manifold Bundle
open scoped Topology ContDiff

noncomputable section
namespace OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  {F : ContinuousFinslerNorm E M}

/-- The original complete metric constructs one continuous and jointly measurable
complete geodesic family on every actual slit initial chart-state domain. -/
theorem exists_complete_measurable_geodesic_family (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace) (old : M) :
    ∃ G : chartEnergyDomain (E := E) old → ℝ → M,
      (∀ z, F.IsEulerLagrangeOn (G z) univ) ∧
      (∀ z, tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (G z) ⟨0, (1 : ℝ)⟩ =
        (extChartAt (𝓘(ℝ, E).prod 𝓘(ℝ, E))
          (⟨old, 0⟩ : TangentBundle 𝓘(ℝ, E) M)).symm z) ∧
      Continuous (Function.uncurry G) ∧ Measurable (Function.uncurry G) := by
  obtain ⟨Γ, hEL, hinit, hΓ⟩ := hF.exists_complete_tangentFamily_C2 hcomplete old 0
  have hcont : ContinuousOn (fun q : (E × E) × ℝ ↦ Γ q.1 q.2)
      (chartEnergyDomain old ×ˢ univ) := by
    intro q hq
    exact ((Bundle.contMDiffWithinAt_totalSpace.mp (hΓ q hq)).1).continuousWithinAt
  have hrestr : Continuous (fun q : chartEnergyDomain (E := E) old × ℝ ↦
      Γ q.1 q.2) := by
    exact hcont.comp_continuous
      ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)
      (fun q ↦ ⟨q.1.property, mem_univ _⟩)
  exact ⟨fun z ↦ Γ z, fun z ↦ hEL z z.property,
    fun z ↦ hinit z z.property, hrestr, hrestr.measurable⟩

/-- The actual measurable Legendre inverse and original complete flow construct a
jointly measurable family indexed by the whole actual chart momentum range. -/
theorem exists_complete_measurable_covector_family (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace) (old : M) :
    ∃ H : F.chartLegendreRange old → ℝ → M,
      (∀ p, F.IsEulerLagrangeOn (H p) univ) ∧
      (∀ p, tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (H p) ⟨0, (1 : ℝ)⟩ =
        (extChartAt (𝓘(ℝ, E).prod 𝓘(ℝ, E))
          (⟨old, 0⟩ : TangentBundle 𝓘(ℝ, E) M)).symm
            ((hF.chartLegendreEquivRange old).symm p)) ∧
      Measurable (Function.uncurry H) := by
  obtain ⟨G, hEL, hi, _, hm⟩ :=
    hF.exists_complete_measurable_geodesic_family hcomplete old
  refine ⟨fun p ↦ G ((hF.chartLegendreEquivRange old).symm p),
    fun p ↦ hEL _, fun p ↦ hi _, ?_⟩
  exact hm.comp (((hF.chartLegendreEquivRange old).symm.measurable.comp measurable_fst).prodMk
    measurable_snd)

end OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

end
end
