import OTSelector.Transport.EmpiricalSelector.CompactSupport
import OTSelector.Limit.SupportedEmpiricalSelector

/-! A population coupling is determined by all continuous readouts on a common compact carrier. -/
open Set MeasureTheory
open scoped BoundedContinuousFunction
noncomputable section
namespace OTSelector.Reconstruction
set_option linter.style.haveILetI false

/-- Equal compact-carrier readouts determine the original ambient coupling.
No sampling model, optimal potential or pressure representation enters this statement. -/
theorem populationCoupling_eq_of_compact_readouts
    {M : Type*} [MetricSpace M] [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M]
    (μ ν : ProbabilityMeasure M) (K : Set M) (hK : IsCompact K)
    (hμ : ∀ᵐ x ∂(μ : Measure M), x ∈ K) (hν : ∀ᵐ y ∂(ν : Measure M), y ∈ K)
    {π₁ π₂ : ProbabilityMeasure (M × M)}
    (hπ₁ : Vlasov.IsCoupling (π₁ : Measure (M × M)) (μ : Measure M) (ν : Measure M))
    (hπ₂ : Vlasov.IsCoupling (π₂ : Measure (M × M)) (μ : Measure M) (ν : Measure M))
    (hreadout : ∀ f : (K × K) →ᵇ ℝ,
      ∫ z, f z ∂((π₁ : Measure (M × M)).comap
        (Prod.map ((↑) : K → M) ((↑) : K → M))) =
      ∫ z, f z ∂((π₂ : Measure (M × M)).comap
        (Prod.map ((↑) : K → M) ((↑) : K → M)))) : π₁ = π₂ := by
  let incl := Prod.map ((↑) : K → M) ((↑) : K → M)
  have recover (π : ProbabilityMeasure (M × M))
      (hπ : Vlasov.IsCoupling (π : Measure (M × M)) (μ : Measure M) (ν : Measure M)) :
      ((π : Measure (M × M)).comap incl).map incl = π := by
    have hcoupling : Vlasov.IsCoupling (π : Measure (M × M))
        (((μ : Measure M).comap ((↑) : K → M)).map ((↑) : K → M))
        (((ν : Measure M).comap ((↑) : K → M)).map ((↑) : K → M)) := by
      simpa only [map_comap_subtype_of_ae_mem hK.measurableSet hμ,
        map_comap_subtype_of_ae_mem hK.measurableSet hν] using hπ
    exact map_comap_of_isCoupling (MeasurableEmbedding.subtype_coe hK.measurableSet)
      (MeasurableEmbedding.subtype_coe hK.measurableSet) hcoupling
  have hrec₁ := recover π₁ hπ₁
  have hrec₂ := recover π₂ hπ₂
  haveI : IsProbabilityMeasure (((π₁ : Measure (M × M)).comap incl).map incl) := by
    rw [hrec₁]
    infer_instance
  haveI : IsProbabilityMeasure (((π₂ : Measure (M × M)).comap incl).map incl) := by
    rw [hrec₂]
    infer_instance
  haveI : IsProbabilityMeasure ((π₁ : Measure (M × M)).comap incl) :=
    Measure.isProbabilityMeasure_of_map incl
  haveI : IsProbabilityMeasure ((π₂ : Measure (M × M)).comap incl) :=
    Measure.isProbabilityMeasure_of_map incl
  have heq : (π₁ : Measure (M × M)).comap incl =
      (π₂ : Measure (M × M)).comap incl := by
    apply MeasureTheory.ext_of_forall_integral_eq_of_IsFiniteMeasure
    exact hreadout
  apply ProbabilityMeasure.toMeasure_injective
  rw [← hrec₁, ← hrec₂, heq]

end OTSelector.Reconstruction
