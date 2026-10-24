import OTSelector.Probability.TypedPopulationSampling

/-!
# Full original population retention in finite RN-marked samples

An exact finite decomposition of the original coupling gives zero residual
population and ensures every actual marked sample carries a retained type.
-/

open Set Function MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators Classical

noncomputable section
namespace OTSelector.Reconstruction.PopulationSubcouplingTypes
set_option backward.isDefEq.respectTransparency false

variable {X Y T : Type*} [MeasurableSpace X] [MeasurableSpace Y] [Fintype T]
  [MeasurableSpace (Option T)] [MeasurableSingletonClass (Option T)]
  {π : Measure (X × Y)} [IsFiniteMeasure π]
  (D : PopulationSubcouplingTypes π T)
  {μ : Measure X} {ν : Measure Y} [IsFiniteMeasure μ] [IsFiniteMeasure ν]

omit [MeasurableSpace (Option T)] [MeasurableSingletonClass (Option T)]
  [IsFiniteMeasure π] in
/-- Exact decomposition of the original coupling leaves no residual population. -/
theorem completed_none_eq_zero (hfull : ∑ t, D.component t = π) :
    D.completed none = 0 := by
  simp only [completed, finiteRNMarkComponent, hfull, Measure.sub_self]

omit [IsFiniteMeasure μ] [IsFiniteMeasure ν] in
/-- Every point in the original marked experiment has a retained type when the
actual type restrictions cover the original coupling completely. -/
theorem marked_ae_some_of_sum_eq (hπ : Vlasov.IsCoupling π μ ν)
    (hfull : ∑ t, D.component t = π) :
    (∀ᵐ x ∂D.sourceMarkedLaw μ, ∃ t, x.2 = some t) ∧
      (∀ᵐ y ∂D.targetMarkedLaw ν, ∃ t, y.2 = some t) := by
  have hz := D.completed_none_eq_zero hfull
  have hm := D.completed_marginals hπ none
  have hs : finiteRNMarkComponent μ D.source none = 0 := by
    rw [← hm.1, hz, Measure.map_zero]
  have ht : finiteRNMarkComponent ν D.target none = 0 := by
    rw [← hm.2, hz, Measure.map_zero]
  constructor
  · apply finiteRNMarkLaw_ae_of_components μ D.source
    intro tag
    cases tag with
    | none => simp only [hs, ae_zero, Filter.eventually_bot]
    | some t => exact Filter.Eventually.of_forall (fun _ ↦ ⟨t, rfl⟩)
  · apply finiteRNMarkLaw_ae_of_components ν D.target
    intro tag
    cases tag with
    | none => simp only [ht, ae_zero, Filter.eventually_bot]
    | some t => exact Filter.Eventually.of_forall (fun _ ↦ ⟨t, rfl⟩)

/-- A finite original sample contains no residual type after exact full-population
chart-bin decomposition; counts in different colors remain unrestricted. -/
theorem iid_marked_ae_some_of_sum_eq {I J : Type*} [Fintype I] [Fintype J]
    (hπ : Vlasov.IsCoupling π μ ν) (hfull : ∑ t, D.component t = π) :
    ∀ᵐ ω ∂(Measure.pi (fun _ : I ↦ D.sourceMarkedLaw μ)).prod
        (Measure.pi (fun _ : J ↦ D.targetMarkedLaw ν)),
      (∀ i, ∃ t, (ω.1 i).2 = some t) ∧ (∀ j, ∃ t, (ω.2 j).2 = some t) := by
  obtain ⟨hs, ht⟩ := D.marked_ae_some_of_sum_eq hπ hfull
  have hxs : ∀ᵐ x ∂Measure.pi (fun _ : I ↦ D.sourceMarkedLaw μ),
      ∀ i, ∃ t, (x i).2 = some t :=
    ae_all_iff.mpr fun i ↦ (Measure.quasiMeasurePreserving_eval
      (fun _ : I ↦ D.sourceMarkedLaw μ) i).ae hs
  have hys : ∀ᵐ y ∂Measure.pi (fun _ : J ↦ D.targetMarkedLaw ν),
      ∀ j, ∃ t, (y j).2 = some t :=
    ae_all_iff.mpr fun j ↦ (Measure.quasiMeasurePreserving_eval
      (fun _ : J ↦ D.targetMarkedLaw ν) j).ae ht
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae hxs,
    Measure.quasiMeasurePreserving_snd.ae hys] with ω hωs hωt
  exact ⟨hωs, hωt⟩

end OTSelector.Reconstruction.PopulationSubcouplingTypes
