import OTSelector.Probability.RadonNikodymMarking
import OTSelector.Probability.SubcouplingTypeMarking

/-!
Conditions: Actual finite RN-type marked populations and a.e. properties of each original component; finite iid arrays, with a coupling premise only for recovery of the full physical-law property.

Objects: One original marked-array a.e. event on which every sampled type has its true component property and positive component mass, and all original physical-array full-measure properties persist.

Proof detail: Transfer a.e. component properties through the finite marked mixture and then through each coordinate of the actual finite product. Forgetting the marks uses the already proved exact original iid marginal law.

References: Günter Last and Mathew Penrose: Section 5.2, Definition 5.3 and equations (5.5)–(5.6), pp. 40–41; Rick Durrett: Section 2.1.2, Theorems 2.1.11–2.1.12, p. 48.
Relation: A finite a.e.-transport argument permitting nonmeasurable predicates and later sample-dependent matching choices. It does not require a measurable selection of those matchings.
-/

/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Reconstruction.FinslerPopulationTypedSampling.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Reconstruction.FinslerPopulationTypedSampling`; the selected original proof blocks follow. -/
section

/-!
# Original type properties on the marked iid sample

Properties holding almost everywhere on an original type subpopulation hold on
every sample carrying that type. The finite arrays share one full-measure event,
so any subsequent sample-dependent matching may use these properties pointwise.
No measurability of the selected matching or of the property is needed here.
-/

open Set Function MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators Classical

noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false

/-- Every property holding on the original component of each mark holds under
the complete marked original law, including its residual component. -/
theorem finiteRNMarkLaw_ae_of_components
    {X T : Type*} [MeasurableSpace X] [Fintype T]
    [MeasurableSpace (Option T)] [MeasurableSingletonClass (Option T)]
    (μ : Measure X) (m : T → Measure X) (P : X × Option T → Prop)
    (hP : ∀ tag, ∀ᵐ x ∂finiteRNMarkComponent μ m tag, P (x, tag)) :
    ∀ᵐ p ∂finiteRNMarkLaw μ m, P p := by
  rw [finiteRNMarkLaw, ae_add_measure_iff]
  constructor
  · exact (measurableEmbedding_prod_mk_right (none : Option T)).ae_map_iff.mpr (hP none)
  · rw [← Measure.sum_fintype, Measure.ae_sum_iff]
    intro t
    exact (measurableEmbedding_prod_mk_right (some t)).ae_map_iff.mpr (hP (some t))

/-- Every retained original component property holds whenever that type is
selected by the RN mark. -/
theorem finiteRNMarkLaw_ae_type_property
    {X T : Type*} [MeasurableSpace X] [Fintype T]
    [MeasurableSpace (Option T)] [MeasurableSingletonClass (Option T)]
    (μ : Measure X) (m : T → Measure X) (Good : T → X → Prop)
    (hgood : ∀ t, ∀ᵐ x ∂m t, Good t x) :
    ∀ᵐ p ∂finiteRNMarkLaw μ m, ∀ t, p.2 = some t → Good t p.1 := by
  apply finiteRNMarkLaw_ae_of_components μ m
  intro tag
  cases tag with
  | none => exact Filter.Eventually.of_forall (fun _ _ h ↦ by cases h)
  | some t =>
    filter_upwards [hgood t] with x hx
    intro t' ht'
    cases Option.some.inj ht'
    exact hx

namespace PopulationSubcouplingTypes
variable {X Y T : Type*} [MeasurableSpace X] [MeasurableSpace Y] [Fintype T]
  [MeasurableSpace (Option T)] [MeasurableSingletonClass (Option T)]
  {π : Measure (X × Y)} [IsFiniteMeasure π]
  (D : PopulationSubcouplingTypes π T)
  {μ : Measure X} {ν : Measure Y} [IsFiniteMeasure μ] [IsFiniteMeasure ν]

/-- Both finite physical arrays retain all actual properties of their original
type subpopulations on one common full-measure event. -/
theorem iid_marked_type_properties {I J : Type*} [Fintype I] [Fintype J]
    (GoodSource : T → X → Prop) (GoodTarget : T → Y → Prop)
    (hsource : ∀ t, ∀ᵐ x ∂D.source t, GoodSource t x)
    (htarget : ∀ t, ∀ᵐ y ∂D.target t, GoodTarget t y) :
    ∀ᵐ ω ∂(Measure.pi (fun _ : I ↦ D.sourceMarkedLaw μ)).prod
        (Measure.pi (fun _ : J ↦ D.targetMarkedLaw ν)),
      (∀ i t, (ω.1 i).2 = some t → GoodSource t (ω.1 i).1) ∧
        (∀ j t, (ω.2 j).2 = some t → GoodTarget t (ω.2 j).1) := by
  have hs : ∀ᵐ x ∂Measure.pi (fun _ : I ↦ D.sourceMarkedLaw μ),
      ∀ i t, (x i).2 = some t → GoodSource t (x i).1 :=
    ae_all_iff.mpr fun i ↦ (Measure.quasiMeasurePreserving_eval (fun _ : I ↦ D.sourceMarkedLaw μ) i).ae
      (finiteRNMarkLaw_ae_type_property μ D.source GoodSource hsource)
  have ht : ∀ᵐ y ∂Measure.pi (fun _ : J ↦ D.targetMarkedLaw ν),
      ∀ j t, (y j).2 = some t → GoodTarget t (y j).1 :=
    ae_all_iff.mpr fun j ↦ (Measure.quasiMeasurePreserving_eval (fun _ : J ↦ D.targetMarkedLaw ν) j).ae
      (finiteRNMarkLaw_ae_type_property ν D.target GoodTarget htarget)
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae hs,
    Measure.quasiMeasurePreserving_snd.ae ht] with ω hωs hωt
  exact ⟨hωs, hωt⟩

/-- A type actually appearing in either iid array has positive original
subcoupling mass, simultaneously for every sample and retained type. -/
theorem iid_marked_positive_types {I J : Type*} [Fintype I] [Fintype J] :
    ∀ᵐ ω ∂(Measure.pi (fun _ : I ↦ D.sourceMarkedLaw μ)).prod
        (Measure.pi (fun _ : J ↦ D.targetMarkedLaw ν)),
      (∀ i t, (ω.1 i).2 = some t → D.component t univ ≠ 0) ∧
        (∀ j t, (ω.2 j).2 = some t → D.component t univ ≠ 0) := by
  apply D.iid_marked_type_properties (fun t _ ↦ D.component t univ ≠ 0)
    (fun t _ ↦ D.component t univ ≠ 0)
  · intro t
    by_cases ht : D.component t univ = 0
    · have hz : D.component t = 0 := Measure.measure_univ_eq_zero.mp ht
      simp only [source, hz, Measure.map_zero, ae_zero, Filter.eventually_bot]
    · exact Filter.Eventually.of_forall (fun _ ↦ ht)
  · intro t
    by_cases ht : D.component t univ = 0
    · have hz : D.component t = 0 := Measure.measure_univ_eq_zero.mp ht
      simp only [target, hz, Measure.map_zero, ae_zero, Filter.eventually_bot]
    · exact Filter.Eventually.of_forall (fun _ ↦ ht)

omit [MeasurableSingletonClass (Option T)] in
/-- A property of the unchanged original physical iid sample also holds on the
marked extension; the subsequent allocation of type marks does not alter it. -/
theorem iid_original_physical_property {I J : Type*} [Fintype I] [Fintype J]
    (hπ : Vlasov.IsCoupling π μ ν) (Good : (I → X) × (J → Y) → Prop)
    (hgood : ∀ᵐ ω ∂(Measure.pi (fun _ : I ↦ μ)).prod (Measure.pi (fun _ : J ↦ ν)), Good ω) :
    ∀ᵐ ω ∂(Measure.pi (fun _ : I ↦ D.sourceMarkedLaw μ)).prod
        (Measure.pi (fun _ : J ↦ D.targetMarkedLaw ν)),
      Good ((fun i ↦ (ω.1 i).1), (fun j ↦ (ω.2 j).1)) := by
  apply ae_of_ae_map (show Measurable (Prod.map (fun x : I → X × Option T ↦ fun i ↦ (x i).1)
      (fun y : J → Y × Option T ↦ fun j ↦ (y j).1)) from by fun_prop).aemeasurable
  rwa [D.iid_physical_law hπ]

end PopulationSubcouplingTypes
end OTSelector.Reconstruction

end
end
