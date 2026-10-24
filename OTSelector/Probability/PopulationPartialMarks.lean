import OTSelector.Probability.PartialMarkCoarsening
import OTSelector.Probability.PopulationMarkCoarsening
import OTSelector.Probability.RadonNikodymMarkCoarsening
import OTSelector.Probability.RadonNikodymMarking
import OTSelector.Probability.SubcouplingTypeMarking

/-!
Conditions: A finite original typed subcoupling and a deterministic partial type observation T→Option U.

Objects: An actual partially observed marked mixture whose source/target and iid marked laws are exactly the pushforwards of the original laws.

Proof detail: Group the observed type components and send unobserved components into the original residual none type; expand the finite sums and push each coordinate through Option.bind.

References: Günter Last and Mathew Penrose: Section 5.2, Definition 5.3 and equations (5.5)–(5.6), pp. 40–41; D. H. Fremlin: Sections 232E–232I, Radon–Nikodym and Lebesgue decomposition; Section 235K, change of measure.
Relation: A partial finite-mark observation preserving the same physical sample. Unobserved types are retained as unused mass rather than removed by conditioning.
-/

/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Reconstruction.FinslerRelativeLawOriginalPopulationPartialMarks.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Reconstruction.FinslerRelativeLawOriginalPopulationPartialMarks`; the selected original proof blocks follow. -/
section

/-! Selected type observations of the same two-color original marked experiment. -/
open Set Function MeasureTheory
open scoped BigOperators Classical
noncomputable section
namespace OTSelector.Reconstruction.PopulationSubcouplingTypes
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

variable {X Y T U : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    [Fintype T] [Fintype U] {π : Measure (X × Y)} [IsFiniteMeasure π]

/-- Retain only the specified finite type fibers; all erased mass remains in the original population. -/
def partialCoarsen (D : PopulationSubcouplingTypes π T) (read : T → Option U) :
    PopulationSubcouplingTypes π U where
  component := fun u ↦ groupedMarkComponent D.component read (some u)
  dominated := by
    calc
      _ ≤ groupedMarkComponent D.component read none +
          ∑ u, groupedMarkComponent D.component read (some u) :=
        Measure.le_add_left (le_refl _)
      _ = ∑ u : Option U, groupedMarkComponent D.component read u := by rw [Fintype.sum_option]
      _ = _ := sum_groupedMarkComponent _ _
      _ ≤ _ := D.dominated

variable [MeasurableSpace (Option T)] [MeasurableSingletonClass (Option T)]
    [MeasurableSpace (Option U)] [MeasurableSingletonClass (Option U)]
    (D : PopulationSubcouplingTypes π T) (E : PopulationSubcouplingTypes π U)
    (read : T → Option U)
    (hcomponents : ∀ u, groupedMarkComponent D.component read (some u) = E.component u)
    {μ : Measure X} {ν : Measure Y} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hπ : Vlasov.IsCoupling π μ ν)
include hcomponents hπ

/-- Erasing fine types gives exactly the physical/type marginals of the retained original shares. -/
theorem marked_laws_map_partial :
    (D.sourceMarkedLaw μ).map (fun p ↦ (p.1, p.2.bind read)) = E.sourceMarkedLaw μ ∧
    (D.targetMarkedLaw ν).map (fun p ↦ (p.1, p.2.bind read)) = E.targetMarkedLaw ν := by
  obtain ⟨hs, ht⟩ := D.marginal_domination hπ
  constructor
  · rw [sourceMarkedLaw, finiteRNMarkLaw_map_partial μ D.source hs]
    congr 1
    funext u
    change groupedMarkComponent (fun t ↦ (D.component t).map Prod.fst) read (some u) = _
    rw [groupedMarkComponent_map _ _ _ measurable_fst, hcomponents u]
    rfl
  · rw [targetMarkedLaw, finiteRNMarkLaw_map_partial ν D.target ht]
    congr 1
    funext u
    change groupedMarkComponent (fun t ↦ (D.component t).map Prod.snd) read (some u) = _
    rw [groupedMarkComponent_map _ _ _ measurable_snd, hcomponents u]
    rfl

/-- The selected-type hierarchy runs on a finite observation of the same fine iid sample. -/
theorem iid_marked_law_map_partial {I J : Type*} [Fintype I] [Fintype J] :
    ((Measure.pi (fun _ : I ↦ D.sourceMarkedLaw μ)).prod
      (Measure.pi (fun _ : J ↦ D.targetMarkedLaw ν))).map
        (Prod.map (fun sample i ↦ ((sample i).1, (sample i).2.bind read))
          (fun sample j ↦ ((sample j).1, (sample j).2.bind read))) =
      (Measure.pi (fun _ : I ↦ E.sourceMarkedLaw μ)).prod
        (Measure.pi (fun _ : J ↦ E.targetMarkedLaw ν)) := by
  have hs : Measurable (fun p : X × Option T ↦ (p.1, p.2.bind read)) :=
    measurable_fst.prodMk ((measurable_of_countable (fun t : Option T ↦ t.bind read)).comp measurable_snd)
  have ht : Measurable (fun p : Y × Option T ↦ (p.1, p.2.bind read)) :=
    measurable_fst.prodMk ((measurable_of_countable (fun t : Option T ↦ t.bind read)).comp measurable_snd)
  have hxs : Measurable (fun sample : I → X × Option T ↦
      fun i ↦ ((sample i).1, (sample i).2.bind read)) :=
    measurable_pi_lambda _ (fun i ↦ hs.comp (measurable_pi_apply i))
  have hys : Measurable (fun sample : J → Y × Option T ↦
      fun j ↦ ((sample j).1, (sample j).2.bind read)) :=
    measurable_pi_lambda _ (fun j ↦ ht.comp (measurable_pi_apply j))
  rw [← Measure.map_prod_map _ _ hxs hys,
    Measure.pi_map_pi (fun _ ↦ hs.aemeasurable),
    Measure.pi_map_pi (fun _ ↦ ht.aemeasurable)]
  simp_rw [(D.marked_laws_map_partial E read hcomponents hπ).1,
    (D.marked_laws_map_partial E read hcomponents hπ).2]

end OTSelector.Reconstruction.PopulationSubcouplingTypes

end
end
