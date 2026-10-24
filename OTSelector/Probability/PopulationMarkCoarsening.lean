import OTSelector.Probability.RNSubplanTypeRefinement
import OTSelector.Probability.RadonNikodymMarkCoarsening
import OTSelector.Probability.SubcouplingTypeMarking

/-!
Conditions: A finite family of actual typed subcouplings, their original source/target marked laws and a deterministic coarsening of the type labels.

Objects: Coarsened original marked laws and iid arrays with exactly the grouped old mark distributions, including grouping back after RN subplan splitting.

Proof detail: Pushforward commutes with the finite component sums; map each retained/unused Option label through the coarsening and apply coordinatewise product-law transport.

References: Günter Last and Mathew Penrose: Section 5.2, Definition 5.3 and equations (5.5)–(5.6), pp. 40–41; Rick Durrett: Section 2.1.2, Theorems 2.1.11–2.1.12, p. 48.
Relation: A finite-label pushforward/grouping adapter for existing RN marked mixtures. It does not replace the physical sample or condition away the unused type.
-/

/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Reconstruction.FinslerRelativeLawOriginalPopulationMarkCoarsening.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Reconstruction.FinslerRelativeLawOriginalPopulationMarkCoarsening`; the selected original proof blocks follow. -/
section

/-! Exact old population marks are finite observations of one refined marked sample. -/
open Set Function MeasureTheory
open scoped BigOperators Classical
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

/-- Grouping finite pairing components commutes with every measurable physical observation. -/
theorem groupedMarkComponent_map {X Z T U : Type*} [MeasurableSpace X]
    [MeasurableSpace Z] [Fintype T] (m : T → Measure X) (coarsen : T → U)
    (f : X → Z) (hf : Measurable f) (u : U) :
    groupedMarkComponent (fun t ↦ (m t).map f) coarsen u =
      (groupedMarkComponent m coarsen u).map f := by
  rw [groupedMarkComponent, groupedMarkComponent, Measure.map_finset_sum hf.aemeasurable]

namespace PopulationSubcouplingTypes
variable {X Y T U : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    [Fintype T] [Fintype U] {π : Measure (X × Y)} [IsFiniteMeasure π]

/-- The coarse types are literally the finite fibers of the original fine pairing types. -/
def coarsen (D : PopulationSubcouplingTypes π T) (read : T → U) :
    PopulationSubcouplingTypes π U where
  component := groupedMarkComponent D.component read
  dominated := by rw [sum_groupedMarkComponent]; exact D.dominated

variable [MeasurableSpace (Option T)] [MeasurableSingletonClass (Option T)]
    [MeasurableSpace (Option U)] [MeasurableSingletonClass (Option U)]
    (D : PopulationSubcouplingTypes π T) (E : PopulationSubcouplingTypes π U)
    (read : T → U) (hcomponents : ∀ u, groupedMarkComponent D.component read u = E.component u)
    (μ : Measure X) (ν : Measure Y) [IsFiniteMeasure μ] [IsFiniteMeasure ν]

include hcomponents

/-- Both physical/old-type marginals are obtained by forgetting only the extra fine marks. -/
theorem marked_laws_map_coarsen :
    (D.sourceMarkedLaw μ).map (fun p ↦ (p.1, p.2.map read)) = E.sourceMarkedLaw μ ∧
    (D.targetMarkedLaw ν).map (fun p ↦ (p.1, p.2.map read)) = E.targetMarkedLaw ν := by
  constructor
  · apply finiteRNMarkLaw_map_coarsen_of_components
    intro u
    change groupedMarkComponent (fun t ↦ (D.component t).map Prod.fst) read u = _
    rw [groupedMarkComponent_map _ _ _ measurable_fst, hcomponents u]
    rfl
  · apply finiteRNMarkLaw_map_coarsen_of_components
    intro u
    change groupedMarkComponent (fun t ↦ (D.component t).map Prod.snd) read u = _
    rw [groupedMarkComponent_map _ _ _ measurable_snd, hcomponents u]
    rfl

/-- One two-color iid fine experiment projects to the exact original coarse marked experiment. -/
theorem iid_marked_law_map_coarsen {I J : Type*} [Fintype I] [Fintype J] :
    ((Measure.pi (fun _ : I ↦ D.sourceMarkedLaw μ)).prod
      (Measure.pi (fun _ : J ↦ D.targetMarkedLaw ν))).map
        (Prod.map (fun sample i ↦ ((sample i).1, (sample i).2.map read))
          (fun sample j ↦ ((sample j).1, (sample j).2.map read))) =
      (Measure.pi (fun _ : I ↦ E.sourceMarkedLaw μ)).prod
        (Measure.pi (fun _ : J ↦ E.targetMarkedLaw ν)) := by
  have hs : Measurable (fun p : X × Option T ↦ (p.1, p.2.map read)) :=
    measurable_fst.prodMk ((measurable_of_countable (Option.map read)).comp measurable_snd)
  have ht : Measurable (fun p : Y × Option T ↦ (p.1, p.2.map read)) :=
    measurable_fst.prodMk ((measurable_of_countable (Option.map read)).comp measurable_snd)
  have hxs : Measurable (fun sample : I → X × Option T ↦
      fun i ↦ ((sample i).1, (sample i).2.map read)) :=
    measurable_pi_lambda _ (fun i ↦ hs.comp (measurable_pi_apply i))
  have hys : Measurable (fun sample : J → Y × Option T ↦
      fun j ↦ ((sample j).1, (sample j).2.map read)) :=
    measurable_pi_lambda _ (fun j ↦ ht.comp (measurable_pi_apply j))
  rw [← Measure.map_prod_map _ _ hxs hys,
    Measure.pi_map_pi (fun _ ↦ hs.aemeasurable),
    Measure.pi_map_pi (fun _ ↦ ht.aemeasurable)]
  simp_rw [(D.marked_laws_map_coarsen E read hcomponents μ ν).1,
    (D.marked_laws_map_coarsen E read hcomponents μ ν).2]

omit hcomponents in
/-- Every original RN subplan split reconstructs each old pairing type separately. -/
theorem rnSubplanTypes_grouped_old {V : Type*} [Fintype V]
    (A : PopulationSubcouplingTypes π V) (η : Measure (X × Y)) (hη : η ≤ π) (t : V) :
    groupedMarkComponent (A.rnSubplanTypes η hη).component Prod.snd t = A.component t := by
  classical
  let _ := A.rnSubplanComponent_isFinite η hη t
  simp only [groupedMarkComponent, Finset.sum_filter, Fintype.sum_prod_type,
    Fintype.sum_bool, rnSubplanTypes, rnSplitComponent]
  simp only [Bool.false_eq_true, ↓reduceIte]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
  rw [add_comm, Measure.sub_add_cancel_of_le (A.rnSubplanComponent_le η hη t)]

end PopulationSubcouplingTypes
end OTSelector.Reconstruction

end
end
