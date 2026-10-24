import OTSelector.Probability.CellRefinedMarkComponents
import OTSelector.Probability.PopulationMarkCoarsening
import OTSelector.Probability.RNSubplanTypeRefinement
import OTSelector.Probability.RadonNikodymMarkCoarsening
import OTSelector.Probability.SubcouplingTypeMarking

/-!
Conditions: An actual typed population subcoupling, a dominated retained subplan and a finite good/bad cell decomposition with its exact split identities.

Objects: Refined typed components dominated by their old types and exact iid laws recovering either the old marks or the retained-subplan marks after coarsening.

Proof detail: Split the genuine subplan into cell components, group the finite refined labels back into their original type/subplan labels and invoke the original mark-coarsening identities.

References: Günter Last and Mathew Penrose: Section 5.2, Definition 5.3 and equations (5.5)–(5.6), pp. 40–41; D. H. Fremlin: Sections 232E–232I, Radon–Nikodym and Lebesgue decomposition; Section 235K, change of measure.
Relation: A local refinement of the original finite mixture. Lost compact/cell mass stays in the represented bad/unused types rather than altering the original marked law.
-/

/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Reconstruction.FinslerRelativeLawOriginalCellRefinedPopulation.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Reconstruction.FinslerRelativeLawOriginalCellRefinedPopulation`; the selected original proof blocks follow. -/
section

/-! Cellwise compact losses refine the original types without changing their marked sample law. -/
open Set Function MeasureTheory
open scoped BigOperators Classical
noncomputable section
namespace OTSelector.Reconstruction.PopulationSubcouplingTypes
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

variable {X Y C T : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    [Fintype C] [Fintype T] {π : Measure (X × Y)} [IsFiniteMeasure π]
    (D : PopulationSubcouplingTypes π T) (η : Measure (X × Y)) (hη : η ≤ π)
    (good : T → Measure (X × Y)) (bad : C → T → Measure (X × Y))
    (hsplit : ∀ t, good t + ∑ c, bad c t = (D.rnSubplanTypes η hη).component (false, t))

include hsplit in
/-- Original residual plus good and bad retained pieces reconstruct each old type. -/
theorem rnCellRefinedComponent_grouped_old (t : T) :
    groupedMarkComponent
      (cellRefinedComponent (fun t ↦ (D.rnSubplanTypes η hη).component (true, t)) good bad)
      cellRefinedOldType t = D.component t := by
  rw [cellRefinedComponent_grouped_old, add_assoc, hsplit]
  let _ := D.rnSubplanComponent_isFinite η hη t
  change D.rnSubplanComponent η t + (D.component t - D.rnSubplanComponent η t) = _
  rw [add_comm, Measure.sub_add_cancel_of_le (D.rnSubplanComponent_le η hη t)]

/-- The fine family is built from the same original RN type shares. Good types
keep only T; only the small bad shares carry the finite cell index. -/
def rnCellRefinedTypes : PopulationSubcouplingTypes π (CellRefinedType C T) where
  component := cellRefinedComponent
    (fun t ↦ (D.rnSubplanTypes η hη).component (true, t)) good bad
  dominated := by
    rw [← sum_groupedMarkComponent _ (cellRefinedOldType (C := C) (T := T))]
    simp_rw [D.rnCellRefinedComponent_grouped_old η hη good bad hsplit]
    exact D.dominated

/-- Coarsening the fine family recovers the original RN retained/residual type,
including the original type name inside both flags. -/
theorem rnCellRefinedTypes_grouped_subplan (t : Bool × T) :
    groupedMarkComponent (D.rnCellRefinedTypes η hη good bad hsplit).component
      cellRefinedSubplanType t = (D.rnSubplanTypes η hη).component t := by
  change groupedMarkComponent
    (cellRefinedComponent (fun t ↦ (D.rnSubplanTypes η hη).component (true, t)) good bad)
    cellRefinedSubplanType t = _
  rcases t with ⟨b, t⟩
  cases b
  · exact (cellRefinedComponent_grouped_retained
      (fun t ↦ (D.rnSubplanTypes η hη).component (true, t)) good bad t).trans (hsplit t)
  · exact cellRefinedComponent_grouped_residual
      (fun t ↦ (D.rnSubplanTypes η hη).component (true, t)) good bad t

/-- Every fine type inherits all original type properties by domination. -/
theorem rnCellRefinedTypes_component_le_old (t : CellRefinedType C T) :
    (D.rnCellRefinedTypes η hη good bad hsplit).component t ≤
      D.component (cellRefinedOldType t) := by
  classical
  calc
    _ ≤ ∑ s ∈ Finset.univ.filter (fun s ↦ cellRefinedOldType s = cellRefinedOldType t),
        (D.rnCellRefinedTypes η hη good bad hsplit).component s :=
      Finset.single_le_sum (fun _ _ ↦ Measure.zero_le _)
        (Finset.mem_filter.mpr ⟨Finset.mem_univ t, rfl⟩)
    _ = _ := D.rnCellRefinedComponent_grouped_old η hη good bad hsplit _

variable [MeasurableSpace (Option T)] [MeasurableSingletonClass (Option T)]
    [MeasurableSpace (Option (Bool × T))] [MeasurableSingletonClass (Option (Bool × T))]
    [MeasurableSpace (Option (CellRefinedType C T))]
    [MeasurableSingletonClass (Option (CellRefinedType C T))]
    (μ : Measure X) (ν : Measure Y) [IsFiniteMeasure μ] [IsFiniteMeasure ν]

include hsplit in
/-- The fine sample coarsens to the original atlas experiment on the same physical indices. -/
theorem rnCellRefinedTypes_iid_old_law {I J : Type*} [Fintype I] [Fintype J] :
    let R := D.rnCellRefinedTypes η hη good bad hsplit
    ((Measure.pi (fun _ : I ↦ R.sourceMarkedLaw μ)).prod
      (Measure.pi (fun _ : J ↦ R.targetMarkedLaw ν))).map
        (Prod.map (fun sample i ↦ ((sample i).1, (sample i).2.map cellRefinedOldType))
          (fun sample j ↦ ((sample j).1, (sample j).2.map cellRefinedOldType))) =
      (Measure.pi (fun _ : I ↦ D.sourceMarkedLaw μ)).prod
        (Measure.pi (fun _ : J ↦ D.targetMarkedLaw ν)) := by
  apply iid_marked_law_map_coarsen
  exact D.rnCellRefinedComponent_grouped_old η hη good bad hsplit

include hsplit in
/-- The same fine sample coarsens to the original retained/residual experiment.
All exact original flag, raw-coordinate and class-prefix laws therefore apply by mapping. -/
theorem rnCellRefinedTypes_iid_subplan_law {I J : Type*} [Fintype I] [Fintype J] :
    let R := D.rnCellRefinedTypes η hη good bad hsplit
    let A := D.rnSubplanTypes η hη
    ((Measure.pi (fun _ : I ↦ R.sourceMarkedLaw μ)).prod
      (Measure.pi (fun _ : J ↦ R.targetMarkedLaw ν))).map
        (Prod.map (fun sample i ↦ ((sample i).1, (sample i).2.map cellRefinedSubplanType))
          (fun sample j ↦ ((sample j).1, (sample j).2.map cellRefinedSubplanType))) =
      (Measure.pi (fun _ : I ↦ A.sourceMarkedLaw μ)).prod
        (Measure.pi (fun _ : J ↦ A.targetMarkedLaw ν)) := by
  apply iid_marked_law_map_coarsen
  exact D.rnCellRefinedTypes_grouped_subplan η hη good bad hsplit

end OTSelector.Reconstruction.PopulationSubcouplingTypes

end
end
