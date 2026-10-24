import OTSelector.Probability.CellRefinedPopulation
import OTSelector.Probability.PopulationPartialMarks

/-! Cell-specific discarded components are observed on the same fine original marked sample. -/
open Set Function MeasureTheory
open scoped BigOperators Classical
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

/-- Observe only bad retained shares, preserving their original cell and atlas type. -/
def cellRefinedBadType {C T : Type*} : CellRefinedType C T → Option (C × T)
  | .inl _ => none
  | .inr p => some p

/-- An observed bad mark is precisely the same original fine bad mark. -/
theorem cellRefinedBadType_bind_some_iff {C T : Type*}
    (tag : Option (CellRefinedType C T)) (p : C × T) :
    tag.bind cellRefinedBadType = some p ↔ tag = some (.inr p) := by
  cases tag with
  | none => simp
  | some tag => cases tag <;> simp [cellRefinedBadType]

/-- Each bad-type fiber is the literal original discarded pairing component. -/
theorem cellRefinedComponent_grouped_bad {X C T : Type*} [MeasurableSpace X]
    [Fintype C] [Fintype T] (residual good : T → Measure X)
    (bad : C → T → Measure X) (p : C × T) :
    groupedMarkComponent (cellRefinedComponent residual good bad) cellRefinedBadType
      (some p) = bad p.1 p.2 := by
  classical
  rcases p with ⟨c, t⟩
  simp only [groupedMarkComponent, Finset.sum_filter, Fintype.sum_sum_type,
    Fintype.sum_prod_type, Fintype.sum_bool, cellRefinedBadType, cellRefinedComponent]
  simp [ite_and]

namespace PopulationSubcouplingTypes
variable {X Y C T : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    [Fintype C] [Fintype T] {π : Measure (X × Y)} [IsFiniteMeasure π]
    (D : PopulationSubcouplingTypes π T) (η : Measure (X × Y)) (hη : η ≤ π)
    (good : T → Measure (X × Y)) (bad : C → T → Measure (X × Y))
    (hsplit : ∀ t, good t + ∑ c, bad c t = (D.rnSubplanTypes η hη).component (false, t))

/-- All bad cells share one finite C × T observation; other original points remain none. -/
def rnCellBadTypes : PopulationSubcouplingTypes π (C × T) :=
  (D.rnCellRefinedTypes η hη good bad hsplit).partialCoarsen cellRefinedBadType

theorem rnCellBadTypes_component (p : C × T) :
    (D.rnCellBadTypes η hη good bad hsplit).component p = bad p.1 p.2 :=
  cellRefinedComponent_grouped_bad
    (fun t ↦ (D.rnSubplanTypes η hη).component (true, t)) good bad p

/-- Every bad pairing share retains its old atlas type properties. -/
theorem rnCellBadTypes_component_le_old (p : C × T) :
    (D.rnCellBadTypes η hη good bad hsplit).component p ≤ D.component p.2 := by
  rw [rnCellBadTypes_component]
  exact D.rnCellRefinedTypes_component_le_old η hη good bad hsplit (.inr p)

variable [MeasurableSpace (Option (C × T))] [MeasurableSingletonClass (Option (C × T))]
    [MeasurableSpace (Option (CellRefinedType C T))]
    [MeasurableSingletonClass (Option (CellRefinedType C T))]
    {μ : Measure X} {ν : Measure Y} [IsFiniteMeasure μ] [IsFiniteMeasure ν]

/-- Bad small-mass energy estimates use an exact observation of the same fine iid arrays. -/
theorem rnCellRefinedTypes_iid_bad_law {I J : Type*} [Fintype I] [Fintype J]
    (hπ : Vlasov.IsCoupling π μ ν) :
    let R := D.rnCellRefinedTypes η hη good bad hsplit
    let B := D.rnCellBadTypes η hη good bad hsplit
    ((Measure.pi (fun _ : I ↦ R.sourceMarkedLaw μ)).prod
      (Measure.pi (fun _ : J ↦ R.targetMarkedLaw ν))).map
        (Prod.map (fun sample i ↦ ((sample i).1, (sample i).2.bind cellRefinedBadType))
          (fun sample j ↦ ((sample j).1, (sample j).2.bind cellRefinedBadType))) =
      (Measure.pi (fun _ : I ↦ B.sourceMarkedLaw μ)).prod
        (Measure.pi (fun _ : J ↦ B.targetMarkedLaw ν)) := by
  apply iid_marked_law_map_partial _ _ _ _ hπ
  intro p
  rfl

end PopulationSubcouplingTypes
end OTSelector.Reconstruction
