import OTSelector.Probability.CellRefinedPopulation
import OTSelector.Probability.PopulationPartialMarks

/-! Good retained types retain the original atlas cardinality on the same fine marked sample. -/
open Set Function MeasureTheory
open scoped BigOperators Classical
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

/-- Observe only good retained old types; discarded and residual marks become none. -/
def cellRefinedGoodType {C T : Type*} : CellRefinedType C T → Option T
  | .inl p => if p.1 then some p.2 else none
  | .inr _ => none

/-- Each observed good mark names precisely its original fine good mark. -/
theorem cellRefinedGoodType_bind_some_iff {C T : Type*}
    (tag : Option (CellRefinedType C T)) (t : T) :
    tag.bind cellRefinedGoodType = some t ↔ tag = some (.inl (true, t)) := by
  cases tag with
  | none => simp
  | some tag =>
    cases tag with
    | inl p => rcases p with ⟨b, s⟩; cases b <;> simp [cellRefinedGoodType]
    | inr p => simp [cellRefinedGoodType]

/-- Exact good-type fibers contain no bad cell index. -/
theorem cellRefinedComponent_grouped_good {X C T : Type*} [MeasurableSpace X]
    [Fintype C] [Fintype T] (residual good : T → Measure X)
    (bad : C → T → Measure X) (t : T) :
    groupedMarkComponent (cellRefinedComponent residual good bad) cellRefinedGoodType
      (some t) = good t := by
  classical
  simp only [groupedMarkComponent, Finset.sum_filter, Fintype.sum_sum_type,
    Fintype.sum_prod_type, Fintype.sum_bool, cellRefinedGoodType, cellRefinedComponent]
  simp

/-- The good selection contains exactly one mark per original atlas type. -/
def cellRefinedGoodTags (C T : Type*) [Fintype T] : Finset (Option (CellRefinedType C T)) :=
  Finset.univ.image (fun t ↦ some (.inl (true, t)))

theorem card_cellRefinedGoodTags (C T : Type*) [Fintype T] :
    (cellRefinedGoodTags C T).card = Fintype.card T := by
  classical
  apply Finset.card_image_of_injective
  intro s t h
  exact (Prod.mk.inj (Sum.inl.inj (Option.some.inj h))).2

namespace PopulationSubcouplingTypes
variable {X Y C T : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    [Fintype C] [Fintype T] {π : Measure (X × Y)} [IsFiniteMeasure π]
    (D : PopulationSubcouplingTypes π T) (η : Measure (X × Y)) (hη : η ≤ π)
    (good : T → Measure (X × Y)) (bad : C → T → Measure (X × Y))
    (hsplit : ∀ t, good t + ∑ c, bad c t = (D.rnSubplanTypes η hη).component (false, t))

/-- The good-only data use T as their type space, while retaining all other original mass as none. -/
def rnCellGoodTypes : PopulationSubcouplingTypes π T :=
  (D.rnCellRefinedTypes η hη good bad hsplit).partialCoarsen cellRefinedGoodType

/-- The good-only original pairing component is the literal prescribed good share. -/
theorem rnCellGoodTypes_component (t : T) :
    (D.rnCellGoodTypes η hη good bad hsplit).component t = good t := by
  exact cellRefinedComponent_grouped_good
    (fun t ↦ (D.rnSubplanTypes η hη).component (true, t)) good bad t

variable [MeasurableSpace (Option T)] [MeasurableSingletonClass (Option T)]
    [MeasurableSpace (Option (CellRefinedType C T))]
    [MeasurableSingletonClass (Option (CellRefinedType C T))]
    {μ : Measure X} {ν : Measure Y} [IsFiniteMeasure μ] [IsFiniteMeasure ν]

/-- The original-T good hierarchy is an observation of the same fine experiment.
None contains the unchanged residual and bad physical samples; no endpoint selection is iid. -/
theorem rnCellRefinedTypes_iid_good_law {I J : Type*} [Fintype I] [Fintype J]
    (hπ : Vlasov.IsCoupling π μ ν) :
    let R := D.rnCellRefinedTypes η hη good bad hsplit
    let G := D.rnCellGoodTypes η hη good bad hsplit
    ((Measure.pi (fun _ : I ↦ R.sourceMarkedLaw μ)).prod
      (Measure.pi (fun _ : J ↦ R.targetMarkedLaw ν))).map
        (Prod.map (fun sample i ↦ ((sample i).1, (sample i).2.bind cellRefinedGoodType))
          (fun sample j ↦ ((sample j).1, (sample j).2.bind cellRefinedGoodType))) =
      (Measure.pi (fun _ : I ↦ G.sourceMarkedLaw μ)).prod
        (Measure.pi (fun _ : J ↦ G.targetMarkedLaw ν)) := by
  apply iid_marked_law_map_partial _ _ _ _ hπ
  intro t
  rfl

end PopulationSubcouplingTypes
end OTSelector.Reconstruction
