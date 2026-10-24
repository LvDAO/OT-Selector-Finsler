import OTSelector.Probability.CellRefinedPopulation
import OTSelector.Reconstruction.FinslerPopulationTypedCostData

/-! Exact old-type reconstruction removes the unmarked case from the same fine experiment. -/
open Set Function MeasureTheory
open scoped BigOperators Classical
noncomputable section
namespace OTSelector.Reconstruction.PopulationSubcouplingTypes
set_option backward.isDefEq.respectTransparency false

variable {X Y C T : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    [Fintype C] [Fintype T] {π : Measure (X × Y)} [IsFiniteMeasure π]
    (D : PopulationSubcouplingTypes π T) (η : Measure (X × Y)) (hη : η ≤ π)
    (good : T → Measure (X × Y)) (bad : C → T → Measure (X × Y))
    (hsplit : ∀ t, good t + ∑ c, bad c t = (D.rnSubplanTypes η hη).component (false, t))

/-- The fine components cover the same full original population, type by type. -/
theorem rnCellRefinedTypes_sum_eq (hfull : ∑ t, D.component t = π) :
    (∑ tag, (D.rnCellRefinedTypes η hη good bad hsplit).component tag) = π := by
  rw [← sum_groupedMarkComponent _ (cellRefinedOldType (C := C) (T := T))]
  calc
    _ = ∑ t, D.component t := by
      apply Finset.sum_congr rfl
      intro t _
      exact D.rnCellRefinedComponent_grouped_old η hη good bad hsplit t
    _ = π := hfull

end OTSelector.Reconstruction.PopulationSubcouplingTypes

namespace OTSelector.Reconstruction.PopulationTypedCostData

variable {X Y C T : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    [Fintype C] [Fintype T] {π : Measure (X × Y)} [IsFiniteMeasure π]
    {μ : Measure X} {ν : Measure Y} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {q : ℕ} {cost : X → Y → ℝ} (D : PopulationTypedCostData π μ ν T q cost)
    (η : Measure (X × Y)) (hη : η ≤ π)
    (good : T → Measure (X × Y)) (bad : C → T → Measure (X × Y))
    (hsplit : ∀ t, good t + ∑ c, bad c t = (D.types.rnSubplanTypes η hη).component (false, t))
    [MeasurableSpace (Option (CellRefinedType C T))]
    [MeasurableSingletonClass (Option (CellRefinedType C T))]

/-- Every actual original vertex has a fine tag on one full-measure event;
no unmarked exceptional vertices enter retained source-defect arithmetic. -/
theorem rnCellRefinedTypes_iid_some (hπ : Vlasov.IsCoupling π μ ν)
    {I J : Type*} [Fintype I] [Fintype J] :
    let R := D.types.rnCellRefinedTypes η hη good bad hsplit
    ∀ᵐ sample ∂(Measure.pi (fun _ : I ↦ R.sourceMarkedLaw μ)).prod
      (Measure.pi (fun _ : J ↦ R.targetMarkedLaw ν)),
      (∀ i, ∃ tag, (sample.1 i).2 = some tag) ∧
        (∀ j, ∃ tag, (sample.2 j).2 = some tag) :=
  (D.types.rnCellRefinedTypes η hη good bad hsplit).iid_marked_ae_some_of_sum_eq hπ
    (D.types.rnCellRefinedTypes_sum_eq η hη good bad hsplit D.sum_eq)

end OTSelector.Reconstruction.PopulationTypedCostData
