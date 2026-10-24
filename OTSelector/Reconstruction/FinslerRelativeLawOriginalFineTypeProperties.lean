import OTSelector.Probability.CellRefinedPopulation
import OTSelector.Reconstruction.FinslerPopulationTypedCostData

/-! Original endpoint and clock properties hold on every fine type before any core is selected. -/
open Set Function MeasureTheory
open scoped BigOperators Classical
noncomputable section
namespace OTSelector.Reconstruction.PopulationTypedCostData
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

variable {X Y C T : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    [Fintype C] [Fintype T] {π : Measure (X × Y)} [IsFiniteMeasure π]
    {μ : Measure X} {ν : Measure Y} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {q : ℕ} {cost : X → Y → ℝ} (D : PopulationTypedCostData π μ ν T q cost)
    (η : Measure (X × Y)) (hη : η ≤ π)
    (good : T → Measure (X × Y)) (bad : C → T → Measure (X × Y))
    (hsplit : ∀ t, good t + ∑ c, bad c t = (D.types.rnSubplanTypes η hη).component (false, t))
    [MeasurableSpace (Option (CellRefinedType C T))]
    [MeasurableSingletonClass (Option (CellRefinedType C T))]

/-- Every fine marked endpoint retains its actual old-type Good property. -/
theorem rnCellRefinedTypes_iid_old_properties {I J : Type*} [Fintype I] [Fintype J] :
    let R := D.types.rnCellRefinedTypes η hη good bad hsplit
    ∀ᵐ sample ∂(Measure.pi (fun _ : I ↦ R.sourceMarkedLaw μ)).prod
        (Measure.pi (fun _ : J ↦ R.targetMarkedLaw ν)),
      (∀ i tag, (sample.1 i).2 = some tag →
        D.sourceGood (cellRefinedOldType tag) (sample.1 i).1) ∧
      (∀ j tag, (sample.2 j).2 = some tag →
        D.targetGood (cellRefinedOldType tag) (sample.2 j).1) := by
  let R := D.types.rnCellRefinedTypes η hη good bad hsplit
  apply R.iid_marked_type_properties
  · intro tag
    exact ae_mono (Measure.map_mono
      (D.types.rnCellRefinedTypes_component_le_old η hη good bad hsplit tag) measurable_fst)
      (D.source_good _)
  · intro tag
    exact ae_mono (Measure.map_mono
      (D.types.rnCellRefinedTypes_component_le_old η hη good bad hsplit tag) measurable_snd)
      (D.target_good _)

/-- Any actual old-type clock gap holds for all same-old-type fine edges on one
full-measure event, so later good, bad and residual cores may select arbitrary edges. -/
theorem rnCellRefinedTypes_iid_old_forward {I J : Type*} [Fintype I] [Fintype J]
    (sourceClock : X → ℝ) (targetClock : Y → ℝ) (gap : ℝ)
    (hforward : ∀ t x y, D.sourceGood t x → D.targetGood t y →
      gap ≤ targetClock y - sourceClock x) :
    let R := D.types.rnCellRefinedTypes η hη good bad hsplit
    ∀ᵐ sample ∂(Measure.pi (fun _ : I ↦ R.sourceMarkedLaw μ)).prod
        (Measure.pi (fun _ : J ↦ R.targetMarkedLaw ν)),
      ∀ i j tag tag', (sample.1 i).2 = some tag → (sample.2 j).2 = some tag' →
        cellRefinedOldType tag = cellRefinedOldType tag' →
        gap ≤ targetClock (sample.2 j).1 - sourceClock (sample.1 i).1 := by
  have h := D.rnCellRefinedTypes_iid_old_properties (I := I) (J := J) η hη good bad hsplit
  filter_upwards [h] with sample hsample
  intro i j tag tag' hi hj heq
  have hx := hsample.1 i tag hi
  have hy := hsample.2 j tag' hj
  rw [← heq] at hy
  exact hforward _ _ _ hx hy

end OTSelector.Reconstruction.PopulationTypedCostData
