import OTSelector.Reconstruction.FinslerRelativeLawOriginalAssignmentExpectation
import OTSelector.Reconstruction.FinslerRelativeLawOriginalFineResidualEnergy

/-! Actual original edge integrability and assignment means on the same fine marked experiment. -/
open Set Function MeasureTheory ProbabilityTheory
open scoped BigOperators Classical
noncomputable section
namespace OTSelector.Reconstruction.PopulationTypedCostData
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

variable {X Y C T : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    [Fintype C] [Fintype T] {π : Measure (X × Y)} [IsFiniteMeasure π]
    {μ : Measure X} {ν : Measure Y} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {q : ℕ} {cost : X → Y → ℝ} (D : PopulationTypedCostData π μ ν T q cost)
    (η : Measure (X × Y)) (hη : η ≤ π)
    (good : T → Measure (X × Y)) (bad : C → T → Measure (X × Y))
    (hsplit : ∀ t, good t + ∑ c, bad c t = (D.types.rnSubplanTypes η hη).component (false, t))
    [MeasurableSpace (Option (CellRefinedType C T))]
    [MeasurableSingletonClass (Option (CellRefinedType C T))]

/-- Original compact cost and the actual bounded probe make every physical edge
integrable in the fine experiment, before any adaptive optimizer selects it. -/
theorem rnCellRefinedTypes_original_tilted_edge_integrable
    (hπ : Vlasov.IsCoupling π μ ν) (n : ℕ) (probe : X → Y → ℝ)
    (hprobe : Measurable (Function.uncurry probe))
    {B : ℝ} (hb : ∀ᵐ p ∂μ.prod ν, |probe p.1 p.2| ≤ B) (tilt : ℝ) :
    let R := D.types.rnCellRefinedTypes η hη good bad hsplit
    let P := (Measure.pi (fun _ : Fin n ↦ R.sourceMarkedLaw μ)).prod
      (Measure.pi (fun _ : Fin n ↦ R.targetMarkedLaw ν))
    ∀ i j, Integrable (fun sample ↦ (n : ℝ) ^ (2 / (q : ℝ)) *
      cost (sample.1 i).1 (sample.2 j).1 + tilt * probe (sample.1 i).1 (sample.2 j).1) P := by
  letI : MeasurableSpace (Option T) := ⊤
  letI : MeasurableSingletonClass (Option T) := ⟨fun _ ↦ trivial⟩
  letI : MeasurableSpace (Option (Bool × T)) := ⊤
  letI : MeasurableSingletonClass (Option (Bool × T)) := ⟨fun _ ↦ trivial⟩
  let R := D.types.rnCellRefinedTypes η hη good bad hsplit
  let A := D.refineSubplan η hη
  let P := (Measure.pi (fun _ : Fin n ↦ R.sourceMarkedLaw μ)).prod
    (Measure.pi (fun _ : Fin n ↦ R.targetMarkedLaw ν))
  have hlaw : P.map cellRefinedSubplanObservation = A.markedLaw n :=
    D.types.rnCellRefinedTypes_iid_subplan_law η hη good bad hsplit μ ν
  have hm := measurable_cellRefinedSubplanObservation (X := X) (Y := Y) (C := C) (T := T)
    (I := Fin n) (J := Fin n)
  have hi := D.original_marked_tilted_edge_integrable hπ η hη n probe hprobe hb tilt
  dsimp only
  intro i j
  have hi' := hi i j
  rw [← hlaw] at hi'
  exact hi'.comp_measurable hm

/-- The actual fine physical assignment minimum is integrable and has exactly
the original unmarked iid expectation, with all integrability discharged. -/
theorem rnCellRefinedTypes_original_tilted_assignment_integral
    (hπ : Vlasov.IsCoupling π μ ν) (n : ℕ) (probe : X → Y → ℝ)
    (hprobe : Measurable (Function.uncurry probe))
    {B : ℝ} (hb : ∀ᵐ p ∂μ.prod ν, |probe p.1 p.2| ≤ B) (tilt : ℝ) :
    let R := D.types.rnCellRefinedTypes η hη good bad hsplit
    let P := (Measure.pi (fun _ : Fin n ↦ R.sourceMarkedLaw μ)).prod
      (Measure.pi (fun _ : Fin n ↦ R.targetMarkedLaw ν))
    let P₀ := (Measure.pi (fun _ : Fin n ↦ μ)).prod (Measure.pi (fun _ : Fin n ↦ ν))
    let value := fun sample : (Fin n → X) × (Fin n → Y) ↦ perturbedAssignmentValue
      (fun i j ↦ (n : ℝ) ^ (2 / (q : ℝ)) * cost (sample.1 i) (sample.2 j) +
        tilt * probe (sample.1 i) (sample.2 j)) 0 0
    let fineValue := fun sample : (Fin n → X × Option (CellRefinedType C T)) ×
        (Fin n → Y × Option (CellRefinedType C T)) ↦
      value ((fun i ↦ (sample.1 i).1), (fun j ↦ (sample.2 j).1))
    Integrable value P₀ ∧ Integrable fineValue P ∧
      (∫ sample, fineValue sample ∂P) = ∫ sample, value sample ∂P₀ := by
  let R := D.types.rnCellRefinedTypes η hη good bad hsplit
  let P := (Measure.pi (fun _ : Fin n ↦ R.sourceMarkedLaw μ)).prod
    (Measure.pi (fun _ : Fin n ↦ R.targetMarkedLaw ν))
  have hm (i j : Fin n) : Measurable (fun sample : (Fin n → X) × (Fin n → Y) ↦
      (n : ℝ) ^ (2 / (q : ℝ)) * cost (sample.1 i) (sample.2 j) +
        tilt * probe (sample.1 i) (sample.2 j)) := by
    apply Measurable.add
    · exact (D.measurable_cost.comp (show Measurable
        (fun sample : (Fin n → X) × (Fin n → Y) ↦ (sample.1 i, sample.2 j)) by
          fun_prop)).const_mul _
    · exact (hprobe.comp (show Measurable
        (fun sample : (Fin n → X) × (Fin n → Y) ↦ (sample.1 i, sample.2 j)) by
          fun_prop)).const_mul tilt
  have hmarked := Probability.integrable_assignmentValue P _
    (fun i j ↦ (hm i j).comp (show Measurable (fun sample :
      (Fin n → X × Option (CellRefinedType C T)) ×
        (Fin n → Y × Option (CellRefinedType C T)) ↦
      ((fun i ↦ (sample.1 i).1), (fun j ↦ (sample.2 j).1))) by fun_prop))
    (D.rnCellRefinedTypes_original_tilted_edge_integrable η hη good bad hsplit
      hπ n probe hprobe hb tilt)
  have htransfer := R.iid_physical_integral hπ _ (Probability.measurable_assignmentValue _ hm)
  exact ⟨htransfer.1.mpr hmarked, hmarked, htransfer.2⟩

end OTSelector.Reconstruction.PopulationTypedCostData
