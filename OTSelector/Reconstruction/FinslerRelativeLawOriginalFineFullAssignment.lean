import OTSelector.Reconstruction.FinslerRelativeLawOriginalFineResidualEnergy

/-! The original full assignment repair holds on the same fine good/bad/residual experiment. -/
open Set Function MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators Classical
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

/-- The true original residual consists precisely of the false left fine marks. -/
def cellRefinedResidualTag {C T : Type*} (tag : Option (CellRefinedType C T)) : Prop :=
  ∃ t, tag = some (.inl (false, t))

theorem cellRefinedSubplanType_mem_selected_iff {C T : Type*} [Fintype T]
    (tag : Option (CellRefinedType C T)) :
    tag.map cellRefinedSubplanType ∈ PopulationTypedCostData.selectedSubplanTags (T := T) ↔
      cellRefinedResidualTag tag := by
  classical
  cases tag with
  | none => simp [PopulationTypedCostData.selectedSubplanTags, cellRefinedResidualTag]
  | some tag =>
    cases tag with
    | inl p =>
      rcases p with ⟨b, t⟩
      cases b <;> simp [PopulationTypedCostData.selectedSubplanTags,
        cellRefinedResidualTag, cellRefinedSubplanType]
    | inr p => simp [PopulationTypedCostData.selectedSubplanTags,
        cellRefinedResidualTag, cellRefinedSubplanType]

namespace PopulationTypedCostData
variable {X Y C T : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    [Fintype C] [Fintype T] {π : Measure (X × Y)} [IsFiniteMeasure π]
    {μ : Measure X} {ν : Measure Y} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {q : ℕ} {cost : X → Y → ℝ} (D : PopulationTypedCostData π μ ν T q cost)
    (η : Measure (X × Y)) (hη : η ≤ π)
    (good : T → Measure (X × Y)) (bad : C → T → Measure (X × Y))
    (hsplit : ∀ t, good t + ∑ c, bad c t = (D.types.rnSubplanTypes η hη).component (false, t))
    [MeasurableSpace (Option (Bool × T))] [MeasurableSingletonClass (Option (Bool × T))]
    [MeasurableSpace (Option (CellRefinedType C T))]
    [MeasurableSingletonClass (Option (CellRefinedType C T))]

/-- Retained matchings and the true residual are spliced on the same original
indices. The true residual retains its small-mass energy estimate, and bounded
completion pays only the genuine retained deficiencies and original type count error. -/
theorem exists_rnCellRefinedTypes_original_full_assignment
    {L : Type*} [Fintype L] [DecidableEq L]
    {n : ℕ} (hq : 4 < q) (hn : 0 < n) (hπ : Vlasov.IsCoupling π μ ν)
    (probe : X → Y → ℝ) (hprobe : Measurable (Function.uncurry probe))
    {B : ℝ} (hB : 0 ≤ B) (hb : ∀ᵐ p ∂μ.prod ν, |probe p.1 p.2| ≤ B) :
    let R := D.types.rnCellRefinedTypes η hη good bad hsplit
    let P := (Measure.pi (fun _ : Fin n ↦ R.sourceMarkedLaw μ)).prod
      (Measure.pi (fun _ : Fin n ↦ R.targetMarkedLaw ν))
    let pressure := fun K tilt sample ↦ D.originalResidualPressureBudget η hη n K probe tilt
      (cellRefinedSubplanObservation sample)
    let count := fun sample ↦ D.originalResidualCountBudget η hη n
      (cellRefinedSubplanObservation sample)
    ∃ K : ℕ,
      (∀ tilt : ℝ, Integrable (pressure K tilt) P ∧
        (1 / (n : ℝ)) * (∫ sample, pressure K tilt sample ∂P) ≤
          D.quadraticConstant * dyadicMatchingConstant q *
            (Fintype.card T : ℝ) ^ (2 / (q : ℝ)) *
              (η univ).toReal ^ (1 - 2 / (q : ℝ)) +
          D.globalBound * Real.sqrt (2 * Fintype.card T) *
            (n : ℝ) ^ (2 / (q : ℝ) - 1 / 2) * Real.sqrt (η univ).toReal +
          2 * |tilt| * B * (η univ).toReal) ∧
      (Integrable count P ∧ (∫ sample, count sample ∂P) ≤
        Real.sqrt (2 * (n : ℝ) * Fintype.card (Option (Bool × T)))) ∧
      ∀ᵐ sample ∂P, ∀ tilt : ℝ,
      ∀ sourceCell targetCell : Fin n → Option L,
      (∀ i, sourceCell i = none ↔ cellRefinedResidualTag (sample.1 i).2) →
      (∀ j, targetCell j = none ↔ cellRefinedResidualTag (sample.2 j).2) →
      ∀ retained : L → OTSelector.PartialMatching n n,
      (∀ c e, e ∈ (retained c).edges → sourceCell e.1 = some c ∧ targetCell e.2 = some c) →
      ∃ full : Assignment n,
        assignmentCost (fun i j ↦ (n : ℝ) ^ (2 / (q : ℝ)) *
          cost (sample.1 i).1 (sample.2 j).1 + tilt * probe (sample.1 i).1 (sample.2 j).1) full ≤
        (∑ c : L, (retained c).cost (fun i j ↦ (n : ℝ) ^ (2 / (q : ℝ)) *
          cost (sample.1 i).1 (sample.2 j).1 + tilt * probe (sample.1 i).1 (sample.2 j).1)) +
        pressure K tilt sample + ((n : ℝ) ^ (2 / (q : ℝ)) * D.globalBound + |tilt| * B) *
          ((∑ c : L, (partitionCount sourceCell (some c) - ((retained c).card : ℝ))) +
            count sample) := by
  let R := D.types.rnCellRefinedTypes η hη good bad hsplit
  let A := D.refineSubplan η hη
  let P := (Measure.pi (fun _ : Fin n ↦ R.sourceMarkedLaw μ)).prod
    (Measure.pi (fun _ : Fin n ↦ R.targetMarkedLaw ν))
  have hm := measurable_cellRefinedSubplanObservation (X := X) (Y := Y) (C := C) (T := T)
    (I := Fin n) (J := Fin n)
  letI : MeasurableSpace (Option T) := ⊤
  letI : MeasurableSingletonClass (Option T) := ⟨fun _ ↦ trivial⟩
  have hlaw : P.map cellRefinedSubplanObservation = A.markedLaw n :=
    D.types.rnCellRefinedTypes_iid_subplan_law η hη good bad hsplit μ ν
  have htransfer (f : (Fin n → X × Option (Bool × T)) ×
      (Fin n → Y × Option (Bool × T)) → ℝ) (hi : Integrable f (A.markedLaw n)) :
      Integrable (fun sample ↦ f (cellRefinedSubplanObservation sample)) P ∧
        (∫ sample, f (cellRefinedSubplanObservation sample) ∂P) =
          ∫ sample, f sample ∂A.markedLaw n := by
    have hmapI : Integrable f (P.map cellRefinedSubplanObservation) := by rwa [hlaw]
    refine ⟨hmapI.comp_measurable hm, ?_⟩
    rw [← integral_map hm.aemeasurable hmapI.aestronglyMeasurable, hlaw]
  obtain ⟨K, henergy, hcount, hfull⟩ :=
    D.exists_original_global_full_assignment (C := L) hq hn hπ η hη probe hprobe hB hb
  dsimp only
  refine ⟨K, ?_, ?_, ?_⟩
  · intro tilt
    obtain ⟨hi, he⟩ := htransfer _ (henergy tilt).1
    exact ⟨hi, by rw [he]; exact (henergy tilt).2⟩
  · exact ⟨(htransfer _ hcount.1).1, by rw [(htransfer _ hcount.1).2]; exact hcount.2⟩
  · rw [← hlaw] at hfull
    have hf := ae_of_ae_map hm.aemeasurable hfull
    filter_upwards [hf] with sample hsample
    intro tilt sourceCell targetCell hsource htarget retained hretained
    apply hsample tilt sourceCell targetCell ?_ ?_ retained hretained
    · intro i
      exact (hsource i).trans (cellRefinedSubplanType_mem_selected_iff (sample.1 i).2).symm
    · intro j
      exact (htarget j).trans (cellRefinedSubplanType_mem_selected_iff (sample.2 j).2).symm

end PopulationTypedCostData
end OTSelector.Reconstruction
