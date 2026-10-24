import OTSelector.Probability.CellRefinedPopulation
import OTSelector.Reconstruction.FinslerRelativeLawOriginalGlobalAssignment

/-! True residual energy and count budgets on the same fine original good/bad experiment. -/
open Set Function MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators Classical
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

/-- Forget only the good/bad subdivision, retaining the original residual flag and old atlas type. -/
def cellRefinedSubplanObservation {X Y C T I J : Type*}
    (sample : (I → X × Option (CellRefinedType C T)) ×
      (J → Y × Option (CellRefinedType C T))) :
    (I → X × Option (Bool × T)) × (J → Y × Option (Bool × T)) :=
  ((fun i ↦ ((sample.1 i).1, (sample.1 i).2.map cellRefinedSubplanType)),
    (fun j ↦ ((sample.2 j).1, (sample.2 j).2.map cellRefinedSubplanType)))

theorem measurable_cellRefinedSubplanObservation {X Y C T I J : Type*}
    [MeasurableSpace X] [MeasurableSpace Y] [Fintype C] [Fintype T]
    [MeasurableSpace (Option (Bool × T))] [MeasurableSingletonClass (Option (Bool × T))]
    [MeasurableSpace (Option (CellRefinedType C T))]
    [MeasurableSingletonClass (Option (CellRefinedType C T))] :
    Measurable (cellRefinedSubplanObservation (X := X) (Y := Y) (C := C) (T := T)
      (I := I) (J := J)) := by
  have hm : Measurable (Option.map (cellRefinedSubplanType (C := C) (T := T))) :=
    measurable_of_countable _
  exact (measurable_pi_lambda _ (fun i ↦
    (((measurable_pi_apply i).comp measurable_fst).fst).prodMk
      (hm.comp ((measurable_pi_apply i).comp measurable_fst).snd))).prodMk
    (measurable_pi_lambda _ (fun j ↦
      (((measurable_pi_apply j).comp measurable_snd).fst).prodMk
        (hm.comp ((measurable_pi_apply j).comp measurable_snd).snd)))

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

/-- The true original residual keeps its small-mass energy rate on the same fine
sample used by both retained hierarchies. Only original RN type counts appear
in its completion error; neither fine type cardinality nor bad mass is charged here. -/
theorem exists_rnCellRefinedTypes_original_residual_budgets
    {n : ℕ} (hq : 4 < q) (hn : 0 < n) (hπ : Vlasov.IsCoupling π μ ν)
    (probe : X → Y → ℝ) (hprobe : Measurable (Function.uncurry probe))
    {B : ℝ} (hB : 0 ≤ B) (hb : ∀ᵐ p ∂μ.prod ν, |probe p.1 p.2| ≤ B) :
    let R := D.types.rnCellRefinedTypes η hη good bad hsplit
    let P := (Measure.pi (fun _ : Fin n ↦ R.sourceMarkedLaw μ)).prod
      (Measure.pi (fun _ : Fin n ↦ R.targetMarkedLaw ν))
    ∃ K : ℕ,
      (∀ tilt : ℝ,
        Integrable (fun sample ↦ D.originalResidualPressureBudget η hη n K probe tilt
          (cellRefinedSubplanObservation sample)) P ∧
        (1 / (n : ℝ)) * (∫ sample, D.originalResidualPressureBudget η hη n K probe tilt
          (cellRefinedSubplanObservation sample) ∂P) ≤
          D.quadraticConstant * dyadicMatchingConstant q *
            (Fintype.card T : ℝ) ^ (2 / (q : ℝ)) *
              (η univ).toReal ^ (1 - 2 / (q : ℝ)) +
          D.globalBound * Real.sqrt (2 * Fintype.card T) *
            (n : ℝ) ^ (2 / (q : ℝ) - 1 / 2) * Real.sqrt (η univ).toReal +
          2 * |tilt| * B * (η univ).toReal) ∧
      Integrable (fun sample ↦ D.originalResidualCountBudget η hη n
        (cellRefinedSubplanObservation sample)) P ∧
      (∫ sample, D.originalResidualCountBudget η hη n
        (cellRefinedSubplanObservation sample) ∂P) ≤
          Real.sqrt (2 * (n : ℝ) * Fintype.card (Option (Bool × T))) := by
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
  obtain ⟨K, henergy, hcount, _⟩ :=
    D.exists_original_global_full_assignment (C := Unit) hq hn hπ η hη probe hprobe hB hb
  dsimp only
  refine ⟨K, ?_, ?_, ?_⟩
  · intro tilt
    obtain ⟨hi, he⟩ := htransfer _ (henergy tilt).1
    exact ⟨hi, by rw [he]; exact (henergy tilt).2⟩
  · exact (htransfer _ hcount.1).1
  · rw [(htransfer _ hcount.1).2]
    exact hcount.2

end PopulationTypedCostData
end OTSelector.Reconstruction
