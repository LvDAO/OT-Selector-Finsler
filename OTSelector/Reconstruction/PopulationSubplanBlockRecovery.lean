import OTSelector.Reconstruction.PopulationTypedSubplanCompetitor
import OTSelector.Reconstruction.TaggedRepairBlockPressure

/-!
# Original small-mass recovery survives local pressure replacement

One marked full competitor is built from the deterministic original subplan.
Replacing every retained equal-type block by an exact local pressure minimizer
preserves its entire selected-piece energy, including the count-repair edges.
-/

open Set Function MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators Classical
noncomputable section
namespace OTSelector.Reconstruction.PopulationTypedCostData
set_option backward.isDefEq.respectTransparency false

variable {X Y T : Type*} [MeasurableSpace X] [MeasurableSpace Y] [Fintype T]
  [MeasurableSpace (Option (Bool × T))] [MeasurableSingletonClass (Option (Bool × T))]
  {π : Measure (X × Y)} [IsFiniteMeasure π]
  {μ : Measure X} {ν : Measure Y} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
  {q : ℕ} {cost : X → Y → ℝ} (D : PopulationTypedCostData π μ ν T q cost)

/-- The actual full assignment after exact optimization of all retained blocks.
The selected subplan and original count-completion edges stay fixed. -/
def subplanBlockAssignment (η : Measure (X × Y)) (hη : η ≤ π) (n K : ℕ)
    (objective : ((Fin n → X × Option (Bool × T)) ×
      (Fin n → Y × Option (Bool × T))) → Fin n → Fin n → ℝ)
    (ξ : (Fin n → X × Option (Bool × T)) × (Fin n → Y × Option (Bool × T))) :
    Assignment n :=
  let R := D.refineSubplan η hη
  let σ := taggedHierarchyAssignment K (R.sourceSample n) (R.targetSample n) ξ
  optimizeAssignmentBlocks (objective ξ) σ
    (retainedRepairBlockTag (selectedSubplanTags (T := T))
      (fun i ↦ (R.sourceSample n i ξ).1) (fun i ↦ (R.targetSample n i ξ).1) σ)

omit [MeasurableSpace (Option (Bool × T))]
  [MeasurableSingletonClass (Option (Bool × T))]
  [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] in
/-- The selected-piece contribution is exactly unchanged for every local
objective, even when that objective depends on the full original sample. -/
theorem subplanBlockAssignment_attributed_energy_eq
    (η : Measure (X × Y)) (hη : η ≤ π) (n K : ℕ)
    (objective : ((Fin n → X × Option (Bool × T)) ×
      (Fin n → Y × Option (Bool × T))) → Fin n → Fin n → ℝ)
    (ξ : (Fin n → X × Option (Bool × T)) × (Fin n → Y × Option (Bool × T))) :
    let R := D.refineSubplan η hη
    attributedTypesEnergy (selectedSubplanTags (T := T))
      (fun i ↦ R.sourceSample n i ξ) (fun i ↦ R.targetSample n i ξ)
      (fun i j ↦ cost (ξ.1 i).1 (ξ.2 j).1)
      (D.subplanBlockAssignment η hη n K objective ξ) =
        D.subplanAttributedEnergy η hη n K ξ :=
  attributedTypesEnergy_optimizeRepairBlocks _ _ _ _ _ _

/-- The original deterministic subplan's energy estimate therefore remains valid
after arbitrary exact local pressure minimization on all retained blocks. -/
theorem fixed_subplan_local_pressure_recovery {n : ℕ} (hq : 4 < q) (hn : 0 < n)
    (hπ : Vlasov.IsCoupling π μ ν) (η : Measure (X × Y)) (hη : η ≤ π) :
    let R := D.refineSubplan η hη
    ∃ K : ℕ, ∀ objective : ((Fin n → X × Option (Bool × T)) ×
      (Fin n → Y × Option (Bool × T))) → Fin n → Fin n → ℝ,
      let selected := fun ξ ↦ attributedTypesEnergy (selectedSubplanTags (T := T))
        (fun i ↦ R.sourceSample n i ξ) (fun i ↦ R.targetSample n i ξ)
        (fun i j ↦ cost (ξ.1 i).1 (ξ.2 j).1)
        (D.subplanBlockAssignment η hη n K objective ξ)
      Integrable selected (R.markedLaw n) ∧
        ((n : ℝ) ^ (2 / (q : ℝ)) / n) * (∫ ξ, selected ξ ∂R.markedLaw n) ≤
          D.quadraticConstant * dyadicMatchingConstant q *
            (Fintype.card T : ℝ) ^ (2 / (q : ℝ)) *
            (η univ).toReal ^ (1 - 2 / (q : ℝ)) +
          D.globalBound * Real.sqrt (2 * Fintype.card T) *
            (n : ℝ) ^ (2 / (q : ℝ) - 1 / 2) * Real.sqrt (η univ).toReal := by
  obtain ⟨K, hK⟩ := D.fixed_subplan_energy hq hn hπ η hη
  refine ⟨K, fun objective ↦ ?_⟩
  simpa only [D.subplanBlockAssignment_attributed_energy_eq] using hK

end OTSelector.Reconstruction.PopulationTypedCostData
