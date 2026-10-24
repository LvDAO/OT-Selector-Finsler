import OTSelector.Reconstruction.FinslerConcreteUpperUniformTypedForward
import OTSelector.Reconstruction.FinslerRelativeLawOriginalGlobalAssignment

/-! A single original typed hierarchy supplies a forward legal core, its
quantitative physical energy, and its original iid count deficiency. No fine
clock bins or reference population enter these constants. -/
open Set Function MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators Classical
noncomputable section
namespace OTSelector.Reconstruction.PopulationTypedCostData
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000

variable {X Y T : Type*} [MeasurableSpace X] [MeasurableSpace Y] [Fintype T]
  {π : Measure (X × Y)} [IsFiniteMeasure π]
  {μ : Measure X} {ν : Measure Y} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
  {q : ℕ} {cost : X → Y → ℝ} (D : PopulationTypedCostData π μ ν T q cost)
  [MeasurableSpace (Option (Bool × T))]
  [MeasurableSingletonClass (Option (Bool × T))]

/-- The original hierarchy core has the small-subplan energy and only an iid
square-root count deficiency, while every retained edge keeps the original
forward clock gap. All three statements concern the same original sample. -/
theorem exists_original_forward_subplan_core
    {n : ℕ} (hq : 4 < q) (hn : 0 < n)
    (hπ : Vlasov.IsCoupling π μ ν) (η : Measure (X × Y)) (hη : η ≤ π)
    (clockS : X → ℝ) (clockT : Y → ℝ) (gap : ℝ)
    (hforward : ∀ t x y, D.sourceGood t x → D.targetGood t y → gap ≤ clockT y - clockS x) :
    let R := D.refineSubplan η hη
    ∃ K : ℕ,
      (Integrable (D.originalResidualPressureBudget η hη n K (fun _ _ ↦ 0) 0) (R.markedLaw n) ∧
        (1 / (n : ℝ)) * (∫ sample,
          D.originalResidualPressureBudget η hη n K (fun _ _ ↦ 0) 0 sample ∂R.markedLaw n) ≤
          D.quadraticConstant * dyadicMatchingConstant q *
            (Fintype.card T : ℝ) ^ (2 / (q : ℝ)) * (η univ).toReal ^ (1 - 2 / (q : ℝ)) +
          D.globalBound * Real.sqrt (2 * Fintype.card T) *
            (n : ℝ) ^ (2 / (q : ℝ) - 1 / 2) * Real.sqrt (η univ).toReal) ∧
      (Integrable (D.originalResidualCountBudget η hη n) (R.markedLaw n) ∧
        (∫ sample, D.originalResidualCountBudget η hη n sample ∂R.markedLaw n) ≤
          Real.sqrt (2 * (n : ℝ) * Fintype.card (Option (Bool × T)))) ∧
      ∀ᵐ sample ∂R.markedLaw n,
      let x := fun i ↦ R.sourceSample n i sample
      let y := fun j ↦ R.targetSample n j sample
      let full := taggedHierarchyAssignment K (R.sourceSample n) (R.targetSample n) sample
      let core := selectedSameTypeMatching (selectedSubplanTags (T := T))
        (fun i ↦ (x i).1) (fun j ↦ (y j).1) full
      (∀ e ∈ core.edges, gap ≤ clockT (sample.2 e.2).1 - clockS (sample.1 e.1).1) ∧
      core.cost (fun i j ↦ (n : ℝ) ^ (2 / (q : ℝ)) * cost (sample.1 i).1 (sample.2 j).1) ≤
        D.originalResidualPressureBudget η hη n K (fun _ _ ↦ 0) 0 sample ∧
      (∑ t ∈ selectedSubplanTags (T := T), partitionCount (fun i ↦ (x i).1) t) - (core.card : ℝ) ≤
        D.originalResidualCountBudget η hη n sample := by
  classical
  let R := D.refineSubplan η hη
  obtain ⟨K, hK⟩ := D.fixed_subplan_pressure_recovery hq hn hπ η hη
    (fun _ _ ↦ 0) measurable_const (G := 0) (by rfl) (Filter.Eventually.of_forall (by simp))
  refine ⟨K, ?_, D.originalResidualCountBudget_expectation hπ η hη n, ?_⟩
  · constructor
    · exact (hK 0).1
    · simpa only [originalResidualPressureBudget, abs_zero, zero_mul, mul_zero, add_zero, R] using (hK 0).2
  have hf := D.refineSubplan_selectedSameTypeMatching_forward clockS clockT gap hforward η hη n
  have hnneg := (R.iid_cost_bounds hπ n).1
  filter_upwards [hf, hnneg] with sample hs hnneg
  let x := fun i ↦ R.sourceSample n i sample
  let y := fun j ↦ R.targetSample n j sample
  let full := taggedHierarchyAssignment K (R.sourceSample n) (R.targetSample n) sample
  let core := selectedSameTypeMatching (selectedSubplanTags (T := T))
    (fun i ↦ (x i).1) (fun j ↦ (y j).1) full
  refine ⟨hs full, ?_, ?_⟩
  · have h := selectedSameTypeMatching_cost_le_attributed (selectedSubplanTags (T := T))
      x y full (fun i j ↦ (n : ℝ) ^ (2 / (q : ℝ)) * cost (sample.1 i).1 (sample.2 j).1)
      (fun i j ↦ mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _) (hnneg i j))
    simpa only [originalResidualPressureBudget, abs_zero, zero_mul, mul_zero, add_zero, R, x, y, full, core] using h
  · have hsat := taggedHierarchy_type_no_opposite x y
      (firstOptimalAssignment_isOptimal (taggedHierarchyCost K x y))
    have h := selectedSameTypeMatching_source_defect_le (selectedSubplanTags (T := T))
      (fun i ↦ (x i).1) (fun j ↦ (y j).1) full hsat
    apply h.trans
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun _ _ _ ↦ abs_nonneg _)

end OTSelector.Reconstruction.PopulationTypedCostData
