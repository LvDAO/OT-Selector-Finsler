import OTSelector.Reconstruction.FinslerRelativeLawDeterministicCellAssignment
import OTSelector.Reconstruction.FinslerRelativeLawOriginalCellwiseExpectation

/-! Original iid expected assignment bounds after prescribed microscopic label truncation. -/
open Set Function MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators Classical
noncomputable section
namespace OTSelector.Reconstruction.PopulationTypedCostData
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2600000

/-- The original physical iid assignment minimum is bounded by all retained
microscopic competitors and the SAME population's enlarged true residual.
Only the prescribed discarded label mass changes the small residual energy;
all completion deficits remain literal original-sample counts. -/
theorem original_deterministic_cellwise_assignment_expectation_le
    {X Z C T : Type*} [MetricSpace X] [MeasurableSpace X] [MeasurableSpace Z]
    [Fintype C] [DecidableEq C] [Fintype T] [DecidableEq T]
    [MeasurableSpace (Option (Bool × T))]
    [MeasurableSingletonClass (Option (Bool × T))]
    (χ ξ : Measure (X × X)) [IsFiniteMeasure χ] [IsFiniteMeasure ξ]
    {μ ν : Measure X} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hπ : Vlasov.IsCoupling (χ + ξ) μ ν)
    {q : ℕ} {cost : X → X → ℝ} (D : PopulationTypedCostData (χ + ξ) μ ν T q cost)
    (a : X → Z) (ha : Measurable a) (u : X → ℝ) {A : Set X}
    (horder : ∀ x ∈ A, ∀ y ∈ A, (a x = a y ∧ u x ≤ u y) ↔ u y - u x = dist x y)
    (hμA : ∀ᵐ x ∂μ, x ∈ A) (hνA : ∀ᵐ y ∂ν, y ∈ A)
    (hcal : ∀ᵐ p ∂χ + ξ, u p.2 - u p.1 = dist p.1 p.2)
    (cell : C → Set Z) (hcell : ∀ c, MeasurableSet (cell c))
    (hdisj : Pairwise (Disjoint on cell))
    {n : ℕ} (hq : 4 < q) (hn : 0 < n)
    (probe : X → X → ℝ) (hprobe : Measurable (Function.uncurry probe))
    {B : ℝ} (hB : 0 ≤ B) (hg : ∀ᵐ p ∂μ.prod ν, |probe p.1 p.2| ≤ B) :
    let G := ⋃ c, cell c
    let ξG := restrictOriginalRetainedResidual χ ξ a G
    let hξG : ξG ≤ χ + ξ := restrictOriginalRetainedResidual_le χ ξ a ha (MeasurableSet.iUnion hcell)
    let R := D.refineSubplan ξG hξG
    let tag := originalRetainedCellTag a cell (selectedSubplanTags (T := T))
    let score := fun tilt (sample : (Fin n → X × Option (Bool × T)) ×
      (Fin n → X × Option (Bool × T))) i j ↦ (n : ℝ) ^ (2 / (q : ℝ)) *
      cost (sample.1 i).1 (sample.2 j).1 + tilt * probe (sample.1 i).1 (sample.2 j).1
    ∀ tilt : ℝ,
    ∀ retained : ((Fin n → X × Option (Bool × T)) × (Fin n → X × Option (Bool × T))) →
        C → OTSelector.PartialMatching n n,
    (∀ c e, MeasurableSet {sample | e ∈ (retained sample c).edges}) →
    (∀ᵐ sample ∂R.markedLaw n, ∀ c e, e ∈ (retained sample c).edges →
      subplanRetentionFlag (sample.1 e.1).2 = false ∧
      subplanRetentionFlag (sample.2 e.2).2 = false ∧
      a (sample.1 e.1).1 ∈ cell c ∧ a (sample.2 e.2).1 ∈ cell c) →
    let retainedCost := fun sample ↦ ∑ c, (retained sample c).cost (score tilt sample)
    let retainedDefect := fun sample ↦ Finset.univ.sum (fun c : C ↦
      partitionCount (fun i ↦ tag (sample.1 i)) (some c) - ((retained sample c).card : ℝ))
    let value := fun sample : (Fin n → X) × (Fin n → X) ↦ perturbedAssignmentValue
      (fun i j ↦ (n : ℝ) ^ (2 / (q : ℝ)) * cost (sample.1 i) (sample.2 j) +
        tilt * probe (sample.1 i) (sample.2 j)) 0 0
    Integrable value ((Measure.pi (fun _ : Fin n ↦ μ)).prod (Measure.pi (fun _ : Fin n ↦ ν))) ∧
      Integrable retainedCost (R.markedLaw n) ∧ Integrable retainedDefect (R.markedLaw n) ∧
      (∫ sample, value sample ∂(Measure.pi (fun _ : Fin n ↦ μ)).prod
        (Measure.pi (fun _ : Fin n ↦ ν))) / (n : ℝ) ≤
      (∫ sample, retainedCost sample ∂R.markedLaw n) / (n : ℝ) +
      (D.quadraticConstant * dyadicMatchingConstant q *
        (Fintype.card T : ℝ) ^ (2 / (q : ℝ)) * (ξG univ).toReal ^ (1 - 2 / (q : ℝ)) +
      D.globalBound * Real.sqrt (2 * Fintype.card T) *
        (n : ℝ) ^ (2 / (q : ℝ) - 1 / 2) * Real.sqrt (ξG univ).toReal +
      2 * |tilt| * B * (ξG univ).toReal) +
      ((n : ℝ) ^ (2 / (q : ℝ)) * D.globalBound + |tilt| * B) *
        ((∫ sample, retainedDefect sample ∂R.markedLaw n) / (n : ℝ) +
          Real.sqrt (2 * (n : ℝ) * Fintype.card (Option (Bool × T))) / (n : ℝ)) := by
  classical
  let G := ⋃ c, cell c
  let ξG := restrictOriginalRetainedResidual χ ξ a G
  let hξG : ξG ≤ χ + ξ := restrictOriginalRetainedResidual_le χ ξ a ha (MeasurableSet.iUnion hcell)
  let R := D.refineSubplan ξG hξG
  let tag := originalRetainedCellTag a cell (selectedSubplanTags (T := T))
  let score := fun tilt (sample : (Fin n → X × Option (Bool × T)) ×
      (Fin n → X × Option (Bool × T))) i j ↦ (n : ℝ) ^ (2 / (q : ℝ)) *
      cost (sample.1 i).1 (sample.2 j).1 + tilt * probe (sample.1 i).1 (sample.2 j).1
  obtain ⟨depth, henergy, hcount, hfull⟩ := D.exists_original_deterministic_cellwise_full_assignment
    χ ξ hπ a ha u horder hμA hνA hcal cell hcell hdisj hq hn probe hprobe hB hg
  dsimp only
  intro tilt retained hmeas hretained
  let retainedCost := fun sample ↦ ∑ c, (retained sample c).cost (score tilt sample)
  let retainedDefect := fun sample ↦ Finset.univ.sum (fun c : C ↦
    partitionCount (fun i ↦ tag (sample.1 i)) (some c) - ((retained sample c).card : ℝ))
  let value := fun sample : (Fin n → X) × (Fin n → X) ↦ perturbedAssignmentValue
    (fun i j ↦ (n : ℝ) ^ (2 / (q : ℝ)) * cost (sample.1 i) (sample.2 j) +
      tilt * probe (sample.1 i) (sample.2 j)) 0 0
  have hvalue := D.original_tilted_assignment_integral hπ ξG hξG n probe hprobe hg tilt
  let _instP : IsProbabilityMeasure (R.markedLaw n) := (R.iid_facts hπ n).1
  have hedges := D.original_marked_tilted_edge_integrable hπ ξG hξG n probe hprobe hg tilt
  have hcost : Integrable retainedCost (R.markedLaw n) :=
    integrable_finsetSum _ (fun c _ ↦ OTSelector.PartialMatching.integrable_sample_cost_of_edge_events
      (R.markedLaw n) (fun sample ↦ retained sample c) (hmeas c) _ hedges)
  have hdefect : Integrable retainedDefect (R.markedLaw n) := by
    apply integrable_finsetSum
    intro c hc
    apply Integrable.sub
    · apply integrable_partitionCount_of_cell_events
      intro i
      exact measurableSet_originalRetainedCellTag_eq_some a ha cell hcell hdisj _
        (fun sample : (Fin n → X × Option (Bool × T)) ×
          (Fin n → X × Option (Bool × T)) ↦ sample.1 i) (by fun_prop) c
    · exact OTSelector.PartialMatching.integrable_sample_card_of_edge_events
        (R.markedLaw n) (fun sample ↦ retained sample c) (hmeas c)
  refine ⟨hvalue.1, hcost, hdefect, ?_⟩
  let completionBound := (n : ℝ) ^ (2 / (q : ℝ)) * D.globalBound + |tilt| * B
  have hcompletion : 0 ≤ completionBound := add_nonneg
    (mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _) D.bound_nonneg)
    (mul_nonneg (abs_nonneg _) hB)
  have hpoint : ∀ᵐ sample ∂R.markedLaw n,
      value ((fun i ↦ (sample.1 i).1), (fun j ↦ (sample.2 j).1)) ≤
        retainedCost sample + D.originalResidualPressureBudget ξG hξG n depth probe tilt sample +
          completionBound * (retainedDefect sample + D.originalResidualCountBudget ξG hξG n sample) := by
    filter_upwards [hfull, hretained] with sample hs hr
    obtain ⟨full, hbound⟩ := hs tilt (retained sample) hr
    exact (perturbedAssignmentValue_le _ 0 0 full).trans (by
      simpa only [perturbedEdgeCost_zero] using hbound)
  have hint := integral_mono_ae hvalue.2.1
    ((hcost.add (henergy tilt).1).add ((hdefect.add hcount.1).const_mul completionBound)) hpoint
  have hsum := integral_add (hcost.add (henergy tilt).1)
    ((hdefect.add hcount.1).const_mul completionBound)
  have hsumRet := integral_add hcost (henergy tilt).1
  have hsumCount := integral_add hdefect hcount.1
  simp only [Pi.add_apply] at hsum hsumRet hsumCount
  rw [hsumRet, integral_const_mul, hsumCount] at hsum
  change (∫ sample, value ((fun i ↦ (sample.1 i).1), (fun j ↦ (sample.2 j).1)) ∂R.markedLaw n) ≤
    ∫ sample, retainedCost sample + D.originalResidualPressureBudget ξG hξG n depth probe tilt sample +
      completionBound * (retainedDefect sample + D.originalResidualCountBudget ξG hξG n sample)
      ∂R.markedLaw n at hint
  rw [hsum] at hint
  have htransfer := hvalue.2.2
  change (∫ sample, value ((fun i ↦ (sample.1 i).1), (fun j ↦ (sample.2 j).1)) ∂R.markedLaw n) =
    ∫ sample, value sample ∂(Measure.pi (fun _ : Fin n ↦ μ)).prod
      (Measure.pi (fun _ : Fin n ↦ ν)) at htransfer
  rw [htransfer] at hint
  have hnormalized : (∫ sample, value sample ∂(Measure.pi (fun _ : Fin n ↦ μ)).prod
      (Measure.pi (fun _ : Fin n ↦ ν))) / (n : ℝ) ≤
      (∫ sample, retainedCost sample ∂R.markedLaw n) / (n : ℝ) +
      (∫ sample, D.originalResidualPressureBudget ξG hξG n depth probe tilt sample ∂R.markedLaw n) /
        (n : ℝ) + completionBound *
          ((∫ sample, retainedDefect sample ∂R.markedLaw n) / (n : ℝ) +
            (∫ sample, D.originalResidualCountBudget ξG hξG n sample ∂R.markedLaw n) / (n : ℝ)) := by
    exact (div_le_div_of_nonneg_right hint (Nat.cast_nonneg n)).trans_eq (by ring)
  apply hnormalized.trans
  apply add_le_add
  · apply add_le_add le_rfl
    calc
      _ = (1 / (n : ℝ)) * (∫ sample,
        D.originalResidualPressureBudget ξG hξG n depth probe tilt sample ∂R.markedLaw n) := by ring
      _ ≤ _ := (henergy tilt).2
  · exact mul_le_mul_of_nonneg_left
      (add_le_add le_rfl (div_le_div_of_nonneg_right hcount.2 (Nat.cast_nonneg n))) hcompletion

end OTSelector.Reconstruction.PopulationTypedCostData
