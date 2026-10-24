import OTSelector.Reconstruction.FinslerRelativeLawDeterministicCellTags
import OTSelector.Reconstruction.FinslerRelativeLawOriginalCellwiseAssignment

/-! Full original assignments after prescribed deterministic microscopic truncation. -/
open Set Function MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators Classical
noncomputable section
namespace OTSelector.Reconstruction.PopulationTypedCostData
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000

/-- Any prescribed measurable microscopic cell family can replace the original
retained support on the same whole population. Discarded retained mass joins
the true residual; its original small-mass energy is preserved. The finite
splice requires only literal original false flags and physical cell membership,
with original count/Hall deficits left explicit. -/
theorem exists_original_deterministic_cellwise_full_assignment
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
    ∃ depth : ℕ,
      (∀ tilt : ℝ,
        Integrable (D.originalResidualPressureBudget ξG hξG n depth probe tilt) (R.markedLaw n) ∧
        (1 / (n : ℝ)) * (∫ sample,
          D.originalResidualPressureBudget ξG hξG n depth probe tilt sample ∂R.markedLaw n) ≤
          D.quadraticConstant * dyadicMatchingConstant q *
            (Fintype.card T : ℝ) ^ (2 / (q : ℝ)) * (ξG univ).toReal ^ (1 - 2 / (q : ℝ)) +
          D.globalBound * Real.sqrt (2 * Fintype.card T) *
            (n : ℝ) ^ (2 / (q : ℝ) - 1 / 2) * Real.sqrt (ξG univ).toReal +
          2 * |tilt| * B * (ξG univ).toReal) ∧
      (Integrable (D.originalResidualCountBudget ξG hξG n) (R.markedLaw n) ∧
        (∫ sample, D.originalResidualCountBudget ξG hξG n sample ∂R.markedLaw n) ≤
          Real.sqrt (2 * (n : ℝ) * Fintype.card (Option (Bool × T)))) ∧
      ∀ᵐ sample ∂R.markedLaw n, ∀ tilt : ℝ,
      ∀ retained : C → OTSelector.PartialMatching n n,
      (∀ c e, e ∈ (retained c).edges →
        subplanRetentionFlag (sample.1 e.1).2 = false ∧
        subplanRetentionFlag (sample.2 e.2).2 = false ∧
        a (sample.1 e.1).1 ∈ cell c ∧ a (sample.2 e.2).1 ∈ cell c) →
      ∃ full : Assignment n,
        assignmentCost (fun i j ↦ (n : ℝ) ^ (2 / (q : ℝ)) * cost (sample.1 i).1 (sample.2 j).1 +
          tilt * probe (sample.1 i).1 (sample.2 j).1) full ≤
        (∑ c, (retained c).cost (fun i j ↦ (n : ℝ) ^ (2 / (q : ℝ)) * cost (sample.1 i).1 (sample.2 j).1 +
          tilt * probe (sample.1 i).1 (sample.2 j).1)) +
        D.originalResidualPressureBudget ξG hξG n depth probe tilt sample +
        ((n : ℝ) ^ (2 / (q : ℝ)) * D.globalBound + |tilt| * B) *
          ((Finset.univ.sum (fun c : C ↦
            partitionCount (fun i ↦ tag (sample.1 i)) (some c) - ((retained c).card : ℝ))) +
            D.originalResidualCountBudget ξG hξG n sample) := by
  classical
  let G := ⋃ c, cell c
  let ξG := restrictOriginalRetainedResidual χ ξ a G
  let hξG : ξG ≤ χ + ξ := restrictOriginalRetainedResidual_le χ ξ a ha (MeasurableSet.iUnion hcell)
  let R := D.refineSubplan ξG hξG
  let tag := originalRetainedCellTag a cell (selectedSubplanTags (T := T))
  obtain ⟨depth, henergy, hcount, hfull⟩ := D.exists_original_global_full_assignment
    (C := C) hq hn hπ ξG hξG probe hprobe hB hg
  refine ⟨depth, henergy, hcount, ?_⟩
  have htags := D.original_deterministic_cell_tags_ae χ ξ hπ a ha u horder hμA hνA hcal cell hcell n
  filter_upwards [hfull, htags] with sample hsample htag
  intro tilt retained hretained
  apply hsample tilt (fun i ↦ tag (sample.1 i)) (fun j ↦ tag (sample.2 j))
    htag.1 htag.2 retained
  intro c e he
  have h := hretained c e he
  exact ⟨(originalRetainedCellTag_eq_some_iff a cell hdisj _ _ c).mpr
      ⟨not_mem_selectedSubplanTags_of_flag_false h.1, h.2.2.1⟩,
    (originalRetainedCellTag_eq_some_iff a cell hdisj _ _ c).mpr
      ⟨not_mem_selectedSubplanTags_of_flag_false h.2.1, h.2.2.2⟩⟩

end OTSelector.Reconstruction.PopulationTypedCostData
