import OTSelector.Reconstruction.FinslerRelativeLawDeterministicCellExpectation
import OTSelector.Reconstruction.FinslerRelativeLawOriginalCellOptimizer

/-! Canonical finite optimizers after deterministic original label truncation. -/
open Set Function MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators Classical
noncomputable section
namespace OTSelector.Reconstruction.PopulationTypedCostData
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000

/-- The canonical frozen optimizer on each prescribed retained microscopic cell
supplies the original iid expected upper bound, with no optimizer selection,
cell-support or new conditional-kernel glue premise after truncation. -/
theorem original_canonical_deterministic_cellwise_assignment_expectation_le
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
    {B : ℝ} (hB : 0 ≤ B) (hg : ∀ᵐ p ∂μ.prod ν, |probe p.1 p.2| ≤ B)
    (extra : C → ((Fin n → X × Option (Bool × T)) × (Fin n → X × Option (Bool × T))) →
      Finset (Fin n × Fin n))
    (hextra : ∀ c S, MeasurableSet {sample | extra c sample = S})
    (model : ℝ → C → ((Fin n → X × Option (Bool × T)) × (Fin n → X × Option (Bool × T))) →
      Fin n → Fin n → ℝ)
    (hmodel : ∀ tilt c i j, Measurable (fun sample ↦ model tilt c sample i j)) :
    let G := ⋃ c, cell c
    let ξG := restrictOriginalRetainedResidual χ ξ a G
    let hξG : ξG ≤ χ + ξ := restrictOriginalRetainedResidual_le χ ξ a ha (MeasurableSet.iUnion hcell)
    let R := D.refineSubplan ξG hξG
    let tag := originalRetainedCellTag a cell (selectedSubplanTags (T := T))
    let score := fun tilt (sample : (Fin n → X × Option (Bool × T)) ×
      (Fin n → X × Option (Bool × T))) i j ↦ (n : ℝ) ^ (2 / (q : ℝ)) *
      cost (sample.1 i).1 (sample.2 j).1 + tilt * probe (sample.1 i).1 (sample.2 j).1
    ∀ tilt : ℝ,
    let retained := fun sample c ↦ originalRetainedCellOptimizer a cell extra (model tilt) c sample
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
  dsimp only
  intro tilt
  exact D.original_deterministic_cellwise_assignment_expectation_le
    χ ξ hπ a ha u horder hμA hνA hcal cell hcell hdisj hq hn probe hprobe hB hg tilt
    (fun sample c ↦ originalRetainedCellOptimizer a cell extra (model tilt) c sample)
    (fun c e ↦ measurableSet_mem_originalRetainedCellOptimizer a ha cell hcell extra hextra
      (model tilt) (hmodel tilt) c e)
    (Filter.Eventually.of_forall fun sample c e he ↦
      (originalRetainedCellOptimizer_support a cell extra (model tilt) c sample e he).2)

end OTSelector.Reconstruction.PopulationTypedCostData
