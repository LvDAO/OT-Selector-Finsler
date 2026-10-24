import OTSelector.Reconstruction.FinslerRelativeLawOriginalCellwiseExpectation
import OTSelector.Reconstruction.FinslerRelativeLawOriginalCellOptimizer

/-! Canonical actual original retained-cell optimizers give an expected upper
bound for the original physical iid assignment minimum with no matching
selection, insertion support, or integrability premise. -/

open Set Function MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators Classical
noncomputable section
namespace OTSelector.Reconstruction.PopulationTypedCostData
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2600000

/-- The fixed first legal optimizer on each actual original retained-cell graph
removes both retained matching measurability and insertion-support premises.
Its physical cost and true source/Hall defects are the only local summaries
left for the frozen-class expectation comparison. -/
theorem original_canonical_cellwise_assignment_expectation_le
    {X Z C T : Type*} [MeasurableSpace X] [MeasurableSpace Z] [MeasurableEq Z]
    [Fintype C] [DecidableEq C] [Fintype T] [DecidableEq T]
    [MeasurableSpace (Option (Bool × T))]
    [MeasurableSingletonClass (Option (Bool × T))]
    {μ ν : Measure X} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (lambda : Measure Z) [SFinite lambda]
    (a : X → Z) (u : X → ℝ) (ha : Measurable a) (hu : Measurable u)
    (b : Z × ℝ → X) (hb : Measurable b)
    (hμinv : ∀ᵐ x ∂μ, b (a x, u x) = x) (hνinv : ∀ᵐ y ∂ν, b (a y, u y) = y)
    (hlabel0 : μ.map a = lambda) (hlabel1 : ν.map a = lambda)
    (cell : C → Set Z) (hcell : ∀ c, MeasurableSet (cell c))
    (hdisj : Pairwise (Disjoint on cell))
    (Kcell : C → Kernel Z (ℝ × ℝ)) [∀ c, IsSFiniteKernel (Kcell c)]
    (Qglobal : Kernel Z (ℝ × ℝ)) [IsSFiniteKernel Qglobal]
    (hwhole : ∀ᵐ z ∂lambda, Vlasov.IsCoupling
      (finiteCellPairKernel cell hcell Kcell z + Qglobal z)
        (condDistrib u a μ z) (condDistrib u a ν z))
    (πWhole ξ : Measure (X × X)) [IsFiniteMeasure πWhole]
    (hπWhole : Vlasov.IsCoupling πWhole μ ν)
    (hsplit : πWhole = (((lambda ⊗ₘ finiteCellPairKernel cell hcell Kcell).map
      sameLabelPopulationPair).map (Prod.map b b)) + ξ)
    {q : ℕ} {cost : X → X → ℝ} (D : PopulationTypedCostData πWhole μ ν T q cost)
    {n : ℕ} (hq : 4 < q) (hn : 0 < n)
    (probe : X → X → ℝ) (hprobe : Measurable (Function.uncurry probe))
    {G : ℝ} (hG : 0 ≤ G) (hg : ∀ᵐ p ∂μ.prod ν, |probe p.1 p.2| ≤ G)
    (extra : C → ((Fin n → X × Option (Bool × T)) × (Fin n → X × Option (Bool × T))) →
      Finset (Fin n × Fin n))
    (hextra : ∀ c S, MeasurableSet {sample | extra c sample = S})
    (model : ℝ → C → ((Fin n → X × Option (Bool × T)) × (Fin n → X × Option (Bool × T))) →
      Fin n → Fin n → ℝ)
    (hmodel : ∀ tilt c i j, Measurable (fun sample ↦ model tilt c sample i j)) :
    let hξ : ξ ≤ πWhole := by rw [hsplit]; exact Measure.le_add_left le_rfl
    let R := D.refineSubplan ξ hξ
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
        (Fintype.card T : ℝ) ^ (2 / (q : ℝ)) * (ξ univ).toReal ^ (1 - 2 / (q : ℝ)) +
      D.globalBound * Real.sqrt (2 * Fintype.card T) *
        (n : ℝ) ^ (2 / (q : ℝ) - 1 / 2) * Real.sqrt (ξ univ).toReal +
      2 * |tilt| * G * (ξ univ).toReal) +
      ((n : ℝ) ^ (2 / (q : ℝ)) * D.globalBound + |tilt| * G) *
        ((∫ sample, retainedDefect sample ∂R.markedLaw n) / (n : ℝ) +
          Real.sqrt (2 * (n : ℝ) * Fintype.card (Option (Bool × T))) / (n : ℝ)) := by
  classical
  dsimp only
  intro tilt
  exact D.original_cellwise_assignment_expectation_le
    lambda a u ha hu b hb hμinv hνinv hlabel0 hlabel1 cell hcell hdisj Kcell Qglobal
    hwhole πWhole ξ hπWhole hsplit hq hn probe hprobe hG hg tilt
    (fun sample c ↦ originalRetainedCellOptimizer a cell extra (model tilt) c sample)
    (fun c e ↦ measurableSet_mem_originalRetainedCellOptimizer a ha cell hcell extra hextra
      (model tilt) (hmodel tilt) c e)
    (Filter.Eventually.of_forall fun sample c e he ↦
      (originalRetainedCellOptimizer_support a cell extra (model tilt) c sample e he).2)

end OTSelector.Reconstruction.PopulationTypedCostData
