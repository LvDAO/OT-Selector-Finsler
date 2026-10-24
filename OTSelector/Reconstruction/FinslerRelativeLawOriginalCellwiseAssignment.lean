import OTSelector.Reconstruction.FinslerRelativeLawOriginalGlobalAssignment
import OTSelector.Reconstruction.FinslerRelativeLawRetainedCellLabels

/-! The actual original global retained population supplies its finite-cell
partition on the same residual-marked sample. Thus original cell competitors
and the small original residual hierarchy give a full physical assignment. -/

open Set Function MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators Classical
noncomputable section
namespace OTSelector.Reconstruction.PopulationTypedCostData
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000

/-- Original conditional clock kernels, the fixed original inverse, and the
actual population split discharge the cell-partition premise. Each retained
competitor needs only its literal false flags and original physical cell
membership. The remaining bounded completion pays original count/Hall defects;
the true residual keeps its small-mass energy estimate. -/
theorem exists_original_cellwise_full_assignment
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
    {G : ℝ} (hG : 0 ≤ G) (hg : ∀ᵐ p ∂μ.prod ν, |probe p.1 p.2| ≤ G) :
    let hξ : ξ ≤ πWhole := by rw [hsplit]; exact Measure.le_add_left le_rfl
    let R := D.refineSubplan ξ hξ
    let tag := originalRetainedCellTag a cell (selectedSubplanTags (T := T))
    ∃ depth : ℕ,
      (∀ tilt : ℝ,
        Integrable (D.originalResidualPressureBudget ξ hξ n depth probe tilt) (R.markedLaw n) ∧
        (1 / (n : ℝ)) * (∫ sample,
          D.originalResidualPressureBudget ξ hξ n depth probe tilt sample ∂R.markedLaw n) ≤
          D.quadraticConstant * dyadicMatchingConstant q *
            (Fintype.card T : ℝ) ^ (2 / (q : ℝ)) * (ξ univ).toReal ^ (1 - 2 / (q : ℝ)) +
          D.globalBound * Real.sqrt (2 * Fintype.card T) *
            (n : ℝ) ^ (2 / (q : ℝ) - 1 / 2) * Real.sqrt (ξ univ).toReal +
          2 * |tilt| * G * (ξ univ).toReal) ∧
      (Integrable (D.originalResidualCountBudget ξ hξ n) (R.markedLaw n) ∧
        (∫ sample, D.originalResidualCountBudget ξ hξ n sample ∂R.markedLaw n) ≤
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
        D.originalResidualPressureBudget ξ hξ n depth probe tilt sample +
        ((n : ℝ) ^ (2 / (q : ℝ)) * D.globalBound + |tilt| * G) *
          ((Finset.univ.sum (fun c : C ↦
            partitionCount (fun i ↦ tag (sample.1 i)) (some c) - ((retained c).card : ℝ))) +
            D.originalResidualCountBudget ξ hξ n sample) := by
  classical
  let hξ : ξ ≤ πWhole := by rw [hsplit]; exact Measure.le_add_left le_rfl
  let R := D.refineSubplan ξ hξ
  let tag := originalRetainedCellTag a cell (selectedSubplanTags (T := T))
  obtain ⟨depth, henergy, hcount, hfull⟩ := D.exists_original_global_full_assignment
    (C := C) hq hn hπWhole ξ hξ probe hprobe hG hg
  refine ⟨depth, henergy, hcount, ?_⟩
  have htags := D.original_global_cell_tags_ae lambda a u ha hu b hb hμinv hνinv
    hlabel0 hlabel1 cell hcell Kcell Qglobal hwhole πWhole ξ hπWhole hsplit n
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
