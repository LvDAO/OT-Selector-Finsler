import OTSelector.Reconstruction.FinslerRelativeLawOriginalGoodBadCanonicalDefect
import OTSelector.Reconstruction.FinslerRelativeLawOriginalFineFullRetention
import OTSelector.Reconstruction.FinslerRelativeLawOriginalFineBadCellProperties
import OTSelector.Reconstruction.FinslerRelativeLawOriginalTruncatedCompactSplit

/-! Actual canonical legal retained cells and the true residual form a full original assignment. -/
open Set Function MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators Classical
noncomputable section
namespace OTSelector.Reconstruction.PopulationTypedCostData
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
set_option linter.style.haveILetI false

/-- Actual canonical legal retained-cell competitors and the original true residual
form a full assignment on the same fine original experiment. Good/bad hierarchy
cores control only the genuine canonical source defect; all costs in the retained
term are those of the literal canonical competitors. -/
theorem exists_original_truncated_compact_canonical_full_assignment
    {X Z C T : Type*} [MetricSpace X] [MeasurableSpace X] [MeasurableSpace Z]
    [Fintype C] [Fintype T] [DecidableEq T]
    [MeasurableSpace (Option (Bool × T))]
    [MeasurableSingletonClass (Option (Bool × T))]
    [MeasurableSpace (Option (CellRefinedType C T))]
    [MeasurableSingletonClass (Option (CellRefinedType C T))]
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
    (compact : T → C → Set (DyadicUnitCube q))
    (hcompact : ∀ t c, MeasurableSet (compact t c))
    {n : ℕ} (hq : 4 < q) (hn : 0 < n)
    (probe : X → X → ℝ) (hprobe : Measurable (Function.uncurry probe))
    {B : ℝ} (hB : 0 ≤ B) (hb : ∀ᵐ p ∂μ.prod ν, |probe p.1 p.2| ≤ B) :
    let η := restrictOriginalRetainedResidual χ ξ a (⋃ c, cell c)
    let hη := restrictOriginalRetainedResidual_le χ ξ a ha (MeasurableSet.iUnion hcell)
    let coord := fun t (p : X × X) ↦ D.sourceCoordinate t p.1
    let good := D.types.rnCellCompactGoodComponent η hη (fun p ↦ a p.1) coord cell compact
    let bad := D.types.rnCellCompactBadComponent η hη (fun p ↦ a p.1) coord cell compact
    let hsplit := D.types.rn_truncated_compact_split χ ξ a ha cell hcell coord
      (fun t ↦ (D.measurable_sourceCoordinate t).comp measurable_fst) hdisj compact hcompact
    let R := D.types.rnCellRefinedTypes η hη good bad hsplit
    let P := (Measure.pi (fun _ : Fin n ↦ R.sourceMarkedLaw μ)).prod
      (Measure.pi (fun _ : Fin n ↦ R.targetMarkedLaw ν))
    let pressure := fun K tilt sample ↦ D.originalResidualPressureBudget η hη n K probe tilt
      (cellRefinedSubplanObservation sample)
    let count := fun sample ↦ D.originalResidualCountBudget η hη n
      (cellRefinedSubplanObservation sample)
    let actualCost := fun tilt sample i j ↦ (n : ℝ) ^ (2 / (q : ℝ)) *
      cost (sample.1 i).1 (sample.2 j).1 + tilt * probe (sample.1 i).1 (sample.2 j).1
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
      ∀ allowed : C → Finset (Fin n × Fin n), ∀ modelScore : C → Fin n → Fin n → ℝ,
      ∀ coreGood coreBad : OTSelector.PartialMatching n n,
      (∀ e ∈ coreGood.edges, ∃ t,
        (sample.1 e.1).2.bind cellRefinedGoodType = some t ∧
        (sample.2 e.2).2.bind cellRefinedGoodType = some t ∧
        ∃ c, cellRefinedGoodCell a cell (sample.1 e.1) = some c ∧
          cellRefinedGoodCell a cell (sample.2 e.2) = some c) →
      (∀ e ∈ coreBad.edges, ∃ p : C × T,
        (sample.1 e.1).2.bind cellRefinedBadType = some p ∧
          (sample.2 e.2).2.bind cellRefinedBadType = some p) →
      (∀ c e, e ∈ coreGood.edges →
        fineOriginalRetainedCellTag a cell (sample.1 e.1) = some c → e ∈ allowed c) →
      (∀ c e, e ∈ coreBad.edges →
        fineOriginalRetainedCellTag a cell (sample.1 e.1) = some c → e ∈ allowed c) →
      let sourceCell := fun i ↦ fineOriginalRetainedCellTag a cell (sample.1 i)
      let targetCell := fun j ↦ fineOriginalRetainedCellTag a cell (sample.2 j)
      let canonical := fun c ↦ PartialMatching.firstLegalOptimalMatching
        (originalAmbientCellLegalGraph sourceCell targetCell allowed c) (modelScore c)
      ∃ full : Assignment n,
        assignmentCost (actualCost tilt sample) full ≤
          (∑ c, (canonical c).cost (actualCost tilt sample)) + pressure K tilt sample + ((n : ℝ) ^ (2 / (q : ℝ)) * D.globalBound + |tilt| * B) *
            (((∑ t ∈ presentTypeTags T,
              partitionCount (fun i ↦ (sample.1 i).2.bind cellRefinedGoodType) t) - coreGood.card) +
            ((∑ t ∈ presentTypeTags (C × T),
              partitionCount (fun i ↦ (sample.1 i).2.bind cellRefinedBadType) t) - coreBad.card) +
              count sample) := by
  let η := restrictOriginalRetainedResidual χ ξ a (⋃ c, cell c)
  let hη := restrictOriginalRetainedResidual_le χ ξ a ha (MeasurableSet.iUnion hcell)
  let coord := fun t (p : X × X) ↦ D.sourceCoordinate t p.1
  let good := D.types.rnCellCompactGoodComponent η hη (fun p ↦ a p.1) coord cell compact
  let bad := D.types.rnCellCompactBadComponent η hη (fun p ↦ a p.1) coord cell compact
  have hcoord t : Measurable (coord t) := (D.measurable_sourceCoordinate t).comp measurable_fst
  have hsplit := D.types.rn_truncated_compact_split χ ξ a ha cell hcell coord hcoord
    hdisj compact hcompact
  obtain ⟨K, henergy, hcount, hfull⟩ := D.exists_rnCellRefinedTypes_original_full_assignment
    (L := C) η hη good bad hsplit hq hn hπ probe hprobe hB hb
  have hproper := D.rnCellRefinedTypes_iid_some η hη good bad hsplit hπ
    (I := Fin n) (J := Fin n)
  have hpartition := D.original_deterministic_fine_cell_tags_ae χ ξ hπ a ha u
    horder hμA hνA hcal cell hcell good bad hsplit n
  have hlabel : ∀ᵐ p ∂χ + ξ, a p.1 = a p.2 :=
    (original_calibrated_coupling_labels μ ν (χ + ξ) (χ + ξ) hπ le_rfl
      a u horder hμA hνA hcal).mono fun _ h ↦ h.1
  have hbad := D.types.rnCellRefinedTypes_bad_cell_properties (μ := μ) (ν := ν)
    η hη good bad hsplit
    a a ha ha cell hcell hdisj
    (original_rn_compact_bad_joint_cells D.types η hη a ha hlabel coord hcoord
      cell hcell compact hcompact) n
  dsimp only
  refine ⟨K, henergy, hcount, ?_⟩
  filter_upwards [hfull, hproper, hpartition, hbad] with sample hfull hp hpart hbad
  intro tilt allowed modelScore coreGood coreBad hgood hbadCore hgoodLegal hbadLegal
  let sourceCell := fun i ↦ fineOriginalRetainedCellTag a cell (sample.1 i)
  let targetCell := fun j ↦ fineOriginalRetainedCellTag a cell (sample.2 j)
  let canonical := fun c ↦ PartialMatching.firstLegalOptimalMatching
    (originalAmbientCellLegalGraph sourceCell targetCell allowed c) (modelScore c)
  have hdefect := original_good_bad_canonical_cell_source_defect_le
    a a cell sample.1 sample.2 coreGood coreBad hgood hbadCore
    (fun i c t hi ↦ (hbad.1 i c t hi).2) (fun j c t hj ↦ (hbad.2 j c t hj).2)
    hp.1 hpart.1 allowed modelScore hgoodLegal hbadLegal
  have hcanonical : ∀ c e, e ∈ (canonical c).edges →
      sourceCell e.1 = some c ∧ targetCell e.2 = some c :=
    fun c e he ↦ firstLegalOptimalMatching_original_cell_edges
      sourceCell targetCell allowed modelScore c e he
  obtain ⟨full, hbound⟩ := hfull tilt sourceCell targetCell
    hpart.1 hpart.2 canonical hcanonical
  refine ⟨full, hbound.trans ?_⟩
  have hcompletion : 0 ≤ (n : ℝ) ^ (2 / (q : ℝ)) * D.globalBound + |tilt| * B :=
    add_nonneg (mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _) D.bound_nonneg)
      (mul_nonneg (abs_nonneg tilt) hB)
  exact add_le_add le_rfl
    (mul_le_mul_of_nonneg_left (add_le_add hdefect le_rfl) hcompletion)

end OTSelector.Reconstruction.PopulationTypedCostData
