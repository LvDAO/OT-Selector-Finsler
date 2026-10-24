import OTSelector.Reconstruction.FinslerRelativeLawDeterministicCellTags
import OTSelector.Reconstruction.FinslerRelativeLawOriginalFineFullAssignment
import OTSelector.Reconstruction.FinslerRelativeLawOriginalGoodCellProperties

/-! Literal original deterministic cell labels on the same fine good/bad/residual sample. -/
open Set Function MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators Classical
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

/-- Read the original physical retained cell after forgetting only the fine subdivision. -/
def fineOriginalRetainedCellTag {X Z C T : Type*} [Fintype T] [DecidableEq T]
    (a : X → Z) (cell : C → Set Z) (p : X × Option (CellRefinedType C T)) : Option C :=
  originalRetainedCellTag a cell (PopulationTypedCostData.selectedSubplanTags (T := T))
    (p.1, p.2.map cellRefinedSubplanType)

/-- A retained cell label records literal original physical membership. -/
theorem fineOriginalRetainedCellTag_eq_some_iff {X Z C T : Type*} [Fintype T] [DecidableEq T]
    (a : X → Z) (cell : C → Set Z) (hdisj : Pairwise (Disjoint on cell))
    (p : X × Option (CellRefinedType C T)) (c : C) :
    fineOriginalRetainedCellTag a cell p = some c ↔
      ¬cellRefinedResidualTag p.2 ∧ a p.1 ∈ cell c := by
  rw [fineOriginalRetainedCellTag, originalRetainedCellTag_eq_some_iff a cell hdisj]
  rw [cellRefinedSubplanType_mem_selected_iff]

/-- On a good observed vertex, the full retained cell agrees with its good-only cell. -/
theorem fineOriginalRetainedCellTag_eq_goodCell {X Z C T : Type*} [Fintype T] [DecidableEq T]
    (a : X → Z) (cell : C → Set Z) (p : X × Option (CellRefinedType C T)) {t : T}
    (ht : p.2.bind cellRefinedGoodType = some t) :
    fineOriginalRetainedCellTag a cell p = cellRefinedGoodCell a cell p := by
  have hp := (cellRefinedGoodType_bind_some_iff p.2 t).mp ht
  simp [fineOriginalRetainedCellTag, originalRetainedCellTag,
    PopulationTypedCostData.selectedSubplanTags, cellRefinedGoodCell, hp,
    cellRefinedSubplanType, cellRefinedGoodType]

/-- A bad observed vertex carries its actual original cell, without changing its index. -/
theorem fineOriginalRetainedCellTag_eq_some_of_bad {X Z C T : Type*} [Fintype T] [DecidableEq T]
    (a : X → Z) (cell : C → Set Z) (hdisj : Pairwise (Disjoint on cell))
    (p : X × Option (CellRefinedType C T)) {c : C} {t : T}
    (ht : p.2.bind cellRefinedBadType = some (c, t)) (hc : a p.1 ∈ cell c) :
    fineOriginalRetainedCellTag a cell p = some c := by
  apply (fineOriginalRetainedCellTag_eq_some_iff a cell hdisj p c).mpr
  refine ⟨?_, hc⟩
  have hp := (cellRefinedBadType_bind_some_iff p.2 (c, t)).mp ht
  simp [cellRefinedResidualTag, hp]

/-- Actual deterministic original truncation discharges the fine full-assignment
partition condition. Every original physical point and index stays in the same experiment. -/
theorem PopulationTypedCostData.original_deterministic_fine_cell_tags_ae
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
    (good : T → Measure (X × X)) (bad : C → T → Measure (X × X))
    (hsplit : ∀ t, good t + ∑ c, bad c t =
      (D.types.rnSubplanTypes (restrictOriginalRetainedResidual χ ξ a (⋃ c, cell c))
        (restrictOriginalRetainedResidual_le χ ξ a ha (MeasurableSet.iUnion hcell))).component
          (false, t)) (n : ℕ) :
    let η := restrictOriginalRetainedResidual χ ξ a (⋃ c, cell c)
    let hη := restrictOriginalRetainedResidual_le χ ξ a ha (MeasurableSet.iUnion hcell)
    let R := D.types.rnCellRefinedTypes η hη good bad hsplit
    let P := (Measure.pi (fun _ : Fin n ↦ R.sourceMarkedLaw μ)).prod
      (Measure.pi (fun _ : Fin n ↦ R.targetMarkedLaw ν))
    ∀ᵐ sample ∂P,
      (∀ i, fineOriginalRetainedCellTag a cell (sample.1 i) = none ↔
        cellRefinedResidualTag (sample.1 i).2) ∧
      (∀ j, fineOriginalRetainedCellTag a cell (sample.2 j) = none ↔
        cellRefinedResidualTag (sample.2 j).2) := by
  let η := restrictOriginalRetainedResidual χ ξ a (⋃ c, cell c)
  let hη := restrictOriginalRetainedResidual_le χ ξ a ha (MeasurableSet.iUnion hcell)
  let R := D.types.rnCellRefinedTypes η hη good bad hsplit
  let A := D.refineSubplan η hη
  let P := (Measure.pi (fun _ : Fin n ↦ R.sourceMarkedLaw μ)).prod
    (Measure.pi (fun _ : Fin n ↦ R.targetMarkedLaw ν))
  letI : MeasurableSpace (Option T) := ⊤
  letI : MeasurableSingletonClass (Option T) := ⟨fun _ ↦ trivial⟩
  have hlaw : P.map cellRefinedSubplanObservation = A.markedLaw n :=
    D.types.rnCellRefinedTypes_iid_subplan_law η hη good bad hsplit μ ν
  have hm := measurable_cellRefinedSubplanObservation (X := X) (Y := X) (C := C) (T := T)
    (I := Fin n) (J := Fin n)
  have htags := D.original_deterministic_cell_tags_ae χ ξ hπ a ha u
    horder hμA hνA hcal cell hcell n
  dsimp only at htags
  rw [← hlaw] at htags
  have hf := ae_of_ae_map hm.aemeasurable htags
  dsimp only
  filter_upwards [hf] with sample hsample
  constructor
  · intro i
    exact (hsample.1 i).trans (cellRefinedSubplanType_mem_selected_iff (sample.1 i).2)
  · intro j
    exact (hsample.2 j).trans (cellRefinedSubplanType_mem_selected_iff (sample.2 j).2)

end OTSelector.Reconstruction
