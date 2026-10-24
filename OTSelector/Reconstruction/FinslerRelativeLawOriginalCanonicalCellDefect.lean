import OTSelector.Finite.MeasurableLegalOptimizer
import OTSelector.Reconstruction.FinslerRelativeLawOriginalFineSourceCounts

/-! Actual canonical legal cell optimizers have no more source defect than retained legal cores. -/
open Set Function
open scoped BigOperators
noncomputable section
namespace OTSelector.Reconstruction

/-- A cell's actual legal graph keeps the original global sample indices. -/
def originalAmbientCellLegalGraph {C : Type*} {m n : ℕ}
    (sourceCell : Fin m → Option C) (targetCell : Fin n → Option C)
    (allowed : C → Finset (Fin m × Fin n)) (c : C) : Finset (Fin m × Fin n) := by
  classical
  exact (allowed c).filter fun e ↦ sourceCell e.1 = some c ∧ targetCell e.2 = some c

/-- Every edge of the actual canonical optimizer lies in its literal physical cell. -/
theorem firstLegalOptimalMatching_original_cell_edges {C : Type*} {m n : ℕ}
    (sourceCell : Fin m → Option C) (targetCell : Fin n → Option C)
    (allowed : C → Finset (Fin m × Fin n)) (score : C → Fin m → Fin n → ℝ)
    (c : C) (e : Fin m × Fin n)
    (he : e ∈ (PartialMatching.firstLegalOptimalMatching
      (originalAmbientCellLegalGraph sourceCell targetCell allowed c) (score c)).edges) :
    sourceCell e.1 = some c ∧ targetCell e.2 = some c := by
  classical
  have hlegal := (PartialMatching.firstLegalOptimalMatching_isLegalOptimal
    (originalAmbientCellLegalGraph sourceCell targetCell allowed c) (score c)).1
  exact (Finset.mem_filter.mp (hlegal he)).2

/-- Canonical legal optimization discharges the cardinality comparison with any
actual retained core, on the same ambient original indices. -/
theorem sum_firstLegalOptimalMatching_source_defect_le
    {C : Type*} [Fintype C] {m n : ℕ}
    (allowed : C → Finset (Fin m × Fin n)) (score : C → Fin m → Fin n → ℝ)
    (sourceCell : Fin m → Option C) (core : C → OTSelector.PartialMatching m n)
    (hlegal : ∀ c, PartialMatching.IsLegal (allowed c) (core c)) :
    (∑ c, (partitionCount sourceCell (some c) -
      ((PartialMatching.firstLegalOptimalMatching (allowed c) (score c)).card : ℝ))) ≤
        ∑ c, (partitionCount sourceCell (some c) - ((core c).card : ℝ)) := by
  apply Finset.sum_le_sum
  intro c _
  apply sub_le_sub_left
  have hcard : (core c).card ≤
      (PartialMatching.firstLegalOptimalMatching (allowed c) (score c)).card := by
    rw [(PartialMatching.firstLegalOptimalMatching_isLegalOptimal (allowed c) (score c)).2.1]
    exact PartialMatching.card_le_legalMaximumCard (hlegal c)
  exact_mod_cast hcard

/-- The exact optimizer defects inherit an existing one-budget source-defect
bound without a separate maximum-cardinality or canonical-selection premise. -/
theorem sum_firstLegalOptimalMatching_source_defect_le_budget
    {C : Type*} [Fintype C] {m n : ℕ}
    (allowed : C → Finset (Fin m × Fin n)) (score : C → Fin m → Fin n → ℝ)
    (sourceCell : Fin m → Option C) (core : C → OTSelector.PartialMatching m n)
    (hlegal : ∀ c, PartialMatching.IsLegal (allowed c) (core c))
    {budget : ℝ}
    (hbudget : (∑ c, (partitionCount sourceCell (some c) - ((core c).card : ℝ))) ≤ budget) :
    (∑ c, (partitionCount sourceCell (some c) -
      ((PartialMatching.firstLegalOptimalMatching (allowed c) (score c)).card : ℝ))) ≤ budget :=
  (sum_firstLegalOptimalMatching_source_defect_le allowed score sourceCell core hlegal).trans hbudget

/-- Filtering the exact legal graph to the actual cell removes the canonical
retained-support and cardinality premises together. Any actual same-cell legal
core supplies the full source-defect bound for this canonical family. -/
theorem sum_original_cell_firstLegalOptimalMatching_defect_le
    {C : Type*} [Fintype C] {m n : ℕ}
    (sourceCell : Fin m → Option C) (targetCell : Fin n → Option C)
    (allowed : C → Finset (Fin m × Fin n)) (score : C → Fin m → Fin n → ℝ)
    (core : C → OTSelector.PartialMatching m n)
    (hcell : ∀ c e, e ∈ (core c).edges →
      sourceCell e.1 = some c ∧ targetCell e.2 = some c)
    (hlegal : ∀ c, PartialMatching.IsLegal (allowed c) (core c))
    {budget : ℝ}
    (hbudget : (∑ c, (partitionCount sourceCell (some c) - ((core c).card : ℝ))) ≤ budget) :
    (∑ c, (partitionCount sourceCell (some c) -
      ((PartialMatching.firstLegalOptimalMatching
        (originalAmbientCellLegalGraph sourceCell targetCell allowed c) (score c)).card : ℝ))) ≤
          budget := by
  classical
  apply sum_firstLegalOptimalMatching_source_defect_le_budget _ score sourceCell core _ hbudget
  intro c e he
  exact Finset.mem_filter.mpr ⟨hlegal c he, hcell c e he⟩

end OTSelector.Reconstruction
