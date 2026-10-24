import OTSelector.Reconstruction.FinslerRelativeLawOriginalCanonicalCellDefect
import OTSelector.Reconstruction.FinslerRelativeLawOriginalFineDeterministicCellTags
import OTSelector.Finite.MeasurableIndexedGraph
import OTSelector.Reconstruction.FinslerRelativeLawOriginalCellOptimizer

/-! The actual canonical optimizer is unchanged by forgetting the fine good/bad subdivision. -/
open Set Function
open scoped BigOperators Classical
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

/-- Original physical legality on the original retained/residual sample. -/
def originalSubplanPhysicalGraph {X C T : Type*} {n : ℕ} (legal : C → X → X → Prop)
    (c : C) (sample : (Fin n → X × Option (Bool × T)) ×
      (Fin n → X × Option (Bool × T))) : Finset (Fin n × Fin n) :=
  Finset.univ.filter (fun e ↦ legal c (sample.1 e.1).1 (sample.2 e.2).1)

/-- The same exact original flags and physical cells characterize a fine retained vertex. -/
theorem fineOriginalRetainedCellTag_eq_some_iff_flag
    {X Z C T : Type*} [Fintype T] [DecidableEq T]
    (a : X → Z) (cell : C → Set Z) (hdisj : Pairwise (Disjoint on cell))
    (p : X × Option (CellRefinedType C T)) (c : C)
    (hproper : ∃ tag, p.2 = some tag) :
    fineOriginalRetainedCellTag a cell p = some c ↔
      subplanRetentionFlag (p.2.map cellRefinedSubplanType) = false ∧ a p.1 ∈ cell c := by
  rw [fineOriginalRetainedCellTag_eq_some_iff a cell hdisj]
  apply and_congr _ Iff.rfl
  obtain ⟨tag, hp⟩ := hproper
  rw [hp]
  rcases tag with ⟨flag,t⟩ | ⟨c,t⟩
  · cases flag <;> simp [cellRefinedResidualTag, cellRefinedSubplanType, subplanRetentionFlag]
  · simp [cellRefinedResidualTag, cellRefinedSubplanType, subplanRetentionFlag]

/-- The entire ambient legal graph equals the old original retained-cell graph
on the same indices. No re-enumeration or optimizer-equivariance premise is used. -/
theorem originalFinePhysicalGraph_subplan_observation
    {X Z C T : Type*} [Fintype T] [DecidableEq T] {n : ℕ}
    (a : X → Z) (cell : C → Set Z) (hdisj : Pairwise (Disjoint on cell))
    (legal : C → X → X → Prop)
    (sample : (Fin n → X × Option (CellRefinedType C T)) ×
      (Fin n → X × Option (CellRefinedType C T))) (c : C)
    (hs : ∀ i, ∃ tag, (sample.1 i).2 = some tag)
    (ht : ∀ j, ∃ tag, (sample.2 j).2 = some tag) :
    originalAmbientCellLegalGraph
      (fun i ↦ fineOriginalRetainedCellTag a cell (sample.1 i))
      (fun j ↦ fineOriginalRetainedCellTag a cell (sample.2 j))
      (originalFinePhysicalGraph legal sample) c =
    originalRetainedCellGraph a cell (originalSubplanPhysicalGraph legal) c
      (cellRefinedSubplanObservation sample) := by
  ext e
  simp only [originalAmbientCellLegalGraph, Finset.mem_filter, originalFinePhysicalGraph,
    originalRetainedCellGraph, originalSubplanPhysicalGraph, Finset.mem_univ, true_and,
    fineOriginalRetainedCellTag_eq_some_iff_flag a cell hdisj _ c (hs _),
    fineOriginalRetainedCellTag_eq_some_iff_flag a cell hdisj _ c (ht _),
    cellRefinedSubplanObservation]
  tauto

/-- Ties are preserved literally: both constructions call the same first legal
optimizer with the same graph and score on the same original index set. -/
theorem original_fine_canonical_eq_subplan_optimizer
    {X Z C T : Type*} [Fintype T] [DecidableEq T] {n : ℕ}
    (a : X → Z) (cell : C → Set Z) (hdisj : Pairwise (Disjoint on cell))
    (legal : C → X → X → Prop) (model : C → X → X → ℝ)
    (sample : (Fin n → X × Option (CellRefinedType C T)) ×
      (Fin n → X × Option (CellRefinedType C T))) (c : C)
    (hs : ∀ i, ∃ tag, (sample.1 i).2 = some tag)
    (ht : ∀ j, ∃ tag, (sample.2 j).2 = some tag) :
    PartialMatching.firstLegalOptimalMatching
      (originalAmbientCellLegalGraph (fun i ↦ fineOriginalRetainedCellTag a cell (sample.1 i))
        (fun j ↦ fineOriginalRetainedCellTag a cell (sample.2 j))
        (originalFinePhysicalGraph legal sample) c)
      (fun i j ↦ model c (sample.1 i).1 (sample.2 j).1) =
    originalRetainedCellOptimizer a cell (originalSubplanPhysicalGraph legal)
      (fun c cloud i j ↦ model c (cloud.1 i).1 (cloud.2 j).1) c
      (cellRefinedSubplanObservation sample) := by
  rw [originalFinePhysicalGraph_subplan_observation a cell hdisj legal sample c hs ht]
  rfl

end OTSelector.Reconstruction
