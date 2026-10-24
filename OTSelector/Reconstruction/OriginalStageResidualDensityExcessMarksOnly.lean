import OTSelector.Reconstruction.OriginalStageResidualDensityExcessCountEvent

/-! Excess selection is invariant under arbitrary changes to all spatial coordinates. -/
open Set Function
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability

/-- Change only original spatial coordinates, retaining the original count, array indices and marks. -/
def originalStageReplaceCloudPositions {q : ℕ} (z : MarkedCloudSpace q ℝ)
    (positions : ℕ → (Fin q → ℝ)) : MarkedCloudSpace q ℝ :=
  ⟨z.1, fun i ↦ (positions i, (z.2 i).2)⟩

namespace OriginalStageExcessRemovalData
variable (A : OriginalStageExcessRemovalData q)

/-- Replace all four original arrays' spatial coordinates while preserving every count,
original array index, clock mark and selected extreme class. -/
def replacePositions (sourceMain targetMain sourceReserve targetReserve : ℕ → (Fin q → ℝ)) :
    OriginalStageExcessRemovalData q :=
  ⟨originalStageReplaceCloudPositions A.sourceMain sourceMain,
    originalStageReplaceCloudPositions A.targetMain targetMain,
    originalStageReplaceCloudPositions A.sourceReserve sourceReserve,
    originalStageReplaceCloudPositions A.targetReserve targetReserve, A.firstClass, A.lastClass⟩

/-- Literal deletion sets, surviving original Fin indices, capacity and count-good event are
unchanged under arbitrary spatial replacement. Thus no position is inspected by the selection. -/
theorem replacePositions_selection_eq
    (sourceMain targetMain sourceReserve targetReserve : ℕ → (Fin q → ℝ))
    (a : ℝ) (properCuts : Set ℝ) :
    (A.replacePositions sourceMain targetMain sourceReserve targetReserve).sourceDeleted = A.sourceDeleted ∧
    (A.replacePositions sourceMain targetMain sourceReserve targetReserve).targetDeleted = A.targetDeleted ∧
    (A.replacePositions sourceMain targetMain sourceReserve targetReserve).sourceKept = A.sourceKept ∧
    (A.replacePositions sourceMain targetMain sourceReserve targetReserve).targetKept = A.targetKept ∧
    ((A.replacePositions sourceMain targetMain sourceReserve targetReserve).hasCapacity ↔ A.hasCapacity) ∧
    ((A.replacePositions sourceMain targetMain sourceReserve targetReserve).countGood a properCuts ↔
      A.countGood a properCuts) := by
  exact ⟨rfl, rfl, rfl, rfl, Iff.rfl, Iff.rfl⟩

end OriginalStageExcessRemovalData
end OTSelector.Reconstruction
