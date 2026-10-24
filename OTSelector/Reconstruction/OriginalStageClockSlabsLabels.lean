import OTSelector.Reconstruction.OriginalStageClockSlabsProducer
import OTSelector.Reconstruction.OriginalStageResidualDensityReserveCounts

/-! Actual original mark labels identify the literal analytic half-open slabs. -/
open Set Function MeasureTheory
open scoped BigOperators Classical
noncomputable section
namespace OTSelector.Reconstruction

/-- Original clock-cell membership supplies a finite stage label. The out-of-window value
is exactly count; it never denotes an admissible stage. This depends only on the mark. -/
def originalFiniteClockCellLabel {n : ℕ} (cell : Fin n → Set ℝ) (a : ℝ) : ℕ :=
  if h : ∃ i, a ∈ cell i then (Classical.choose h).val else n

/-- Disjoint original clock cells make the mark label exactly equivalent to actual cell
membership, including at atoms on stage thresholds. -/
theorem originalFiniteClockCellLabel_eq_iff {n : ℕ} (cell : Fin n → Set ℝ)
    (hd : Pairwise (fun i j ↦ Disjoint (cell i) (cell j))) (a : ℝ) (i : Fin n) :
    originalFiniteClockCellLabel cell a = i.val ↔ a ∈ cell i := by
  unfold originalFiniteClockCellLabel
  split_ifs with h
  · have hc := Classical.choose_spec h
    constructor
    · intro he
      have he' : Classical.choose h = i := Fin.ext he
      rwa [he'] at hc
    · intro hi
      have he : Classical.choose h = i := by
        by_contra hne
        exact Set.disjoint_left.mp (hd hne) hc hi
      exact congrArg Fin.val he
  · constructor
    · intro he
      exact False.elim ((Nat.ne_of_lt i.isLt) he.symm)
    · intro hi
      exact False.elim (h ⟨i, hi⟩)

namespace OriginalStageClockGrid
variable (G : OriginalStageClockGrid)

def sourceLabel (a : ℝ) : ℕ := originalFiniteClockCellLabel G.sourceCell a
def targetLabel (a : ℝ) : ℕ := originalFiniteClockCellLabel G.targetCell a

theorem sourceLabel_eq_iff (a : ℝ) (i : Fin G.count) :
    G.sourceLabel a = i.val ↔ a ∈ G.sourceCell i :=
  originalFiniteClockCellLabel_eq_iff G.sourceCell G.source_disjoint a i

theorem targetLabel_eq_iff (a : ℝ) (i : Fin G.count) :
    G.targetLabel a = i.val ↔ a ∈ G.targetCell i :=
  originalFiniteClockCellLabel_eq_iff G.targetCell G.target_disjoint a i

theorem sourceLabel_lt_count {a : ℝ} (ha : a ∈ Ico (G.cut 0) (G.cut G.count)) :
    G.sourceLabel a < G.count := by
  rw [← G.source_union] at ha
  obtain ⟨i, hi⟩ := mem_iUnion.mp ha
  rw [(G.sourceLabel_eq_iff a i).mpr hi]
  exact i.isLt

theorem targetLabel_lt_count {a : ℝ} (ha : a ∈ Ioc (G.cut 0) (G.cut G.count)) :
    G.targetLabel a < G.count := by
  rw [← G.target_union] at ha
  obtain ⟨i, hi⟩ := mem_iUnion.mp ha
  rw [(G.targetLabel_eq_iff a i).mpr hi]
  exact i.isLt

/-- Class-label order implies strict order of the same original physical clock marks. -/
theorem clock_lt_of_labels {a b : ℝ} (ha : G.sourceLabel a < G.count)
    (hb : G.targetLabel b < G.count) (hab : G.sourceLabel a < G.targetLabel b) : a < b :=
  G.source_lt_target hab ((G.sourceLabel_eq_iff a ⟨_, ha⟩).mp rfl)
    ((G.targetLabel_eq_iff b ⟨_, hb⟩).mp rfl)

/-- The source reserve count labelled by a real stage is literally the count in the actual
analytic Ico slab, on the same original reserve array and kept finite indices. -/
theorem sourceReserveClassCount_eq {q : ℕ} (z : OTSelector.Probability.MarkedCloudSpace q ℝ)
    (kept : Finset (Fin z.1)) (i : Fin G.count) :
    (kept.filter (fun j : Fin z.1 ↦ G.sourceLabel (z.2 j).2 = i.val)).card =
      originalStageRemainingReserveClassCount z kept (Ico (G.cut i) (G.cut (i + 1))) := by
  congr 1
  ext j
  simp only [Finset.mem_filter]
  exact and_congr_right (fun _ ↦ G.sourceLabel_eq_iff (z.2 j).2 i)

/-- The target reserve class is exactly the original Ioc stage count. -/
theorem targetReserveClassCount_eq {q : ℕ} (z : OTSelector.Probability.MarkedCloudSpace q ℝ)
    (kept : Finset (Fin z.1)) (i : Fin G.count) :
    (kept.filter (fun j : Fin z.1 ↦ G.targetLabel (z.2 j).2 = i.val)).card =
      originalStageRemainingReserveClassCount z kept (Ioc (G.cut i) (G.cut (i + 1))) := by
  congr 1
  ext j
  simp only [Finset.mem_filter]
  exact and_congr_right (fun _ ↦ G.targetLabel_eq_iff (z.2 j).2 i)

end OriginalStageClockGrid
end OTSelector.Reconstruction
