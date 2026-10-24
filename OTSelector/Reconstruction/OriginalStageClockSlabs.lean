import OTSelector.Reconstruction.OriginalFiniteOrderedMonochromeClassesGap
import Mathlib.Order.Interval.Set.Union

/-! Actual finite clock thresholds with the source Ico / target Ioc convention. -/
open Set Function MeasureTheory
open scoped BigOperators ENNReal
noncomputable section
namespace OTSelector.Reconstruction

/-- A finite increasing clock grid. Source and target cells use their actual distinct
half-open lifetime conventions; no assertion about absence of atoms is imposed. -/
structure OriginalStageClockGrid where
  count : ℕ
  cut : ℕ → ℝ
  strictMono : StrictMono cut

namespace OriginalStageClockGrid
variable (G : OriginalStageClockGrid)

def sourceCell (i : Fin G.count) : Set ℝ := Ico (G.cut i) (G.cut (i + 1))
def targetCell (i : Fin G.count) : Set ℝ := Ioc (G.cut i) (G.cut (i + 1))

theorem source_union : (⋃ i, G.sourceCell i) = Ico (G.cut 0) (G.cut G.count) := by
  apply Subset.antisymm
  · intro x hx
    obtain ⟨i, hi⟩ := mem_iUnion.mp hx
    exact ⟨(G.strictMono.monotone (Nat.zero_le _)).trans hi.1,
      hi.2.trans_le (G.strictMono.monotone (Nat.succ_le_of_lt i.isLt))⟩
  · intro x hx
    obtain ⟨i, hi⟩ := mem_iUnion.mp (Ico_subset_biUnion_Ico G.count G.cut hx)
    obtain ⟨hiN, hix⟩ := mem_iUnion.mp hi
    exact mem_iUnion.mpr ⟨⟨i, Finset.mem_range.mp hiN⟩, hix⟩

theorem target_union : (⋃ i, G.targetCell i) = Ioc (G.cut 0) (G.cut G.count) := by
  apply Subset.antisymm
  · intro x hx
    obtain ⟨i, hi⟩ := mem_iUnion.mp hx
    exact ⟨(G.strictMono.monotone (Nat.zero_le _)).trans_lt hi.1,
      hi.2.trans (G.strictMono.monotone (Nat.succ_le_of_lt i.isLt))⟩
  · intro x hx
    obtain ⟨i, hi⟩ := mem_iUnion.mp (Ioc_subset_biUnion_Ioc G.count G.cut hx)
    obtain ⟨hiN, hix⟩ := mem_iUnion.mp hi
    exact mem_iUnion.mpr ⟨⟨i, Finset.mem_range.mp hiN⟩, hix⟩

theorem source_disjoint : Pairwise (fun i j ↦ Disjoint (G.sourceCell i) (G.sourceCell j)) := by
  intro i j hij
  apply Set.disjoint_left.mpr
  intro x hxi hxj
  rcases lt_or_gt_of_ne hij with h | h
  · have ho := G.strictMono.monotone (Nat.succ_le_of_lt h)
    exact (not_lt_of_ge (ho.trans hxj.1)) hxi.2
  · have ho := G.strictMono.monotone (Nat.succ_le_of_lt h)
    exact (not_lt_of_ge (ho.trans hxi.1)) hxj.2

theorem target_disjoint : Pairwise (fun i j ↦ Disjoint (G.targetCell i) (G.targetCell j)) := by
  intro i j hij
  apply Set.disjoint_left.mpr
  intro x hxi hxj
  rcases lt_or_gt_of_ne hij with h | h
  · have ho := G.strictMono.monotone (Nat.succ_le_of_lt h)
    exact (not_lt_of_ge (hxi.2.trans ho)) hxj.1
  · have ho := G.strictMono.monotone (Nat.succ_le_of_lt h)
    exact (not_lt_of_ge (hxj.2.trans ho)) hxi.1

/-- Actual threshold slabs reconstruct each original clock law exactly. -/
theorem sum_restrict (μ ν : Measure ℝ)
    (hμ : ∀ᵐ x ∂μ, x ∈ Ico (G.cut 0) (G.cut G.count))
    (hν : ∀ᵐ x ∂ν, x ∈ Ioc (G.cut 0) (G.cut G.count)) :
    (∑ i, μ.restrict (G.sourceCell i)) = μ ∧
      (∑ i, ν.restrict (G.targetCell i)) = ν := by
  constructor
  · rw [← Measure.sum_fintype, ← Measure.restrict_iUnion G.source_disjoint
      (fun _ ↦ measurableSet_Ico), G.source_union, Measure.restrict_eq_self_of_ae_mem hμ]
  · rw [← Measure.sum_fintype, ← Measure.restrict_iUnion G.target_disjoint
      (fun _ ↦ measurableSet_Ioc), G.target_union, Measure.restrict_eq_self_of_ae_mem hν]

/-- An earlier actual source slab and later actual target slab preserve the literal strict
clock order, including their distinct endpoint conventions. -/
theorem source_lt_target {i j : Fin G.count} (hij : i < j)
    {a b : ℝ} (ha : a ∈ G.sourceCell i) (hb : b ∈ G.targetCell j) : a < b := by
  exact ha.2.trans_le ((G.strictMono.monotone (Nat.succ_le_of_lt hij)).trans hb.1.le)

end OriginalStageClockGrid
end OTSelector.Reconstruction
