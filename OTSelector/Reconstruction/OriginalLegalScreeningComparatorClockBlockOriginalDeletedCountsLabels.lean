import OTSelector.Reconstruction.OriginalClasswiseOriginalAtomRepairClockBlockGraph

/-! Exact original block-label filters and original embedding cardinalities. -/
open Set Function MeasureTheory
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OTSelector.Reconstruction

/-- Filtering mapped original reserve indices preserves the exact original mark predicate. -/
theorem originalEmbeddedDeletion_filter_card {k m : ℕ} {B : Type*}
    (r : Fin k ↪ Fin m) (D : Finset (Fin k)) (c : Fin m → B) (b : B)
    (p : Fin k → Prop) (hc : ∀ i, c (r i) = b ↔ p i) :
    ((D.map r).filter (fun i ↦ c i = b)).card = (D.filter p).card := by
  classical
  rw [Finset.filter_map,Finset.card_map]
  congr 1
  ext i
  simp only [Finset.mem_filter,Function.comp_apply,hc]

namespace OriginalStageClockGrid
variable (G : OriginalStageClockGrid) {μ ν : Measure ℝ}

/-- Real source-block labels read exactly the original Ico block mark filter. -/
theorem sourceBlockLabel_filter_eq_clock_filter {q m : ℕ}
    (h₀ : G.clockSlabSurplus μ ν 0 = 0) (hN : G.clockSlabSurplus μ ν G.count = 0)
    (x : Fin m → LegalMarkedPhysicalPoint q) (hx : ∀ i, G.sourceLabel (x i).2 < G.count)
    (U : Finset (Fin m)) (block : G.ClockSlabBlock μ ν) :
    U.filter (fun i ↦ G.sourceBlockLabel h₀ hN (x i).2 (hx i) = block) =
      U.filter (fun i ↦ (x i).2 ∈ G.sourceBlockCell μ ν block) := by
  classical
  ext i
  simp only [Finset.mem_filter,G.sourceBlockLabel_eq_iff_mem h₀ hN (x i).2 (hx i) block]

/-- Real target-block labels keep the separate original Ioc block mark filter. -/
theorem targetBlockLabel_filter_eq_clock_filter {q n : ℕ}
    (h₀ : G.clockSlabSurplus μ ν 0 = 0) (hN : G.clockSlabSurplus μ ν G.count = 0)
    (y : Fin n → LegalMarkedPhysicalPoint q) (hy : ∀ j, G.targetLabel (y j).2 < G.count)
    (V : Finset (Fin n)) (block : G.ClockSlabBlock μ ν) :
    V.filter (fun j ↦ G.targetBlockLabel h₀ hN (y j).2 (hy j) = block) =
      V.filter (fun j ↦ (y j).2 ∈ G.targetBlockCell μ ν block) := by
  classical
  ext j
  simp only [Finset.mem_filter,G.targetBlockLabel_eq_iff_mem h₀ hN (y j).2 (hy j) block]
end OriginalStageClockGrid
end OTSelector.Reconstruction
