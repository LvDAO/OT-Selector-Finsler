import OTSelector.Reconstruction.OriginalClasswiseOriginalAtomRepairClockBlockGraph

/-! Empty actual zero-block original arrays have their genuine empty legal bijection. -/
open Set Function MeasureTheory
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OTSelector.Reconstruction.OriginalStageClockGrid
variable (G : OriginalStageClockGrid) {μ ν : Measure ℝ}

/-- The genuine source and target block labels read the same empty original mark
filters. Their actual subtypes are empty and the resulting legal bijection needs no floor. -/
theorem zeroBlock_unused_labels_empty_equiv {q m n : ℕ}
    (h₀ : G.clockSlabSurplus μ ν 0 = 0) (hN : G.clockSlabSurplus μ ν G.count = 0)
    (x : Fin m → LegalMarkedPhysicalPoint q) (y : Fin n → LegalMarkedPhysicalPoint q)
    (hx : ∀ i, G.sourceLabel (x i).2 < G.count) (hy : ∀ j, G.targetLabel (y j).2 < G.count)
    (U : Finset (Fin m)) (V : Finset (Fin n)) (block : G.ClockSlabBlock μ ν)
    (hU : U.filter (fun i ↦ (x i).2 ∈ G.sourceBlockCell μ ν block) = ∅)
    (hV : V.filter (fun j ↦ (y j).2 ∈ G.targetBlockCell μ ν block) = ∅) :
    let Ub := U.filter (fun i ↦ G.sourceBlockLabel h₀ hN (x i).2 (hx i) = block)
    let Vb := V.filter (fun j ↦ G.targetBlockLabel h₀ hN (y j).2 (hy j) = block)
    Ub = ∅ ∧ Vb = ∅ ∧ IsEmpty Ub ∧ IsEmpty Vb ∧
      ∃ e : Ub ≃ Vb, ∀ i : Ub, (x i.val).2 < (y (e i).val).2 := by
  classical
  dsimp only
  let Ub := U.filter (fun i ↦ G.sourceBlockLabel h₀ hN (x i).2 (hx i) = block)
  let Vb := V.filter (fun j ↦ G.targetBlockLabel h₀ hN (y j).2 (hy j) = block)
  have hUb : Ub = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro i hi
    obtain ⟨hi,hb⟩ := Finset.mem_filter.mp hi
    have hh : i ∈ U.filter (fun i ↦ (x i).2 ∈ G.sourceBlockCell μ ν block) :=
      Finset.mem_filter.mpr ⟨hi,(G.sourceBlockLabel_eq_iff_mem h₀ hN (x i).2 (hx i) block).mp hb⟩
    rw [hU] at hh
    exact Finset.notMem_empty i hh
  have hVb : Vb = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro j hj
    obtain ⟨hj,hb⟩ := Finset.mem_filter.mp hj
    have hh : j ∈ V.filter (fun j ↦ (y j).2 ∈ G.targetBlockCell μ ν block) :=
      Finset.mem_filter.mpr ⟨hj,(G.targetBlockLabel_eq_iff_mem h₀ hN (y j).2 (hy j) block).mp hb⟩
    rw [hV] at hh
    exact Finset.notMem_empty j hh
  have : IsEmpty Ub := Finset.isEmpty_coe_sort.mpr hUb
  have : IsEmpty Vb := Finset.isEmpty_coe_sort.mpr hVb
  exact ⟨hUb,hVb,inferInstance,inferInstance,Equiv.equivOfIsEmpty _ _,fun i ↦ isEmptyElim i⟩

end OTSelector.Reconstruction.OriginalStageClockGrid
