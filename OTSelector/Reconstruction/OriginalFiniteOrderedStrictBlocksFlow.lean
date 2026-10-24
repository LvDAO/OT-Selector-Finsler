import OTSelector.Reconstruction.OriginalFiniteOrderedStrictBlocksCuts
import OTSelector.Probability.FiniteCellClassFlow

/-! Actual finite forward class flow identifies every tight prefix crossing. -/
open Set Function MeasureTheory
open scoped BigOperators ENNReal
noncomputable section
namespace OTSelector.Reconstruction
set_option maxHeartbeats 600000

/-- Surplus of the unchanged original finite class masses at an integer cut. -/
def finiteClassSurplus {N : ℕ} (a b : Fin N → ℝ) (k : ℕ) : ℝ :=
  finiteClockPrefix a k - finiteClockPrefix b k

/-- An actual forward finite flow conserves prefix mass exactly: the surplus
is the literal sum of all crossing entries, including tight cuts. -/
theorem finiteClassFlow_prefix_balance
    {N : ℕ} (P : Fin N → Fin N → ℝ) (a b : Fin N → ℝ)
    (hrow : ∀ i, ∑ j, P i j = a i) (hcol : ∀ j, ∑ i, P i j = b j)
    (hzero : ∀ i j, ¬ i < j → P i j = 0) (k : ℕ) (hk : k ≤ N) :
    finiteClockPrefix a k = finiteClockPrefix b k +
      ∑ i ∈ Finset.univ.filter (fun i : Fin N ↦ i.val < k),
        ∑ j ∈ Finset.univ.filter (fun j : Fin N ↦ ¬ j.val < k), P i j := by
  classical
  let A := Finset.univ.filter (fun i : Fin N ↦ i.val < k)
  let B := Finset.univ.filter (fun i : Fin N ↦ ¬ i.val < k)
  have hs : finiteClockPrefix a k = ∑ i ∈ A, ∑ j, P i j := by
    rw [finiteClockPrefix_eq_filter a hk]
    simp_rw [hrow]
    rfl
  have ht : finiteClockPrefix b k = ∑ j ∈ A, ∑ i, P i j := by
    rw [finiteClockPrefix_eq_filter b hk]
    simp_rw [hcol]
    rfl
  have hss : (∑ i ∈ A, ∑ j, P i j) =
      (∑ i ∈ A, ∑ j ∈ A, P i j) + (∑ i ∈ A, ∑ j ∈ B, P i j) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    exact (Finset.sum_filter_add_sum_filter_not Finset.univ
      (fun j : Fin N ↦ j.val < k) (P i)).symm
  have htt : (∑ j ∈ A, ∑ i, P i j) =
      (∑ i ∈ A, ∑ j ∈ A, P i j) + (∑ i ∈ B, ∑ j ∈ A, P i j) := by
    calc
      _ = ∑ j ∈ A, ((∑ i ∈ A, P i j) + (∑ i ∈ B, P i j)) := by
        apply Finset.sum_congr rfl
        intro j _
        exact (Finset.sum_filter_add_sum_filter_not Finset.univ
          (fun i : Fin N ↦ i.val < k) (fun i ↦ P i j)).symm
      _ = _ := by rw [Finset.sum_add_distrib]; congr 1 <;> rw [Finset.sum_comm]
  have hin : (∑ i ∈ B, ∑ j ∈ A, P i j) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    apply Finset.sum_eq_zero
    intro j hj
    apply hzero
    have hi' := (Finset.mem_filter.mp hi).2
    have hj' := (Finset.mem_filter.mp hj).2
    simp only [Fin.lt_def]
    omega
  change finiteClockPrefix a k = finiteClockPrefix b k + ∑ i ∈ A, ∑ j ∈ B, P i j
  linarith

/-- Every genuine forward class flow has weakly nonnegative surplus. -/
theorem finiteClassFlow_surplus_nonneg
    {N : ℕ} (P : Fin N → Fin N → ℝ) (a b : Fin N → ℝ)
    (hP : ∀ i j, 0 ≤ P i j)
    (hrow : ∀ i, ∑ j, P i j = a i) (hcol : ∀ j, ∑ i, P i j = b j)
    (hzero : ∀ i j, ¬ i < j → P i j = 0) (k : ℕ) (hk : k ≤ N) :
    0 ≤ finiteClassSurplus a b k := by
  have h := finiteClassFlow_prefix_balance P a b hrow hcol hzero k hk
  have hp : 0 ≤ ∑ i ∈ Finset.univ.filter (fun i : Fin N ↦ i.val < k),
      ∑ j ∈ Finset.univ.filter (fun j : Fin N ↦ ¬ j.val < k), P i j :=
    Finset.sum_nonneg fun i _ ↦ Finset.sum_nonneg fun j _ ↦ hP i j
  dsimp only [finiteClassSurplus]
  linarith

/-- A tight actual prefix cut kills every forward crossing entry of the actual
flow, rather than merely asserting feasibility of some replacement matrix. -/
theorem finiteClassFlow_zero_crossing_of_tight
    {N : ℕ} (P : Fin N → Fin N → ℝ) (a b : Fin N → ℝ)
    (hP : ∀ i j, 0 ≤ P i j)
    (hrow : ∀ i, ∑ j, P i j = a i) (hcol : ∀ j, ∑ i, P i j = b j)
    (hzero : ∀ i j, ¬ i < j → P i j = 0) (k : ℕ) (hk : k ≤ N)
    (htight : finiteClassSurplus a b k = 0)
    (i j : Fin N) (hi : i.val < k) (hj : k ≤ j.val) : P i j = 0 := by
  classical
  have hb := finiteClassFlow_prefix_balance P a b hrow hcol hzero k hk
  have hs : (∑ i ∈ Finset.univ.filter (fun i : Fin N ↦ i.val < k),
      ∑ j ∈ Finset.univ.filter (fun j : Fin N ↦ ¬ j.val < k), P i j) = 0 := by
    dsimp only [finiteClassSurplus] at htight
    linarith
  have hinner : P i j ≤ ∑ j ∈ Finset.univ.filter (fun j : Fin N ↦ ¬ j.val < k), P i j :=
    Finset.single_le_sum (fun j _ ↦ hP i j)
      (Finset.mem_filter.mpr ⟨Finset.mem_univ _, not_lt.mpr hj⟩)
  have houter : (∑ j ∈ Finset.univ.filter (fun j : Fin N ↦ ¬ j.val < k), P i j) ≤
      ∑ i ∈ Finset.univ.filter (fun i : Fin N ↦ i.val < k),
        ∑ j ∈ Finset.univ.filter (fun j : Fin N ↦ ¬ j.val < k), P i j :=
    Finset.single_le_sum (fun i _ ↦ Finset.sum_nonneg fun j _ ↦ hP i j)
      (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩)
  exact le_antisymm (hinner.trans (houter.trans_eq hs)) (hP i j)

/-- The surplus begins and ends at zero for the actual row and column masses. -/
theorem finiteClassFlow_surplus_endpoints
    {N : ℕ} (P : Fin N → Fin N → ℝ) (a b : Fin N → ℝ)
    (hrow : ∀ i, ∑ j, P i j = a i) (hcol : ∀ j, ∑ i, P i j = b j) :
    finiteClassSurplus a b 0 = 0 ∧ finiteClassSurplus a b N = 0 := by
  constructor
  · simp [finiteClassSurplus, finiteClockPrefix_zero]
  · rw [finiteClassSurplus, finiteClockPrefix_total, finiteClockPrefix_total]
    simp_rw [← hrow, ← hcol]
    rw [Finset.sum_comm, sub_self]

/-- The unchanged actual conditional coupling has zero mass in every backward
class rectangle. Nonzero class masses are derived internally when needed. -/
theorem FiniteOrderedMonochromeClasses.actualClassFlow_zero
    {μ ν : Measure ℝ} {δ : ℝ} (C : FiniteOrderedMonochromeClasses μ ν δ) (hδ : 0 < δ)
    (γ : Measure (ℝ × ℝ)) (hγ : Vlasov.IsCoupling γ μ ν)
    (hforward : ∀ᵐ p ∂γ, p.1 ≤ p.2) (i j : Fin C.count) (hij : ¬ i < j) :
    actualClockClassFlow γ C.cell C.cell i j = 0 := by
  have hs : γ (Prod.fst ⁻¹' C.cell i) = μ (C.cell i) :=
    (Measure.map_apply measurable_fst (C.measurable_cell i)).symm.trans
      (congrArg (fun θ : Measure ℝ ↦ θ (C.cell i)) hγ.1)
  have ht : γ (Prod.snd ⁻¹' C.cell j) = ν (C.cell j) :=
    (Measure.map_apply measurable_snd (C.measurable_cell j)).symm.trans
      (congrArg (fun θ : Measure ℝ ↦ θ (C.cell j)) hγ.2)
  have hnull : γ (C.cell i ×ˢ C.cell j) = 0 := by
    by_cases hi : μ (C.cell i) = 0
    · exact measure_mono_null (fun _ hp ↦ hp.1) (hs.trans hi)
    by_cases hj : ν (C.cell j) = 0
    · exact measure_mono_null (fun _ hp ↦ hp.2) (ht.trans hj)
    have hne : i ≠ j := by
      intro heq
      subst j
      exact (C.monochrome i).elim hi hj
    have hji : j < i := lt_of_le_of_ne (le_of_not_gt hij) (Ne.symm hne)
    apply measure_mono_null (fun p hp ↦ ?_) (ae_iff.mp hforward)
    intro ho
    have hg := C.opposite_gap j i hji (Or.inr ⟨hj, hi⟩)
      p.2 (subset_closure hp.2) p.1 (subset_closure hp.1)
    linarith
  simp only [actualClockClassFlow, measureReal_def, hnull, ENNReal.toReal_zero]

/-- The original continuous coupling constructs its actual finite ordered flow
with exact original class masses; no Hall or positive slack hypothesis occurs. -/
theorem FiniteOrderedMonochromeClasses.actualClassFlow_marginals
    {μ ν : Measure ℝ} {δ : ℝ} (C : FiniteOrderedMonochromeClasses μ ν δ)
    (γ : Measure (ℝ × ℝ)) [IsFiniteMeasure γ] (hγ : Vlasov.IsCoupling γ μ ν) :
    (∀ i, ∑ j, actualClockClassFlow γ C.cell C.cell i j = μ.real (C.cell i)) ∧
    (∀ j, ∑ i, actualClockClassFlow γ C.cell C.cell i j = ν.real (C.cell j)) := by
  have hs : ∀ᵐ p ∂γ, p.1 ∈ ⋃ i, C.cell i :=
    ae_of_ae_map measurable_fst.aemeasurable (by rw [hγ.1]; exact C.ae_source_cover)
  have ht : ∀ᵐ p ∂γ, p.2 ∈ ⋃ i, C.cell i :=
    ae_of_ae_map measurable_snd.aemeasurable (by rw [hγ.2]; exact C.ae_target_cover)
  constructor
  · intro i
    rw [actualClockClassFlow_row γ C.cell C.cell C.measurable_cell C.measurable_cell
      C.disjoint ht i, hγ.1]
  · intro j
    rw [actualClockClassFlow_col γ C.cell C.cell C.measurable_cell C.measurable_cell
      C.disjoint hs j, hγ.2]

end OTSelector.Reconstruction
