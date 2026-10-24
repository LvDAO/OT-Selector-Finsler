import OTSelector.Reconstruction.FinslerConcreteUpperForwardSubplanCore
import OTSelector.Reconstruction.FinslerConcreteUpperCompactTypeColors
import OTSelector.Finite.CompactDyadicColors

/-! One original hierarchy supplies all retained cell cores. Fixed-depth type
histograms pay the deleted cross-cell edges, while the sum of core energies is
charged only once to the original attributed physical energy. -/
open Set Function MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators Classical
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
set_option linter.unusedSectionVars false

/-- Summing a literal fine histogram over its spatial cells recovers the
unchanged original type count. -/
theorem sum_partitionCount_fine_cells {T A : Type*} [Fintype A]
    [DecidableEq T] [DecidableEq A] {n : ℕ}
    (tag : Fin n → T) (cell : Fin n → A) (t : T) :
    (∑ a, partitionCount (fun i ↦ (tag i, cell i)) (t, a)) = partitionCount tag t := by
  unfold partitionCount
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  by_cases ht : tag i = t <;> simp [partitionIndicator, ht]

/-- A fixed positive dyadic level of the SAME original hierarchy yields one
partial core internal to every retained color. Its energy uses only the original
type budget; its genuine source deficiency uses the fixed-level histograms. -/
theorem exists_hierarchy_same_cell_core
    {T C : Type*} [Fintype T] [Fintype C] [DecidableEq T] [DecidableEq C]
    {q n k K : ℕ} (hk : 0 < k) (hkK : k ≤ K)
    (S : Finset T) (x y : Fin n → T × DyadicUnitCube q)
    (full : Assignment n) (hfull : OptimalAssignment (taggedHierarchyCost K x y) full)
    (sourceCell targetCell : Fin n → Option C)
    (hsource : ∀ i, (x i).1 ∈ S → ∃ c, sourceCell i = some c)
    (htarget : ∀ j, (y j).1 ∈ S → ∃ c, targetCell j = some c)
    (hseparate : ∀ i j c c', sourceCell i = some c → targetCell j = some c' →
      (x i).1 = (y j).1 → dyadicCubeCell k (x i).2 = dyadicCubeCell k (y j).2 → c = c')
    (cost : Fin n → Fin n → ℝ) (hcost : ∀ i j, 0 ≤ cost i j) :
    ∃ core : OTSelector.PartialMatching n n,
      (∀ e ∈ core.edges, (x e.1).1 ∈ S ∧ (x e.1).1 = (y e.2).1 ∧
        ∃ c, sourceCell e.1 = some c ∧ targetCell e.2 = some c) ∧
      core.cost cost ≤ attributedTypesEnergy S x y cost full ∧
      (∑ t ∈ S, partitionCount (fun i ↦ (x i).1) t) - (core.card : ℝ) ≤
        ∑ t ∈ S, taggedDyadicDiscrepancy t k x y := by
  classical
  let Fine := T × (Fin q → Fin (2 ^ k + 1))
  let fineS : Finset Fine := Finset.univ.filter (fun p ↦ p.1 ∈ S)
  let xf : Fin n → Fine := fun i ↦ ((x i).1, dyadicCubeCell k (x i).2)
  let yf : Fin n → Fine := fun j ↦ ((y j).1, dyadicCubeCell k (y j).2)
  let core := selectedSameTypeMatching fineS xf yf full
  have hsat : ∀ i j, xf i = yf (full j) → xf i ≠ yf (full i) → xf j = yf (full j) :=
    taggedHierarchy_cell_no_opposite hk hkK x y hfull
  refine ⟨core, ?_, ?_, ?_⟩
  · intro e he
    obtain ⟨hs, ht, heq⟩ := selectedSameTypeMatching_mem fineS xf yf full he
    have hxs : (x e.1).1 ∈ S := (Finset.mem_filter.mp hs).2
    have hyt : (y e.2).1 ∈ S := (Finset.mem_filter.mp ht).2
    have htype : (x e.1).1 = (y e.2).1 := congrArg (fun z : Fine ↦ z.1) heq
    have hcell : dyadicCubeCell k (x e.1).2 = dyadicCubeCell k (y e.2).2 := congrArg (fun z : Fine ↦ z.2) heq
    obtain ⟨c, hc⟩ := hsource e.1 hxs
    obtain ⟨c', hc'⟩ := htarget e.2 hyt
    have hcc := hseparate e.1 e.2 c c' hc hc' htype hcell
    exact ⟨hxs, htype, c, hc, hcc ▸ hc'⟩
  · have hrefine (i) (h : xf i ∈ fineS ∧ xf i = yf (full i)) :
        (x i).1 ∈ S ∧ (x i).1 = (y (full i)).1 :=
      ⟨(Finset.mem_filter.mp h.1).2, congrArg (fun z : Fine ↦ z.1) h.2⟩
    have hle : core.cost cost ≤
        (selectedSameTypeMatching S (fun i ↦ (x i).1) (fun j ↦ (y j).1) full).cost cost := by
      rw [cost_selectedSameTypeMatching, cost_selectedSameTypeMatching]
      apply Finset.sum_le_sum
      intro i _
      by_cases hf : xf i ∈ fineS ∧ xf i = yf (full i)
      · rw [ite_eq_left hf, ite_eq_left (hrefine i hf)]
      · rw [ite_eq_right hf]
        split_ifs
        · exact hcost i (full i)
        · rfl
    exact hle.trans (selectedSameTypeMatching_cost_le_attributed S x y full cost hcost)
  · have h := selectedSameTypeMatching_source_defect_le fineS xf yf full hsat
    have hsum (F : Fine → ℝ) : (∑ p ∈ fineS, F p) = ∑ t ∈ S, ∑ a, F (t, a) := by
      rw [show fineS = Finset.univ.filter (fun p : T × (Fin q → Fin (2 ^ k + 1)) ↦ p.1 ∈ S) from rfl,
        Finset.sum_filter]
      change (∑ p : T × (Fin q → Fin (2 ^ k + 1)), if p.1 ∈ S then F p else 0) = _
      rw [Fintype.sum_prod_type]
      change (∑ t : T, ∑ a : Fin q → Fin (2 ^ k + 1), if t ∈ S then F (t, a) else 0) = _
      have hi (t : T) : (∑ a : Fin q → Fin (2 ^ k + 1), if t ∈ S then F (t, a) else 0) =
          if t ∈ S then ∑ a, F (t, a) else 0 := by
        by_cases ht : t ∈ S <;> simp [ht]
      simp_rw [hi]
      exact Finset.sum_ite_mem_eq S (fun t ↦ ∑ a, F (t, a))
    rw [hsum, hsum] at h
    simp_rw [show ∀ t, (∑ a, partitionCount xf (t, a)) =
        partitionCount (fun i ↦ (x i).1) t from fun t ↦
          sum_partitionCount_fine_cells (fun i ↦ (x i).1) (fun i ↦ dyadicCubeCell k (x i).2) t] at h
    exact h

end OTSelector.Reconstruction
