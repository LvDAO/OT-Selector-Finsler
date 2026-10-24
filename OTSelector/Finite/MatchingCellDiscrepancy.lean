import OTSelector.Finite.PartialMatching
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Reconstruction.FinslerRelativeLawOrphanDiscrepancy.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Reconstruction.FinslerRelativeLawOrphanDiscrepancy`; the selected original proof blocks follow. -/
section

/-!
# Reconstruction.FinslerRelativeLawOrphanDiscrepancy

**Conditions:** An arbitrary original finite partial matching and finite cell labels; the matching may have been selected adaptively.

**Objects:** Unused endpoint imbalance and the divergence of retained edges.

**Proof detail:** Subtract used-row and used-column sums from the original full sums, transfer them to edges using endpoint injectivity, and sum the cell indicators; each cross-cell edge contributes to at most two discrepancies.

**Sources:** [Reinhard Diestel, Graph Theory, 4th electronic edition (2010), corrected reprint 2012](https://diestel-graph-theory.com/Sample.pdf#page=2), Chapter 2 opening matching definition and Section 2.1, first three chapter pages; [Terence Tao, Analysis I](https://github.com/teorth/analysis/blob/main/Analysis/Section_7_1.lean), Sections 4.3 (absolute value) and 7.1 (finite series), in particular Proposition 7.1.11; [OTSelector project, Original strict-screen residual slack and repair](main.tex#strict-screen-residual-slack), main.tex label strict-screen-residual-slack, line 6749.

Source relation (corollary): The cited sections provide the stated mathematical foundations; the exact finite construction and quantitative bound in this module are local consequences, not a claim that the book states the Lean theorem verbatim.
-/

/-!
The unused endpoint counts are the original counts minus the divergence of the
retained matching. This identity is pathwise and permits arbitrary adaptive
selection of the retained matching.
-/

open scoped BigOperators
noncomputable section
namespace OTSelector.PartialMatching

variable {m n : ℕ}

/-- Original color imbalance and retained-edge flux account for every orphan,
without assigning a new law to the selected endpoint clouds. -/
theorem free_vertex_sum_sub_eq_original_sub_edge_divergence
    (σ : PartialMatching m n) (f : Fin m → ℝ) (g : Fin n → ℝ) :
    (∑ i ∈ σ.freeRows, f i) - (∑ j ∈ σ.freeCols, g j) =
      (∑ i, f i) - (∑ j, g j) - ∑ e ∈ σ.edges, (f e.1 - g e.2) := by
  classical
  have hs : (∑ i ∈ σ.rows, f i) = ∑ e ∈ σ.edges, f e.1 := by
    unfold rows
    rw [Finset.sum_image]
    exact fun e he e' he' h ↦ σ.row_inj e he e' he' h
  have ht : (∑ j ∈ σ.cols, g j) = ∑ e ∈ σ.edges, g e.2 := by
    unfold cols
    rw [Finset.sum_image]
    exact fun e he e' he' h ↦ σ.col_inj e he e' he' h
  have hfullS := Finset.sum_sdiff (Finset.subset_univ σ.rows) (f := f)
  have hfullT := Finset.sum_sdiff (Finset.subset_univ σ.cols) (f := g)
  change (∑ i ∈ σ.freeRows, f i) + (∑ i ∈ σ.rows, f i) = ∑ i, f i at hfullS
  change (∑ j ∈ σ.freeCols, g j) + (∑ j ∈ σ.cols, g j) = ∑ j, g j at hfullT
  rw [hs] at hfullS
  rw [ht] at hfullT
  rw [Finset.sum_sub_distrib]
  linarith

/-- A cell's selected-orphan imbalance is at most the original cell imbalance
plus the retained matching's edges crossing that cell boundary. -/
theorem abs_free_cell_imbalance_le_original_add_crossings
    {C : Type*} [DecidableEq C] (σ : PartialMatching m n)
    (a : Fin m → C) (b : Fin n → C) (c : C) :
    |(∑ i ∈ σ.freeRows, if a i = c then (1 : ℝ) else 0) -
      (∑ j ∈ σ.freeCols, if b j = c then (1 : ℝ) else 0)| ≤
      |(∑ i, if a i = c then (1 : ℝ) else 0) -
        (∑ j, if b j = c then (1 : ℝ) else 0)| +
      ∑ e ∈ σ.edges,
        if (a e.1 = c ∧ b e.2 ≠ c) ∨ (a e.1 ≠ c ∧ b e.2 = c) then (1 : ℝ) else 0 := by
  rw [free_vertex_sum_sub_eq_original_sub_edge_divergence]
  apply (abs_sub _ _).trans
  apply add_le_add_right
  calc |∑ e ∈ σ.edges,
        ((if a e.1 = c then (1 : ℝ) else 0) - (if b e.2 = c then (1 : ℝ) else 0))|
      ≤ ∑ e ∈ σ.edges,
        |(if a e.1 = c then (1 : ℝ) else 0) - (if b e.2 = c then (1 : ℝ) else 0)| :=
          Finset.abs_sum_le_sum_abs _ _
    _ = _ := by
      apply Finset.sum_congr rfl
      intro e he
      by_cases hs : a e.1 = c <;> by_cases ht : b e.2 = c <;> simp [hs, ht]

/-- Total selected-orphan cell discrepancy is bounded by the original
histogram discrepancy and twice the number of retained cross-cell edges. -/
theorem sum_abs_free_cell_imbalance_le_original_add_crossings
    {C : Type*} [Fintype C] [DecidableEq C] (σ : PartialMatching m n)
    (a : Fin m → C) (b : Fin n → C) :
    (∑ c, |(∑ i ∈ σ.freeRows, if a i = c then (1 : ℝ) else 0) -
      (∑ j ∈ σ.freeCols, if b j = c then (1 : ℝ) else 0)|) ≤
      (∑ c, |(∑ i, if a i = c then (1 : ℝ) else 0) -
        (∑ j, if b j = c then (1 : ℝ) else 0)|) +
      2 * ((σ.edges.filter fun e ↦ a e.1 ≠ b e.2).card : ℝ) := by
  classical
  have h := Finset.sum_le_sum (s := (Finset.univ : Finset C))
    (fun c _ ↦ abs_free_cell_imbalance_le_original_add_crossings σ a b c)
  rw [Finset.sum_add_distrib] at h
  have hflux : (∑ c : C, ∑ e ∈ σ.edges,
      if (a e.1 = c ∧ b e.2 ≠ c) ∨ (a e.1 ≠ c ∧ b e.2 = c) then (1 : ℝ) else 0) =
        2 * ((σ.edges.filter fun e ↦ a e.1 ≠ b e.2).card : ℝ) := by
    rw [Finset.sum_comm]
    have hcell (e : Fin m × Fin n) :
        (∑ c : C,
          if (a e.1 = c ∧ b e.2 ≠ c) ∨ (a e.1 ≠ c ∧ b e.2 = c) then (1 : ℝ) else 0) =
            if a e.1 ≠ b e.2 then (2 : ℝ) else 0 := by
      by_cases he : a e.1 = b e.2
      · simp [he]
      · rw [ite_eq_left he]
        have hterm (c : C) :
            (if (a e.1 = c ∧ b e.2 ≠ c) ∨ (a e.1 ≠ c ∧ b e.2 = c) then (1 : ℝ) else 0) =
              (if a e.1 = c then (1 : ℝ) else 0) +
                (if b e.2 = c then (1 : ℝ) else 0) := by
          by_cases hs : a e.1 = c <;> by_cases ht : b e.2 = c <;> simp_all
        simp_rw [hterm]
        simp [Finset.sum_add_distrib]
        norm_num
    simp_rw [hcell]
    rw [← Finset.sum_filter]
    simp [Finset.sum_const, nsmul_eq_mul, mul_comm]
  rw [hflux] at h
  exact h

end OTSelector.PartialMatching

end
end
