import OTSelector.Finite.OrderedHallFlow
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Reconstruction.FinslerRelativeLawThresholdClockFlow.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Reconstruction.FinslerRelativeLawThresholdClockFlow`; the selected original proof blocks follow. -/
section

/-!
# Reconstruction.FinslerRelativeLawThresholdClockFlow

**Conditions:** Finite real clock upper/lower thresholds and a nonnegative feasible legal flow with its exact marginals.

**Objects:** Sorted threshold permutations, an ordered legal graph and all weighted Hall cut inequalities.

**Proof detail:** Sort the two finite threshold lists monotonically; sum the nonnegative feasible matrix over a source cut and discard only zero forbidden entries to obtain the neighbor-mass bound.

**Sources:** [Gabriel Peyré; Marco Cuturi, Computational Optimal Transport](https://optimaltransport.github.io/pdf/ComputationalOT.pdf#page=39), Section 2.6, Remarks 2.27–2.28, pp. 35–37, equations (2.31)–(2.37); [Reinhard Diestel, Graph Theory, 4th electronic edition (2010), corrected reprint 2012](https://diestel-graph-theory.com/Sample.pdf#page=2), Chapter 2 opening matching definition and Section 2.1, first three chapter pages; [Terence Tao, Analysis I](https://github.com/teorth/analysis/blob/main/Analysis/Section_7_1.lean), Sections 4.3 (absolute value) and 7.1 (finite series), in particular Proposition 7.1.11.

Source relation (corollary): The cited sections provide the stated mathematical foundations; the exact finite construction and quantitative bound in this module are local consequences, not a claim that the book states the Lean theorem verbatim.
-/

/-!
Deterministic threshold sorting and weighted Hall inequalities for actual finite clock-class coupling matrices.
-/

open MeasureTheory
open scoped BigOperators
noncomputable section
namespace OTSelector.Reconstruction

/-- A separate finite type allows a threshold order without altering `Fin` order. -/
structure ClockThresholdIndex (M : ℕ) where
  index : Fin M
  deriving DecidableEq, Fintype

/-- Arbitrary finite clock classes can be deterministically sorted by their
actual scalar threshold, with stable index tie breaking. -/
theorem exists_monotone_clockThreshold_permutation {M : ℕ} (bound : Fin M → ℝ) :
    ∃ e : Fin M ≃ Fin M, Monotone (fun i ↦ bound (e i)) := by
  classical
  let g : ClockThresholdIndex M → ℝ ×ₗ Fin M := fun i ↦ toLex (bound i.index, i.index)
  have hg : Function.Injective g := by
    intro i j hij
    cases i
    cases j
    congr 1
    exact congrArg (fun p : ℝ ×ₗ Fin M ↦ (ofLex p).2) hij
  let _inst : LinearOrder (ClockThresholdIndex M) := LinearOrder.lift' g hg
  let e₀ : ClockThresholdIndex M ≃ Fin M :=
    { toFun := ClockThresholdIndex.index
      invFun := ClockThresholdIndex.mk
      left_inv := by intro i; cases i; rfl
      right_inv := fun i ↦ rfl }
  let o : Fin M ≃o ClockThresholdIndex M := Fintype.orderIsoFinOfCardEq _
    ((Fintype.card_congr e₀).trans (Fintype.card_fin M))
  refine ⟨o.toEquiv.trans e₀, ?_⟩
  intro i j hij
  have h := o.monotone hij
  change g (o i) ≤ g (o j) at h
  exact Prod.Lex.monotone_fst _ _ h

/-- The class graph given by source upper and target lower thresholds becomes
ordered after independent source and target threshold permutations. -/
theorem exists_ordered_clockThreshold_graph {M L : ℕ}
    (sourceUpper : Fin M → ℝ) (targetLower : Fin L → ℝ) (gap : ℝ) :
    ∃ (e : Fin M ≃ Fin M) (f : Fin L ≃ Fin L),
      ∀ i i' j j', i ≤ i' → j' ≤ j →
        sourceUpper (e i') + gap ≤ targetLower (f j') →
          sourceUpper (e i) + gap ≤ targetLower (f j) := by
  obtain ⟨e, he⟩ := exists_monotone_clockThreshold_permutation sourceUpper
  obtain ⟨f, hf⟩ := exists_monotone_clockThreshold_permutation targetLower
  refine ⟨e, f, ?_⟩
  intro i i' j j' hii hjj hallowed
  exact (add_le_add_left (he hii) gap).trans (hallowed.trans (hf hjj))

/-- An actual legal original finite-class coupling supplies Hall feasibility;
no sampled or adaptive residual law is needed. -/
theorem finiteClockFlow_hall
    {M L : ℕ} (allowed : Fin M → Fin L → Prop)
    (P : Fin M → Fin L → ℝ) (a : Fin M → ℝ) (b : Fin L → ℝ)
    (hP : ∀ i j, 0 ≤ P i j)
    (hrow : ∀ i, ∑ j, P i j = a i) (hcol : ∀ j, ∑ i, P i j = b j)
    (hzero : ∀ i j, ¬ allowed i j → P i j = 0) (A : Finset (Fin M)) :
    (∑ i ∈ A, a i) ≤ ∑ j ∈ orderedClockNeighbors allowed A, b j := by
  classical
  calc
    _ = ∑ j, ∑ i ∈ A, P i j := by simp_rw [← hrow]; rw [Finset.sum_comm]
    _ = ∑ j ∈ orderedClockNeighbors allowed A, ∑ i ∈ A, P i j := by
      symm
      apply Finset.sum_subset (Finset.subset_univ _)
      intro j hj hnj
      apply Finset.sum_eq_zero
      intro i hi
      apply hzero i j
      intro hij
      exact hnj (Finset.mem_filter.mpr ⟨Finset.mem_univ _, i, hi, hij⟩)
    _ ≤ ∑ j ∈ orderedClockNeighbors allowed A, ∑ i, P i j := by
      apply Finset.sum_le_sum
      intro j hj
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        (fun i hi hni ↦ hP i j)
    _ = _ := by simp_rw [hcol]

end OTSelector.Reconstruction

end
end
