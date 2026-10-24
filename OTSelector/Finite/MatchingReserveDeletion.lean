import Mathlib.MeasureTheory.Measure.Dirac
import OTSelector.Finite.PartialMatching
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Reconstruction.OriginalLegalScreeningComparatorOriginalDeletion.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Reconstruction.OriginalLegalScreeningComparatorOriginalDeletion`; the selected original proof blocks follow. -/
section

/-!
# Reconstruction.OriginalLegalScreeningComparatorOriginalDeletion

**Conditions:** A partial matching retains its original endpoint labels; deleted reserve indices are free and have exactly the excess cardinalities.

**Objects:** Unused original-label counts and unchanged counting laws after reserve deletion.

**Proof detail:** Subtract only the embedded reserve indices from free endpoints, use exact finite-cardinality subtraction and cancel the corresponding Dirac sums against the given original-law decomposition.

**Sources:** [Reinhard Diestel, Graph Theory, 4th electronic edition (2010), corrected reprint 2012](https://diestel-graph-theory.com/Sample.pdf#page=2), Chapter 2 opening matching definition and Section 2.1, first three chapter pages; [Günter Last; Mathew Penrose, Lectures on the Poisson Process (author version, 21 August 2017)](https://stoch.math.kit.edu/img/Last/lastpenrose2017.pdf#page=22), Section 2.1, pp. 9–10, equations (2.1)–(2.2); multiplicities explicitly allowed on p. 10; [Terence Tao, Analysis I](https://github.com/teorth/analysis/blob/main/Analysis/Section_7_1.lean), Sections 4.3 (absolute value) and 7.1 (finite series), in particular Proposition 7.1.11; [OTSelector project, Original strict-screen residual slack and repair](main.tex#strict-screen-residual-slack), main.tex label strict-screen-residual-slack, line 6749.

Source relation (composition): The cited sections provide the stated mathematical foundations; the exact finite construction and quantitative bound in this module are local consequences, not a claim that the book states the Lean theorem verbatim.
-/

/-! Exact original-label cardinalities and counting laws after real excess deletion. -/

open MeasureTheory
open scoped BigOperators Classical

noncomputable section
namespace OTSelector.Reconstruction
variable {m n K : ℕ}

/-- Removing exactly the actual source color excess from unused rows leaves
the precise number of rows needed to complete the retained core. -/
theorem sourceDeletedUnused_count_spec (σ : OTSelector.PartialMatching m n)
    (D : Finset (Fin m)) (hD : D ⊆ σ.freeRows) (hcard : D.card = m-n) :
    σ.freeRows \ D ⊆ σ.freeRows ∧ σ.card + (σ.freeRows \ D).card = min m n := by
  refine ⟨Finset.sdiff_subset, ?_⟩
  rw [Finset.card_sdiff_of_subset hD, σ.card_freeRows, hcard]
  have := σ.card_le
  omega

/-- The same original target bookkeeping uses its own actual color excess. -/
theorem targetDeletedUnused_count_spec (σ : OTSelector.PartialMatching m n)
    (D : Finset (Fin n)) (hD : D ⊆ σ.freeCols) (hcard : D.card = n-m) :
    σ.freeCols \ D ⊆ σ.freeCols ∧ σ.card + (σ.freeCols \ D).card = min m n := by
  refine ⟨Finset.sdiff_subset, ?_⟩
  rw [Finset.card_sdiff_of_subset hD, σ.card_freeCols, hcard]
  have := σ.card_le
  omega

/-- Deleting the two actual color excesses balances the original unused labels. -/
theorem excessDeletedUnused_card_eq (σ : OTSelector.PartialMatching m n)
    (D : Finset (Fin m)) (E : Finset (Fin n)) (hD : D ⊆ σ.freeRows) (hE : E ⊆ σ.freeCols)
    (hDcard : D.card = m-n) (hEcard : E.card = n-m) :
    (σ.freeRows \ D).card = (σ.freeCols \ E).card := by
  have hs := (sourceDeletedUnused_count_spec σ D hD hDcard).2
  have ht := (targetDeletedUnused_count_spec σ E hE hEcard).2
  omega

/-- A true finite original window conservation law survives deletion of any
observed reserve subset. Only finite used and deleted counting laws are cancelled. -/
theorem unusedOriginalLaw_after_reserveDeletion
    {X I J : Type*} [MeasurableSpace X] [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    (x : I → X) (reserve : J → X) (used : Finset I) (r : J ↪ I)
    (hpoints : ∀ j, x (r j) = reserve j)
    (hfree : Finset.univ.map r ⊆ Finset.univ \ used) (port : Measure X)
    (hwindow : (∑ i, Measure.dirac (x i)) =
      (∑ i ∈ used, Measure.dirac (x i)) + port + ∑ j, Measure.dirac (reserve j))
    (D : Finset J) :
    (∑ i ∈ (Finset.univ \ used) \ D.map r, Measure.dirac (x i)) =
      port + ∑ j ∈ Finset.univ \ D, Measure.dirac (reserve j) := by
  classical
  let U := ∑ i ∈ used, Measure.dirac (x i)
  have hsplit : U + (∑ i ∈ Finset.univ \ used, Measure.dirac (x i)) =
      ∑ i, Measure.dirac (x i) := by
    simpa only [add_comm] using (Finset.sum_sdiff (f := fun i ↦ Measure.dirac (x i))
      (Finset.subset_univ used))
  have hf : (∑ i ∈ Finset.univ \ used, Measure.dirac (x i)) =
      port + ∑ j, Measure.dirac (reserve j) :=
    (Measure.add_right_inj U _ _).mp (hsplit.trans (by simpa only [add_assoc] using hwindow))
  have hd : D.map r ⊆ Finset.univ \ used :=
    (Finset.map_subset_map.mpr (Finset.subset_univ D)).trans hfree
  have hm : (∑ i ∈ D.map r, Measure.dirac (x i)) = ∑ j ∈ D, Measure.dirac (reserve j) := by
    rw [Finset.sum_map]
    simp only [hpoints]
  apply (Measure.add_left_inj (∑ j ∈ D, Measure.dirac (reserve j)) _ _).mp
  calc
    _ = ∑ i ∈ Finset.univ \ used, Measure.dirac (x i) := by
      rw [← hm]
      exact Finset.sum_sdiff hd
    _ = port + ∑ j, Measure.dirac (reserve j) := hf
    _ = _ := by
      rw [← Finset.sum_sdiff (f := fun j ↦ Measure.dirac (reserve j)) (Finset.subset_univ D)]
      ac_rfl

/-- The real used-edge source law and original reserve embedding identify exactly
the unchanged undeleted unused rows, without distinctness of original observations. -/
theorem sourceUnusedOriginalLaw_after_reserveDeletion
    {X : Type*} [MeasurableSpace X] (σ : OTSelector.PartialMatching m n)
    (x : Fin m → X) (reserve : Fin K → X) (r : Fin K ↪ Fin m)
    (hpoints : ∀ j, x (r j) = reserve j) (hfree : Finset.univ.map r ⊆ σ.freeRows)
    (port : Measure X)
    (hwindow : (∑ i, Measure.dirac (x i)) =
      (∑ e ∈ σ.edges, Measure.dirac (x e.1)) + port + ∑ j, Measure.dirac (reserve j))
    (D : Finset (Fin K)) :
    σ.freeRows \ D.map r ⊆ σ.freeRows ∧
      (∑ i ∈ σ.freeRows \ D.map r, Measure.dirac (x i)) =
        port + ∑ j ∈ Finset.univ \ D, Measure.dirac (reserve j) := by
  classical
  have hu : (∑ i ∈ σ.rows, Measure.dirac (x i)) = ∑ e ∈ σ.edges, Measure.dirac (x e.1) := by
    rw [OTSelector.PartialMatching.rows, Finset.sum_image]
    exact fun a ha b hb hab ↦ σ.row_inj a ha b hb hab
  refine ⟨Finset.sdiff_subset, unusedOriginalLaw_after_reserveDeletion x reserve σ.rows r hpoints hfree port ?_ D⟩
  rw [hu]
  exact hwindow

/-- The target statement reuses the same finite partition proof through the
actual column injection of the retained edges. -/
theorem targetUnusedOriginalLaw_after_reserveDeletion
    {X : Type*} [MeasurableSpace X] (σ : OTSelector.PartialMatching m n)
    (x : Fin n → X) (reserve : Fin K → X) (r : Fin K ↪ Fin n)
    (hpoints : ∀ j, x (r j) = reserve j) (hfree : Finset.univ.map r ⊆ σ.freeCols)
    (port : Measure X)
    (hwindow : (∑ i, Measure.dirac (x i)) =
      (∑ e ∈ σ.edges, Measure.dirac (x e.2)) + port + ∑ j, Measure.dirac (reserve j))
    (D : Finset (Fin K)) :
    σ.freeCols \ D.map r ⊆ σ.freeCols ∧
      (∑ i ∈ σ.freeCols \ D.map r, Measure.dirac (x i)) =
        port + ∑ j ∈ Finset.univ \ D, Measure.dirac (reserve j) := by
  classical
  have hu : (∑ i ∈ σ.cols, Measure.dirac (x i)) = ∑ e ∈ σ.edges, Measure.dirac (x e.2) := by
    rw [OTSelector.PartialMatching.cols, Finset.sum_image]
    exact fun a ha b hb hab ↦ σ.col_inj a ha b hb hab
  refine ⟨Finset.sdiff_subset, unusedOriginalLaw_after_reserveDeletion x reserve σ.cols r hpoints hfree port ?_ D⟩
  rw [hu]
  exact hwindow

end OTSelector.Reconstruction

end
end
