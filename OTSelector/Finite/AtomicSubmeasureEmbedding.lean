import Mathlib.MeasureTheory.Integral.Bochner.Basic
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Reconstruction.OriginalReserveFiniteIndexEmbedding.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Reconstruction.OriginalReserveFiniteIndexEmbedding`; the selected original proof blocks follow. -/
section

/-!
# Reconstruction.OriginalReserveFiniteIndexEmbedding

**Conditions:** The reserve point array is injective and its sum of Dirac measures is dominated by the full finite array; measurable singletons are available.

**Objects:** An embedding of reserve indices into the original full indices, preserving every point.

**Proof detail:** Evaluate domination at each reserve singleton to find a representing full index; distinct reserve points force the selected indices to be distinct.

**Sources:** [Günter Last; Mathew Penrose, Lectures on the Poisson Process (author version, 21 August 2017)](https://stoch.math.kit.edu/img/Last/lastpenrose2017.pdf#page=22), Section 2.1, pp. 9–10, equations (2.1)–(2.2); multiplicities explicitly allowed on p. 10; [Terence Tao, Analysis I](https://github.com/teorth/analysis/blob/main/Analysis/Section_7_1.lean), Sections 4.3 (absolute value) and 7.1 (finite series), in particular Proposition 7.1.11.

Source relation (corollary): The cited sections provide the stated mathematical foundations; the exact finite construction and quantitative bound in this module are local consequences, not a claim that the book states the Lean theorem verbatim.
-/

/-! A submeasure of a literal finite input array retains its own original indices. -/
open Set Function MeasureTheory
open scoped ENNReal BigOperators Classical
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-- Every distinct original reserve label embeds into the given full original
array when its literal point measure is a submeasure. The map preserves the
entire marked point, handles empty arrays, and never samples new positions. -/
theorem exists_originalIndexEmbedding_of_sum_dirac_le
    {I J X : Type*} [Fintype I] [Fintype J]
    [MeasurableSpace X] [MeasurableSingletonClass X]
    (reserve : I → X) (full : J → X) (hr : Injective reserve)
    (hle : (∑ i, Measure.dirac (reserve i)) ≤ (∑ j, Measure.dirac (full j))) :
    ∃ e : I ↪ J, ∀ i, full (e i) = reserve i := by
  have hex (i : I) : ∃ j : J, full j = reserve i := by
    have hi : (Measure.dirac (reserve i) : Measure X) ≤ ∑ k, Measure.dirac (reserve k) :=
      Finset.single_le_sum (f := fun k ↦ (Measure.dirac (reserve k) : Measure X))
        (fun _ _ ↦ Measure.zero_le _) (Finset.mem_univ i)
    have hsingle := (hi.trans hle) ({reserve i} : Set X)
    by_contra hn
    have hne (j : J) : full j ≠ reserve i := fun hj ↦ hn ⟨j, hj⟩
    have hz : (∑ j, Measure.dirac (full j)) ({reserve i} : Set X) = 0 := by
      rw [Measure.finsetSum_apply]
      apply Finset.sum_eq_zero
      intro j _
      simp [Measure.dirac_apply', hne j]
    rw [hz] at hsingle
    simp at hsingle
  choose e he using hex
  refine ⟨⟨e, ?_⟩, he⟩
  intro i j hij
  apply hr
  rw [← he i, ← he j, hij]

end OTSelector.Reconstruction

end
end
