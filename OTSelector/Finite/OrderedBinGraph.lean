import OTSelector.Finite.ThresholdClockHallFlow
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Reconstruction.FinslerRelativeLawOrderedBinGraph.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Reconstruction.FinslerRelativeLawOrderedBinGraph`; the selected original proof blocks follow. -/
section

/-!
# Reconstruction.FinslerRelativeLawOrderedBinGraph

**Conditions:** Finite bounded clock bins have diameter at most gap/4, with gap>0.

**Objects:** One ordered threshold graph containing every genuinely separated bin pair and allowing only forward clock edges.

**Proof detail:** Sort source suprema and target infima; diameter bounds convert a witnessed gap into the half-gap threshold, and the threshold implies every original clock pair is forward.

**Sources:** [Sheldon Axler, Supplement for Measure, Integration & Real Analysis](https://measure.axler.net/SupplementMIRA.pdf#page=18), Section C, Definitions 0.32 and 0.35, pp. 18–19; [Gabriel Peyré; Marco Cuturi, Computational Optimal Transport](https://optimaltransport.github.io/pdf/ComputationalOT.pdf#page=39), Section 2.6, Remarks 2.27–2.28, pp. 35–37, equations (2.31)–(2.37); [Terence Tao, Analysis I](https://github.com/teorth/analysis/blob/main/Analysis/Section_7_1.lean), Sections 4.3 (absolute value) and 7.1 (finite series), in particular Proposition 7.1.11.

Source relation (corollary): The cited sections provide the stated mathematical foundations; the exact finite construction and quantitative bound in this module are local consequences, not a claim that the book states the Lean theorem verbatim.
-/

/-!
Original reference-bin feasibility and measurable legal population reconstruction.
-/

open Set Function MeasureTheory ProbabilityTheory
open scoped BigOperators
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false

/-- Arbitrary finite measurable clock bins of small diameter admit actual
ordered legal class graphs after sorting their true endpoint thresholds.
Empty bins introduce no support or nonemptiness hypothesis. -/
theorem exists_ordered_legal_clockBin_graph
    {m n : ℕ} (S : Fin m → Set ℝ) (T : Fin n → Set ℝ)
    (hSbound : ∀ i, BddAbove (S i)) (hTbound : ∀ j, BddBelow (T j))
    (gap : ℝ) (hgap : 0 < gap)
    (hSdiam : ∀ i, ∀ x ∈ S i, ∀ y ∈ S i, |x - y| ≤ gap / 4)
    (hTdiam : ∀ j, ∀ x ∈ T j, ∀ y ∈ T j, |x - y| ≤ gap / 4) :
    ∃ (e : Fin m ≃ Fin m) (f : Fin n ≃ Fin n),
      let allowed := fun i j ↦ sSup (S (e i)) + gap / 2 ≤ sInf (T (f j))
      (∀ i i' j j', i ≤ i' → j' ≤ j → allowed i' j' → allowed i j) ∧
      (∀ i j, ∀ s ∈ S (e i), ∀ t ∈ T (f j), gap ≤ t - s → allowed i j) ∧
      (∀ i j, allowed i j → ∀ s ∈ S (e i), ∀ t ∈ T (f j), s ≤ t) := by
  obtain ⟨e, f, horder⟩ := exists_ordered_clockThreshold_graph
    (fun i ↦ sSup (S i)) (fun j ↦ sInf (T j)) (gap / 2)
  refine ⟨e, f, horder, ?_, ?_⟩
  · intro i j s hs t ht hst
    have hupper : sSup (S (e i)) ≤ s + gap / 4 := by
      apply csSup_le ⟨s, hs⟩
      intro x hx
      have h := (abs_le.mp (hSdiam (e i) x hx s hs)).2
      linarith
    have hlower : t - gap / 4 ≤ sInf (T (f j)) := by
      apply le_csInf ⟨t, ht⟩
      intro y hy
      have h := (abs_le.mp (hTdiam (f j) t ht y hy)).2
      linarith
    change sSup (S (e i)) + gap / 2 ≤ sInf (T (f j))
    linarith
  · intro i j hij s hs t ht
    have hu : s ≤ sSup (S (e i)) := le_csSup (hSbound (e i)) hs
    have hl : sInf (T (f j)) ≤ t := csInf_le (hTbound (f j)) ht
    change sSup (S (e i)) + gap / 2 ≤ sInf (T (f j)) at hij
    linarith

end OTSelector.Reconstruction

end
end
