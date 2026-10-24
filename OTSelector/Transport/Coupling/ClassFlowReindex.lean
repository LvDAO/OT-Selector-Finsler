import OTSelector.Probability.FiniteCellClassFlow
import OTSelector.Transport.Coupling.FiniteClockMixture
import OTSelector.Transport.Coupling.WindowPairFlow
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Reconstruction.FinslerRelativeLawClassFlowReindex.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Reconstruction.FinslerRelativeLawClassFlowReindex`; the selected original proof blocks follow. -/
section

/-!
# Reconstruction.FinslerRelativeLawClassFlowReindex

**Conditions:** Finite source and target class equivalences; the original population kernels have their explicit s-finiteness instances.

**Objects:** The unchanged class population kernel, unsorted exact marginals and unsorted window masks.

**Proof detail:** Reindex the two finite kernel sums by inverse equivalences and simplify composition; each row, column and mask then evaluates on its original literal clock bins.

**Sources:** [D. H. Fremlin, Measure Theory, Volume 4](https://www1.essex.ac.uk/maths/people/fremlin/chap45.pdf#page=18), Section 452A–452F (integration of families and disintegrations), 452M (product disintegration); [Terence Tao, Analysis I](https://github.com/teorth/analysis/blob/main/Analysis/Section_7_1.lean), Sections 4.3 (absolute value) and 7.1 (finite series), in particular Proposition 7.1.11.

Source relation (adapter): The cited sections provide the stated mathematical foundations; the exact finite construction and quantitative bound in this module are local consequences, not a claim that the book states the Lean theorem verbatim.
-/

/-! Sorting a finite clock-flow proof preserves its literal original classes. -/
open Set Function MeasureTheory ProbabilityTheory
open scoped BigOperators
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false

/-- Relabeling both finite flow indices leaves the actual raw-clock kernel unchanged. -/
theorem finiteClassPopulationKernel_reindex
    {I J I' J' Z X Y : Type*} [Fintype I] [Fintype J] [Fintype I'] [Fintype J']
    [MeasurableSpace Z] [MeasurableSpace X] [MeasurableSpace Y]
    (e : I' ≃ I) (f : J' ≃ J) (P : Z → I → J → ℝ)
    (α : I → Kernel Z X) (β : J → Kernel Z Y)
    [∀ i, IsSFiniteKernel (α i)] [∀ j, IsSFiniteKernel (β j)] :
    finiteClassPopulationKernel (fun z i j ↦ P z (e i) (f j))
      (fun i ↦ α (e i)) (fun j ↦ β (f j)) = finiteClassPopulationKernel P α β := by
  unfold finiteClassPopulationKernel
  have hsum (i : I') :
      (∑ j, classWeightedKernel (fun z ↦ P z (e i) (f j)) ((α (e i)) ×ₖ (β (f j)))) =
        ∑ j, classWeightedKernel (fun z ↦ P z (e i) j) ((α (e i)) ×ₖ (β j)) :=
    f.sum_comp (fun j ↦ classWeightedKernel (fun z ↦ P z (e i) j) ((α (e i)) ×ₖ (β j)))
  simp_rw [hsum]
  exact e.sum_comp (fun i ↦ ∑ j, classWeightedKernel (fun z ↦ P z i j) ((α i) ×ₖ (β j)))

/-- Unsorting a finite matrix restores its original row and column laws exactly. -/
theorem originalClassFlow_unsort_rows_cols
    {I J I' J' : Type*} [Fintype I] [Fintype J] [Fintype I'] [Fintype J']
    (e : I' ≃ I) (f : J' ≃ J) (P Q : I' → J' → ℝ) (a : I → ℝ) (b : J → ℝ)
    (hrow : ∀ i, ∑ j, (P i j + Q i j) = a (e i))
    (hcol : ∀ j, ∑ i, (P i j + Q i j) = b (f j)) :
    (∀ i, ∑ j, (P (e.symm i) (f.symm j) + Q (e.symm i) (f.symm j)) = a i) ∧
    (∀ j, ∑ i, (P (e.symm i) (f.symm j) + Q (e.symm i) (f.symm j)) = b j) := by
  constructor
  · intro i
    calc
      _ = ∑ j, (P (e.symm i) j + Q (e.symm i) j) :=
        f.symm.sum_comp (fun j ↦ P (e.symm i) j + Q (e.symm i) j)
      _ = a i := by simpa only [e.apply_symm_apply] using hrow (e.symm i)
  · intro j
    calc
      _ = ∑ i, (P i (f.symm j) + Q i (f.symm j)) :=
        e.symm.sum_comp (fun i ↦ P i (f.symm j) + Q i (f.symm j))
      _ = b j := by simpa only [f.apply_symm_apply] using hcol (f.symm j)

/-- Sorting changes neither the actual original pair-class mass nor its static window mask. -/
theorem actualClockClassFlow_unsort_mask
    {I J I' J' : Type*} (e : I' ≃ I) (f : J' ≃ J)
    (γ : Measure (ℝ × ℝ)) (S : I → Set ℝ) (T : J → Set ℝ)
    (H : Set (ℝ × ℝ)) (c d : ℝ) (i : I) (j : J) :
    maskedClockFlow (fun k l ↦ ((S (e k) ×ˢ T (f l)) ∩ H).Nonempty)
      (fun k l ↦ c * actualClockClassFlow γ (fun k ↦ S (e k)) (fun l ↦ T (f l)) k l / d)
      (e.symm i) (f.symm j) =
    maskedClockFlow (fun k l ↦ ((S k ×ˢ T l) ∩ H).Nonempty)
      (fun k l ↦ c * actualClockClassFlow γ S T k l / d) i j := by
  simp only [maskedClockFlow, actualClockClassFlow, Equiv.apply_symm_apply]
  congr 1
  simp only [Equiv.apply_symm_apply]

end OTSelector.Reconstruction

end
end
