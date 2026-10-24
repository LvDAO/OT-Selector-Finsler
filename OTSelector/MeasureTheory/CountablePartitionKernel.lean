import Mathlib.Probability.Kernel.Basic

/-!
## Lemma skeleton

* **Conditions:** A countable measurable disjoint partition and probability kernels, with a fallback.
* **Objects:** A kernel equal to the prescribed kernel on each cell.
* **Proof detail:** Paste measurable evaluations on countably many cells; verify total mass one pointwise.

## Mathematical sources

* D. H. Fremlin, *Measure Theory, Volume 4*, Section 452A–452F (integration of families and disintegrations), 452M (product disintegration).
  https://www1.essex.ac.uk/maths/people/fremlin/chap45.pdf#page=18
* D. H. Fremlin, *Measure Theory, Volume 4*, Sections 418A–418C, measurable maps, products, and limits into metrizable/Polish spaces.
  https://www1.essex.ac.uk/maths/people/fremlin/chap41.pdf#page=106

**Relationship to the sources:** Countable gluing and fallback selection are measurable-map constructors, not a claimed new disintegration theorem.
-/

/-!
# Measurable countable partition of probability kernels

Countably many measurable, disjoint cells use their prescribed kernels exactly, while
the complement uses a fixed fallback. Probability kernels remain Markov after gluing.
-/
open Set Function Filter MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators
noncomputable section
namespace OTSelector.Probability
set_option backward.isDefEq.respectTransparency false

/-- Measurable kernels on a countable cell family, with a fixed fallback off the union. -/
def countablePartitionKernel
    {I A S : Type*} [Countable I] [MeasurableSpace A] [MeasurableSpace S]
    (cell : I → Set A) (hcell : ∀ i, MeasurableSet (cell i))
    (κ : I → Kernel A S) (fallback : Kernel A S) : Kernel A S := by
  classical
  exact Kernel.piecewise (MeasurableSet.iUnion hcell)
    (Kernel.sum (fun i ↦ Kernel.piecewise (hcell i) (κ i) 0)) fallback

/-- On a disjoint cell the glued kernel equals precisely the prescribed original kernel. -/
theorem countablePartitionKernel_eq
    {I A S : Type*} [Countable I] [MeasurableSpace A] [MeasurableSpace S]
    (cell : I → Set A) (hcell : ∀ i, MeasurableSet (cell i))
    (hdisj : Pairwise (Disjoint on cell)) (κ : I → Kernel A S) (fallback : Kernel A S)
    (i : I) {a : A} (ha : a ∈ cell i) :
    countablePartitionKernel cell hcell κ fallback a = κ i a := by
  classical
  rw [countablePartitionKernel, Kernel.piecewise_apply, ite_eq_left (mem_iUnion.mpr ⟨i,ha⟩)]
  ext U hU
  rw [Kernel.sum_apply' _ _ hU, tsum_eq_single i]
  · rw [Kernel.piecewise_apply', ite_eq_left ha]
  · intro j hji
    rw [Kernel.piecewise_apply', ite_eq_right (fun haj ↦ disjoint_left.mp (hdisj hji) haj ha)]
    rfl

/-- Off the union the glued kernel is the fixed original fallback. -/
theorem countablePartitionKernel_eq_fallback
    {I A S : Type*} [Countable I] [MeasurableSpace A] [MeasurableSpace S]
    (cell : I → Set A) (hcell : ∀ i, MeasurableSet (cell i))
    (κ : I → Kernel A S) (fallback : Kernel A S)
    {a : A} (ha : a ∉ ⋃ i, cell i) :
    countablePartitionKernel cell hcell κ fallback a = fallback a := by
  classical
  exact ite_eq_right ha

/-- A disjoint countable gluing of original probability kernels is Markov everywhere. -/
theorem isMarkovKernel_countablePartitionKernel
    {I A S : Type*} [Countable I] [MeasurableSpace A] [MeasurableSpace S]
    (cell : I → Set A) (hcell : ∀ i, MeasurableSet (cell i))
    (hdisj : Pairwise (Disjoint on cell)) (κ : I → Kernel A S) (fallback : Kernel A S)
    [∀ i, IsMarkovKernel (κ i)] [IsMarkovKernel fallback] :
    IsMarkovKernel (countablePartitionKernel cell hcell κ fallback) := by
  constructor
  intro a
  by_cases ha : a ∈ ⋃ i, cell i
  · obtain ⟨i,hi⟩ := mem_iUnion.mp ha
    rw [countablePartitionKernel_eq cell hcell hdisj κ fallback i hi]
    infer_instance
  · rw [countablePartitionKernel_eq_fallback cell hcell κ fallback ha]
    infer_instance

end OTSelector.Probability
