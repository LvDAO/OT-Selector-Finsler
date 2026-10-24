import Mathlib.MeasureTheory.Integral.Bochner.Basic
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Reconstruction.OriginalClasswiseOriginalAtomRepairUnusedExtension.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Reconstruction.OriginalClasswiseOriginalAtomRepairUnusedExtension`; the selected original proof blocks follow. -/
section

/-!
# Probability.UnusedAtomFamilyExtension

## Lemma skeleton

* **Conditions:** A finite set of actual unused labels with probability endpoint laws and integrable squared distances.
* **Objects:** An extension of the family to every original label, equal to a zero-displacement Dirac law off the finite set.
* **Proof detail:** Keep the supplied laws on members and assign dirac(x_i) elsewhere; its squared distance integral is zero and all probability/integrability claims follow by cases.

## Mathematical sources

- [Günter Last; Mathew Penrose, Lectures on the Poisson Process (author version, 21 August 2017)](https://stoch.math.kit.edu/img/Last/lastpenrose2017.pdf#page=22): Section 2.1, pp. 9–10, equations (2.1)–(2.2); multiplicities explicitly allowed on p. 10.
- [Sheldon Axler, Measure, Integration & Real Analysis (author PDF, 12 June 2026)](https://measure.axler.net/MIRA.pdf#page=99): Section 3A, Theorem 3.23, p. 84; Section 3B, Theorem 3.25, p. 88.

Source relation (composition): Pure family-extension adapter; no sampling or repair optimization is performed.
-/

/-! Extend actual unused-label families to all original labels at zero extra energy. -/
open Set Function MeasureTheory
open scoped ENNReal BigOperators Classical
noncomputable section
namespace OTSelector.Reconstruction

/-- Used original labels receive their genuine point mass; unused labels retain
exactly their constructed probability laws. Thus the globally indexed family
has the same unused energies and clock-class laws, including empty subsets. -/
theorem exists_originalUnusedAtomFamily_extension
    {I E : Type*} [DecidableEq I] [PseudoMetricSpace E]
    [MeasurableSpace E] [MeasurableSingletonClass E]
    (U : Finset I) (x : I → E) (laws : U → Measure E)
    (hprob : ∀ i, IsProbabilityMeasure (laws i))
    (hI : ∀ i, Integrable (fun v ↦ dist (x i.val) v^2) (laws i)) :
    ∃ κ : I → Measure E,
      (∀ i, IsProbabilityMeasure (κ i)) ∧
      (∀ i, Integrable (fun v ↦ dist (x i) v^2) (κ i)) ∧
      (∀ i (hi : i ∈ U), κ i = laws ⟨i,hi⟩) ∧
      (∀ i, i ∉ U → κ i = Measure.dirac (x i)) := by
  classical
  let κ : I → Measure E := fun i ↦ if hi : i ∈ U then laws ⟨i,hi⟩ else Measure.dirac (x i)
  refine ⟨κ,?_,?_,?_,?_⟩
  · intro i
    dsimp only [κ]
    split_ifs with hi
    · exact hprob ⟨i,hi⟩
    · infer_instance
  · intro i
    dsimp only [κ]
    split_ifs with hi
    · exact hI ⟨i,hi⟩
    · exact integrable_dirac (by simp)
  · intro i hi
    simp only [κ, hi, dite_true]
  · intro i hi
    simp only [κ, hi, dite_false]

end OTSelector.Reconstruction

end
end
