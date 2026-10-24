import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Reconstruction.WindowJointAbsoluteContinuity.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Reconstruction.WindowJointAbsoluteContinuity`; the selected original proof blocks follow. -/
section

/-!
# MeasureTheory.WindowJointAbsoluteContinuity

## Lemma skeleton

* **Conditions:** A countable almost-everywhere measurable window cover and joint absolute continuity for each disjointified window against its own label marginal times volume.
* **Objects:** Joint absolute continuity for the whole original label-clock law.
* **Proof detail:** Each window label marginal is dominated by the full one, so its null-reference event is locally null. Sum the countable window measures and remove the null complement.

## Mathematical sources

- [D. H. Fremlin, Measure Theory, Volume 2](https://www1.essex.ac.uk/maths/people/fremlin/chap23.pdf): Sections 232E–232I, Radon–Nikodym and Lebesgue decomposition; Section 235K, change of measure.
- [D. H. Fremlin, Measure Theory, Volume 2](https://www1.essex.ac.uk/maths/people/fremlin/chap25.pdf#page=2): Sections 251A–251I, pp. 2–6: rectangular covers, product outer measures and the product-measure rectangle formula.
- [Sheldon Axler, Measure, Integration & Real Analysis (author PDF, 12 June 2026)](https://measure.axler.net/MIRA.pdf#page=93): Section 3A, Theorem 3.11, p. 78 (Monotone Convergence).

Source relation (composition): Elementary countable window assembly under the original reference law.
-/

/-!+# Combining the original window joint laws

Absolute continuity relative to each piece's own label law lifts to the full
label law and sums over an almost-everywhere countable cover.
-/

open Set MeasureTheory

namespace OTSelector.Reconstruction

/-- Actual window joint laws control the whole joint law relative to its own
label marginal. The cover and each piece refer to the original physical law. -/
theorem labelClock_joint_absolutelyContinuous_of_window_pieces
    {M Z : Type*} [MeasurableSpace M] [MeasurableSpace Z]
    (η : Measure M) {a : M → Z} {u : M → ℝ}
    (ha : Measurable a) (hu : Measurable u)
    (O : ℕ → Set M) (hO : ∀ j, MeasurableSet (O j))
    (hcover : ∀ᵐ x ∂η, x ∈ ⋃ j, O j)
    (hpiece : ∀ j, (η.restrict (disjointed O j)).map (fun x ↦ (a x, u x)) ≪
      ((η.restrict (disjointed O j)).map a).prod (volume : Measure ℝ)) :
    η.map (fun x ↦ (a x, u x)) ≪ (η.map a).prod (volume : Measure ℝ) := by
  let C := disjointed O
  have hC : ∀ j, MeasurableSet (C j) := MeasurableSet.disjointed hO
  have hfull : ∀ᵐ x ∂η, x ∈ ⋃ j, C j := by
    simpa only [C, iUnion_disjointed] using hcover
  have hsum : Measure.sum (fun j ↦ η.restrict (C j)) = η := by
    rw [← Measure.restrict_iUnion (disjoint_disjointed O) hC]
    exact Measure.restrict_eq_self_of_ae_mem hfull
  have hsumQ : Measure.sum (fun j ↦
      (η.restrict (C j)).map (fun x ↦ (a x, u x))) =
        η.map (fun x ↦ (a x, u x)) := by
    rw [← Measure.map_sum (ha.prodMk hu).aemeasurable, hsum]
  rw [← hsumQ]
  apply Measure.absolutelyContinuous_sum_left
  intro j
  exact (hpiece j).trans
    (((Measure.map_mono (Measure.restrict_le_self (s := C j)) ha).absolutelyContinuous).prod
      Measure.AbsolutelyContinuous.rfl)

end OTSelector.Reconstruction

end
