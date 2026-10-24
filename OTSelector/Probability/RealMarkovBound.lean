import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Real

/-!
# Real Markov Bound

Conditions: Nonnegative integrable real observable on a finite measure space and a strictly positive threshold.

Objects: Real-valued strict-tail mass bounded by its unnormalized integral divided by the threshold.

Proof detail: Apply Markov to the nonnegative observable and convert finite ENNReal mass to real values.

Relation to primary sources: The finite-measure strict-threshold version of standard Markov inequality, proved with the displayed measure normalization.

References:
* Rick Durrett, Probability: Theory and Examples, fifth edition, author version 11 January 2019, Section 1.6.1, Theorem 1.6.4 and equation (1.6.1), pp. 29–30. https://sites.math.duke.edu/~rtd/PTE/PTE5_011119.pdf#page=37
-/
/-! Shared real-probability Markov transfer on the unchanged finite experiment. -/
open Set MeasureTheory
noncomputable section
namespace OTSelector.Reconstruction

/-- A nonnegative integrable actual observable controls its strict upper event;
no independence or law approximation is needed. -/
theorem measureReal_strict_gt_le_integral_div_of_nonneg {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsFiniteMeasure P] (f : Ω → ℝ) (hf : ∀ p, 0 ≤ f p)
    (hI : Integrable f P) {a : ℝ} (ha : 0 < a) :
    P.real {p | a < f p} ≤ (∫ p, f p ∂P) / a := by
  have hm : P.real {p | a < f p} ≤ P.real {p | a ≤ f p} := measureReal_mono (by
    intro p hp
    exact (show a < f p from hp).le)
  have hmark := mul_meas_ge_le_integral_of_nonneg (Filter.Eventually.of_forall hf) hI a
  refine hm.trans ((le_div_iff₀ ha).mpr ?_)
  simpa only [mul_comm] using hmark

end OTSelector.Reconstruction
