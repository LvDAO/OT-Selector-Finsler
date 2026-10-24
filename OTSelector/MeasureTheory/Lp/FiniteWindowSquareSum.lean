import Mathlib.Algebra.Order.Chebyshev
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSpace.InfiniteSum
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Probability.FiniteWindowTrafficSquare.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Probability.FiniteWindowTrafficSquare`; the selected original proof blocks follow. -/
section

/-!
# MeasureTheory.Lp.FiniteWindowSquareSum

## Lemma skeleton

* **Conditions:** A finite L2 window family with one uniform real second-moment upper bound.
* **Objects:** Squared integral of the sum is bounded by cardinality squared times that bound.
* **Proof detail:** Apply finite Minkowski to the square-root second moments and square the resulting norm bound, handling the empty family separately.

## Mathematical sources

- [Sheldon Axler, Measure, Integration & Real Analysis (author PDF, 12 June 2026)](https://measure.axler.net/MIRA.pdf#page=214): Section 7A, Theorem 7.14, p. 199 (Minkowski).
- [Sheldon Axler, Measure, Integration & Real Analysis (author PDF, 12 June 2026)](https://measure.axler.net/MIRA.pdf#page=233): Section 8A, Theorem 8.11, p. 218; Example 8.14, p. 219 (L2 Cauchy–Schwarz).

Source relation (composition): Finite-sum second-moment consequence without orthogonality assumptions.
-/

/-! Group the fixed finite physical clock cover inside each original mark band
before summing bands. The original band energy is spent once per fixed window. -/
open Set MeasureTheory
open scoped ENNReal BigOperators
noncomputable section
namespace OTSelector.Probability

/-- Actual finite-window traffic pieces on the same original scene combine in
L2 with at most the square of the fixed number of physical windows in their mean-square
bound. No independence of the physical windows or their events is used. -/
theorem finiteWindow_traffic_memLp_two_of_uniform_second_moment
    {Ω ι : Type*} [MeasurableSpace Ω] (P : Measure Ω) (windows : Finset ι)
    (T : ι → Ω → ℝ) (hT : ∀ i ∈ windows, MemLp (T i) 2 P)
    {B : ℝ} (hmean : ∀ i ∈ windows, (∫ x, T i x ^ 2 ∂P) ≤ B) :
    MemLp (fun x ↦ ∑ i ∈ windows, T i x) 2 P ∧
      (∫ x, (∑ i ∈ windows, T i x) ^ 2 ∂P) ≤ (windows.card : ℝ) ^ 2 * B := by
  have hsum := memLp_finsetSum windows hT
  have hsq (i : ι) (hi : i ∈ windows) : Integrable (fun x ↦ T i x ^ 2) P :=
    (memLp_two_iff_integrable_sq (hT i hi).aestronglyMeasurable).mp (hT i hi)
  have hisum : Integrable (fun x ↦ ∑ i ∈ windows, T i x ^ 2) P :=
    integrable_finsetSum windows hsq
  refine ⟨hsum, ?_⟩
  calc
    _ ≤ ∫ x, (windows.card : ℝ) * (∑ i ∈ windows, T i x ^ 2) ∂P := by
      apply integral_mono_ae
        ((memLp_two_iff_integrable_sq hsum.aestronglyMeasurable).mp hsum)
        (hisum.const_mul (windows.card : ℝ))
      exact Filter.Eventually.of_forall (fun x ↦ sq_sum_le_card_mul_sum_sq)
    _ = (windows.card : ℝ) * ∑ i ∈ windows, ∫ x, T i x ^ 2 ∂P := by
      rw [integral_const_mul, integral_finsetSum windows hsq]
    _ ≤ (windows.card : ℝ) * ∑ _i ∈ windows, B :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum hmean) (Nat.cast_nonneg _)
    _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul]; ring

end OTSelector.Probability

end
end
