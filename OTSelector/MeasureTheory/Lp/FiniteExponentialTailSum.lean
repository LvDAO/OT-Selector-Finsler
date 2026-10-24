import OTSelector.Probability.ExponentialTailSecondMoment
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Probability.FiniteCountTailTrafficLtwo.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Probability.FiniteCountTailTrafficLtwo`; the selected original proof blocks follow. -/
section

/-!
# MeasureTheory.Lp.FiniteExponentialTailSum

## Lemma skeleton

* **Conditions:** A finite family of the actual count-tail traffic readouts, each with the stated exponential moment and amplitude bounds.
* **Objects:** L2 of the finite tail sum with the literal cardinality times the exponential norm bound.
* **Proof detail:** Apply the one-band exponential-tail L2 estimate to every term and sum with Minkowski.

## Mathematical sources

- [Rick Durrett, Probability: Theory and Examples, 5th edition (11 January 2019)](https://sites.math.duke.edu/~rtd/PTE/PTE5_011119.pdf#page=37): Section 1.6.1, Theorem 1.6.4 and equation (1.6.1), pp. 29–30.
- [Sheldon Axler, Measure, Integration & Real Analysis (author PDF, 12 June 2026)](https://measure.axler.net/MIRA.pdf#page=233): Section 8A, Theorem 8.11, p. 218; Example 8.14, p. 219 (L2 Cauchy–Schwarz).
- [Sheldon Axler, Measure, Integration & Real Analysis (author PDF, 12 June 2026)](https://measure.axler.net/MIRA.pdf#page=214): Section 7A, Theorem 7.14, p. 199 (Minkowski).

Source relation (composition): Finite tail summation without independence of events or readouts.
-/

/-! Count tails of the actual finite birth bands sum in L2 with the literal
number of bands. No independence of the events or readouts is used. -/
open Set MeasureTheory
open scoped ENNReal BigOperators
noncomputable section
namespace OTSelector.Probability

/-- Each original band has its own count and correlated traffic. A common
original exponential-moment bound gives the finite bad-traffic sum its sharp
linear number-of-bands L2 factor and an explicit exponential threshold decay. -/
theorem finite_countTail_traffic_memLp_two_and_exponential_norm
    {Ω ι : Type*} [MeasurableSpace Ω] (P : Measure Ω) (s : Finset ι)
    (N T : ι → Ω → ℝ)
    (hN : ∀ i ∈ s, Measurable (N i)) (hN0 : ∀ i ∈ s, ∀ x, 0 ≤ N i x)
    (hExp : ∀ i ∈ s, Integrable (fun x ↦ Real.exp (N i x)) P)
    {L B K : ℝ} (hExpBound : ∀ i ∈ s, (∫ x, Real.exp (N i x) ∂P) ≤ Real.exp L)
    (hT : ∀ i ∈ s, AEStronglyMeasurable (T i) P) (hB : 0 ≤ B)
    (hbound : ∀ i ∈ s, ∀ᵐ x ∂P, K < N i x → |T i x| ≤ B * N i x) :
    MemLp (fun x ↦ ∑ i ∈ s, {z | K < N i z}.indicator (T i) x) 2 P ∧
      eLpNorm (fun x ↦ ∑ i ∈ s, {z | K < N i z}.indicator (T i) x) 2 P ≤
        ENNReal.ofReal ((s.card : ℝ) * Real.sqrt 8 * B *
          Real.exp (L / 2) * Real.exp (-K / 4)) := by
  have hb i hi := countTail_traffic_memLp_two_and_exponential_norm P
    (hN i hi) (hN0 i hi) (hExp i hi) (hExpBound i hi) (hT i hi) hB (hbound i hi)
  refine ⟨memLp_finsetSum s (fun i hi ↦ (hb i hi).1), ?_⟩
  calc
    _ = eLpNorm (∑ i ∈ s, {z | K < N i z}.indicator (T i)) 2 P := by
      congr 1; funext x; simp
    _ ≤ ∑ i ∈ s, eLpNorm ({z | K < N i z}.indicator (T i)) 2 P :=
      eLpNorm_sum_le (fun i hi ↦ (hb i hi).1.aestronglyMeasurable) (by norm_num)
    _ ≤ ∑ _i ∈ s, ENNReal.ofReal
        (Real.sqrt 8 * B * Real.exp (L / 2) * Real.exp (-K / 4)) :=
      Finset.sum_le_sum (fun i hi ↦ (hb i hi).2.2)
    _ = ENNReal.ofReal (∑ _i ∈ s,
        (Real.sqrt 8 * B * Real.exp (L / 2) * Real.exp (-K / 4))) :=
      (ENNReal.ofReal_sum_of_nonneg (fun _ _ ↦ by positivity)).symm
    _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul]; congr 1; ring

end OTSelector.Probability

end
end
