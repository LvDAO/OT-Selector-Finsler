import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.Probability.ConditionalProbability
import Mathlib.Tactic.Linarith
import OTSelector.Probability.ConditionalMinimumMean

/-!
# Probability.InvariantConditionalMeanZero

## Lemma skeleton

* **Conditions:** An integrable complete real Banach-valued function under a finite measure, and zero conditional mean on every positive-mass event of the conditioning sigma-algebra.
* **Objects:** Its conditional expectation is almost everywhere zero.
* **Proof detail:** Normalize each positive conditioning event to convert the conditional-mean hypothesis to an event integral identity, handle null events automatically, then use conditional-expectation uniqueness.

## Mathematical sources

- [Rick Durrett, Probability: Theory and Examples, fifth edition (2019 author PDF)](https://sites.math.duke.edu/~rtd/PTE/PTE5_011119.pdf#page=213): Section 4.1, conditional-expectation definition and Uniqueness argument, pp. 205–206; Section 4.1.3, Theorems 4.1.16–4.1.18, pp. 214–215.
- [D. H. Fremlin, Measure Theory, Volume 2](https://www1.essex.ac.uk/maths/people/fremlin/chap25.pdf#page=46): Exercises 253Y(f)(i)–(vii), 253Y(g)–(h), pp. 46–47: Banach-valued L1, bounded bilinear maps and section integrals.

Source relation (composition): Finite-measure Banach-valued characterization from defining conditional integrals; no ergodicity assumption is needed.
-/

/-! Vanishing conditional Banach means determine invariant conditional centering. -/
open Set MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory
noncomputable section
namespace OTSelector.Probability

/-- Vanishing means under every positive conditional event give zero
conditional expectation; null events are handled in the original measure. -/
theorem condExp_eq_zero_of_all_positive_cond_integral_eq_zero
    {Ω V : Type*} {m : MeasurableSpace Ω} [m₀ : MeasurableSpace Ω]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
    (P : @Measure Ω m₀) [IsFiniteMeasure P] (hm : m ≤ m₀)
    {f : Ω → V} (hf : Integrable f P)
    (hzero : ∀ A, MeasurableSet[m] A → P A ≠ 0 → ∫ x, f x ∂P[|A] = 0) :
    P[f | m] =ᵐ[P] fun _ ↦ 0 := by
  apply condExp_eq_zero_of_all_setIntegral_eq_zero P hm hf
  intro A hA
  by_cases hz : P A = 0
  · exact setIntegral_measure_zero _ hz
  · have h := hzero A hA hz
    have hr : (P A).toReal ≠ 0 := ENNReal.toReal_ne_zero.mpr ⟨hz, measure_ne_top _ _⟩
    have he : ((P A).toReal)⁻¹ • (∫ x in A, f x ∂P) = 0 := by
      simpa only [ProbabilityTheory.cond, integral_smul_measure, ENNReal.toReal_inv] using h
    exact (smul_eq_zero.mp he).resolve_left (inv_ne_zero hr)

end OTSelector.Probability
