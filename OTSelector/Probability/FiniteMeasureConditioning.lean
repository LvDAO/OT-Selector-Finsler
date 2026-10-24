import Mathlib.Probability.ConditionalProbability
import OTSelector.MeasureTheory.FiniteMeasureNormalizationVariation
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Reconstruction.FiniteMeasureConditioning.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Reconstruction.FiniteMeasureConditioning`; the selected original proof blocks follow. -/
section

/-!
# Probability.FiniteMeasureConditioning

## Lemma skeleton

* **Conditions:** A finite-mass restriction or a measurable target set and measurable map.
* **Objects:** Exact normalized-restriction/conditioning identity and pushforward of conditioning on a preimage.
* **Proof detail:** Unfold conditioning as inverse event-mass times restriction and commute measurable pushforward with restriction and scalar multiplication.

## Mathematical sources

- [D. H. Fremlin, Measure Theory, Volume 2](https://www1.essex.ac.uk/maths/people/fremlin/chap23.pdf): Section 235G, integration along an inverse-measure-preserving map.
- [D. H. Fremlin, Measure Theory, Volume 2](https://www1.essex.ac.uk/maths/people/fremlin/chap23.pdf#page=27): Sections 234I–234L, pp. 27–29; especially 234L(c); Section 235K, p. 40.

Source relation (composition): Definitional finite-law normalization, including the library zero-mass convention; no positive mass is silently inserted.
-/

/-! Exact normalization and conditioning of original finite restrictions. -/
open Set Function MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false
variable {X : Type*} [MeasurableSpace X]

/-- Normalizing an original restriction is exactly conditioning, including a
null event. Only finiteness of that event is required. -/
theorem normalizedFiniteLaw_restrict_eq_cond (μ : Measure X) (S : Set X)
    (hS : μ S ≠ ∞) : normalizedFiniteLaw (μ.restrict S) = ProbabilityTheory.cond μ S := by
  by_cases hzero : μ S = 0
  · have hz : μ.restrict S = 0 := Measure.restrict_eq_zero.mpr hzero
    simp only [normalizedFiniteLaw, hz, smul_zero, ProbabilityTheory.cond]
  unfold normalizedFiniteLaw ProbabilityTheory.cond
  rw [measureReal_def, Measure.restrict_apply_univ, Real.toNNReal_inv, ENNReal.toNNReal_toReal_eq]
  change ((μ S).toNNReal)⁻¹ • μ.restrict S = (μ S)⁻¹ • μ.restrict S
  rw [← Measure.coe_nnreal_smul, ENNReal.coe_inv, ENNReal.coe_toNNReal hS]
  exact ENNReal.toNNReal_ne_zero.mpr ⟨hzero, hS⟩

/-- Conditioning on an observed event commutes with the original measurable
observation, including null events. -/
theorem map_cond_preimage {Y : Type*} [MeasurableSpace Y]
    (μ : Measure X) {f : X → Y} (hf : Measurable f)
    {S : Set Y} (hS : MeasurableSet S) :
    (ProbabilityTheory.cond μ (f ⁻¹' S)).map f = ProbabilityTheory.cond (μ.map f) S := by
  unfold ProbabilityTheory.cond
  rw [Measure.map_smul, ← Measure.restrict_map hf hS, Measure.map_apply hf hS]

end OTSelector.Reconstruction

end
end
