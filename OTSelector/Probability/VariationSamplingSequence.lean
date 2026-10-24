import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import OTSelector.MeasureTheory.FiniteMeasureNormalizationVariation
import OTSelector.Probability.CommonSubmeasureSampling
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Reconstruction.OriginalProbabilityVariationSampling.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Reconstruction.OriginalProbabilityVariationSampling`; the selected original proof blocks follow. -/
section

/-!
# Probability.VariationSamplingSequence

## Lemma skeleton

* **Conditions:** Original probability laws on a measurable-equality space; the sequential version assumes their full variation tends to zero.
* **Objects:** Exact sampling couplings and a sequence with disagreement probability tending to zero.
* **Proof detail:** Use the common part of the two measures for diagonal sampling and independently couple residuals; bound mismatch by full variation and squeeze the resulting sequence.

## Mathematical sources

- [Sheldon Axler, Measure, Integration & Real Analysis (author PDF, 12 June 2026)](https://measure.axler.net/MIRA.pdf#page=275): Section 9A, Theorems 9.9–9.10, pp. 259–261 (total variation and density formula).
- [Gabriel Peyré; Marco Cuturi, Computational Optimal Transport (2019 author version)](https://optimaltransport.github.io/pdf/ComputationalOT.pdf): Section 2.2, Definition 2.1 and equations (2.6)–(2.7), p. 12; Section 2.3, Remark 2.13, equations (2.14)–(2.15), p. 20.
- [D. H. Fremlin, Measure Theory, Volume 2](https://www1.essex.ac.uk/maths/people/fremlin/chap25.pdf#page=19): Theorems 252B–252C (Fubini) and 252G–252H (Tonelli), pp. 19–25.

Source relation (composition): Common-part coupling corollary with an upper bound by full variation; no stronger maximal-coupling equality is claimed.
-/

/-! Original probability-law variation produces actual exact sampling
couplings and their vanishing original disagreement probabilities. -/
open Set Function MeasureTheory ProbabilityTheory Filter
open scoped Topology ENNReal NNReal Classical
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

/-- Original probability laws supply one exact common-sampling coupling whose
changed probability is bounded by their actual signed variation. -/
theorem exists_original_probability_variation_sampling
    {X : Type*} [MeasurableSpace X] [MeasurableEq X]
    (μ ν : Measure X) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    ∃ κ : ProbabilityMeasure (X × X),
      (κ : Measure (X × X)).map Prod.fst = μ ∧
      (κ : Measure (X × X)).map Prod.snd = ν ∧
      (κ : Measure (X × X)) {p | p.1 ≠ p.2} ≤
        (μ.toSignedMeasure - ν.toSignedMeasure).totalVariation univ := by
  obtain ⟨κ,hκ,hf,hs,hb⟩ := exists_common_sampling_of_submeasure μ ν (commonFiniteLaw μ ν)
    (commonFiniteLaw_le_left μ ν) (commonFiniteLaw_le_right μ ν)
  exact ⟨⟨κ,hκ⟩,hf,hs,hb.trans (commonFiniteLaw_residual_bounds μ ν).2.2.1⟩

/-- A convergent sequence of actual original probability laws has exact
common-sampling couplings to the original limit law with vanishing changed
probability; this supplies the pressure continuity factory directly. -/
theorem exists_original_probability_variation_sampling_sequence
    {X : Type*} [MeasurableSpace X] [MeasurableEq X]
    (μ : ℕ → ProbabilityMeasure X) (ν : ProbabilityMeasure X)
    (hvariation : Tendsto (fun n ↦
      ((μ n : Measure X).toSignedMeasure - (ν : Measure X).toSignedMeasure).totalVariation.real univ)
      atTop (𝓝 0)) :
    ∃ κ : ℕ → ProbabilityMeasure (X × X),
      (∀ n, (κ n : Measure (X × X)).map Prod.fst = (μ n : Measure X)) ∧
      (∀ n, (κ n : Measure (X × X)).map Prod.snd = (ν : Measure X)) ∧
      Tendsto (fun n ↦ ((κ n : Measure (X × X)) {p | p.1 ≠ p.2}).toReal) atTop (𝓝 0) := by
  have hex n := exists_original_probability_variation_sampling (μ n : Measure X) (ν : Measure X)
  choose κ hf hs hb using hex
  refine ⟨κ,hf,hs,?_⟩
  apply squeeze_zero' (Filter.Eventually.of_forall fun _ ↦ ENNReal.toReal_nonneg) _ hvariation
  apply Filter.Eventually.of_forall
  intro n
  exact ENNReal.toReal_mono (measure_ne_top _ _) (hb n)

end OTSelector.Reconstruction

end
end
