import OTSelector.MeasureTheory.FiniteMeasureNormalizationVariation
import OTSelector.Probability.FiniteClassThinning
import OTSelector.Probability.FiniteMeasureConditioning
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Reconstruction.OriginalRetainedPairKernel.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Reconstruction.OriginalRetainedPairKernel`; the selected original proof blocks follow. -/
section

/-!
# Probability.NormalizedRetainedPairKernel

## Lemma skeleton

* **Conditions:** An actual measurable pair kernel with finite sections; positive retained section mass for the evaluation formula.
* **Objects:** A measurable normalized Markov kernel and its coordinate Markov projections, equal to the original normalization on positive roots.
* **Proof detail:** Divide by the measurable section mass on its positive event and choose a fixed Dirac fallback on the null/degenerate branch; projection preserves the Markov property.

## Mathematical sources

- [D. H. Fremlin, Measure Theory, Volume 4](https://www1.essex.ac.uk/maths/people/fremlin/chap45.pdf#page=18): Section 452A–452F (integration of families and disintegrations), 452M (product disintegration).
- [D. H. Fremlin, Measure Theory, Volume 2](https://www1.essex.ac.uk/maths/people/fremlin/chap23.pdf#page=27): Sections 234I–234L, pp. 27–29; especially 234L(c); Section 235K, p. 40.

Source relation (composition): Normalization adapter for the original kernel; the fallback does not replace a positive retained conditional law.
-/

/-! Actual retained original pair kernels normalize measurably without replacing
any conditional law. A fixed null fallback is irrelevant on positive retained roots. -/
open Set Function MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false
variable {Z : Type*} [MeasurableSpace Z]

/-- The actual original retained pair normalized at its own original root. -/
def originalNormalizedRetainedPairKernel (χ : Kernel Z (ℝ × ℝ)) : Kernel Z (ℝ × ℝ) :=
  normalizedActualBinKernel χ univ MeasurableSet.univ (0,0)

instance originalNormalizedRetainedPairKernel_isMarkov
    (χ : Kernel Z (ℝ × ℝ)) [∀ z, IsFiniteMeasure (χ z)] :
    IsMarkovKernel (originalNormalizedRetainedPairKernel χ) := inferInstanceAs
      (IsMarkovKernel (normalizedActualBinKernel χ univ MeasurableSet.univ (0,0)))

instance originalNormalizedRetainedPairKernel_fst_isMarkov
    (χ : Kernel Z (ℝ × ℝ)) [∀ z, IsFiniteMeasure (χ z)] :
    IsMarkovKernel ((originalNormalizedRetainedPairKernel χ).map Prod.fst) :=
  Kernel.IsMarkovKernel.map _ measurable_fst

instance originalNormalizedRetainedPairKernel_snd_isMarkov
    (χ : Kernel Z (ℝ × ℝ)) [∀ z, IsFiniteMeasure (χ z)] :
    IsMarkovKernel ((originalNormalizedRetainedPairKernel χ).map Prod.snd) :=
  Kernel.IsMarkovKernel.map _ measurable_snd

/-- Positive retained original mass identifies the canonical normalized kernel
with the literal normalized original submeasure, including its exact total mass. -/
theorem originalNormalizedRetainedPairKernel_apply_eq
    (χ : Kernel Z (ℝ × ℝ)) [∀ z, IsFiniteMeasure (χ z)] (z : Z)
    (hpos : 0 < (χ z).real univ) :
    originalNormalizedRetainedPairKernel χ z = normalizedFiniteLaw (χ z) := by
  have hzero : χ z univ ≠ 0 := (ENNReal.toReal_pos_iff.mp hpos).1.ne'
  change (if χ z univ = 0 then Measure.dirac (0,0)
    else (χ z univ)⁻¹ • (χ z).restrict univ) = normalizedFiniteLaw (χ z)
  simp only [hzero,ite_false,Measure.restrict_univ]
  have hn := normalizedFiniteLaw_restrict_eq_cond (χ z) univ (measure_ne_top _ _)
  simpa only [Measure.restrict_univ,ProbabilityTheory.cond] using hn.symm

/-- The exact original retained mass is measurable before any original sample. -/
theorem measurable_originalRetainedPairMass (χ : Kernel Z (ℝ × ℝ)) :
    Measurable (fun z ↦ (χ z).real univ) :=
  (χ.measurable_coe MeasurableSet.univ).ennreal_toReal

end OTSelector.Reconstruction

end
end
