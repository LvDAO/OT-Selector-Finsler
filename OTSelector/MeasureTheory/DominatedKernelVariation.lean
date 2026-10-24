import Mathlib.Probability.Kernel.RadonNikodym
import OTSelector.MeasureTheory.WeightedKernelVariation
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Reconstruction.DensityKernelVariationDominated.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Reconstruction.DensityKernelVariationDominated`; the selected original proof blocks follow. -/
section

/-!
# MeasureTheory.DominatedKernelVariation

## Lemma skeleton

* **Conditions:** Finite original root law with measurable density weight, Markov mark kernel and a probability frozen mark law both absolutely continuous relative to a common SFinite reference; target sigma-algebra is countably generated.
* **Objects:** Full variation bound for the weighted original composition product without pre-supplied joint density functions.
* **Proof detail:** Use the measurable kernel RN theorem to obtain actual joint/section densities, then apply the weighted intensity-plus-mark variation estimate.

## Mathematical sources

- [D. H. Fremlin, Measure Theory, Volume 2](https://www1.essex.ac.uk/maths/people/fremlin/chap23.pdf): Sections 232E–232I, Radon–Nikodym and Lebesgue decomposition; Section 235K, change of measure.
- [D. H. Fremlin, Measure Theory, Volume 4](https://www1.essex.ac.uk/maths/people/fremlin/chap45.pdf#page=18): Section 452A–452F (integration of families and disintegrations), 452M (product disintegration).
- [Sheldon Axler, Measure, Integration & Real Analysis (author PDF, 12 June 2026)](https://measure.axler.net/MIRA.pdf#page=275): Section 9A, Theorems 9.9–9.10, pp. 259–261 (total variation and density formula).
- [D. H. Fremlin, Measure Theory, Volume 2](https://www1.essex.ac.uk/maths/people/fremlin/chap25.pdf#page=19): Theorems 252B–252C (Fubini) and 252G–252H (Tonelli), pp. 19–25.

Source relation (composition): Dominated-kernel extension of the density variation estimate; countable generation is used for the kernel density theorem.
-/

/-!
# Raw variation under an original dominating measure

Joint measurable densities are supplied by the kernel Radon--Nikodym theorem.
-/

open Set MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace OTSelector.Reconstruction

/-- Absolute continuity of the original marks supplies the joint measurable
Radon--Nikodym density needed for the unnormalized freezing estimate. -/
theorem totalVariation_weighted_compProd_le_of_absolutelyContinuous
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    [MeasurableSpace.CountablyGenerated Y]
    (μ : Measure X) [IsFiniteMeasure μ] (τ : Measure Y) [SFinite τ]
    (k : Kernel X Y) [IsMarkovKernel k]
    (ν : Measure Y) [IsProbabilityMeasure ν]
    {ρ : X → ℝ≥0∞} [IsFiniteMeasure (μ.withDensity ρ)]
    (hρ : Measurable ρ) (hk : ∀ᵐ x ∂μ, k x ≪ τ) (hν : ν ≪ τ)
    {ρ₀ η : ℝ} (hρ₀ : 0 ≤ ρ₀) (hη : 0 ≤ η)
    (hclose : ∀ᵐ x ∂μ, |(ρ x).toReal - ρ₀| ≤ η * ρ₀)
    (hmark : ∀ᵐ x ∂μ,
      ((k x).toSignedMeasure - ν.toSignedMeasure).totalVariation univ ≤ ENNReal.ofReal η) :
    ((μ.withDensity ρ ⊗ₘ k).toSignedMeasure -
      (ρ₀.toNNReal • μ.prod ν).toSignedMeasure).totalVariation univ ≤
      ENNReal.ofReal (2 * η * ρ₀) * μ univ := by
  obtain ⟨τ', hτ', hττ', _⟩ := exists_isFiniteMeasure_absolutelyContinuous τ
  let : IsFiniteMeasure τ' := hτ'
  let ref : Kernel X Y := Kernel.const X τ'
  have hdensity : ∀ᵐ x ∂μ, τ'.withDensity (k.rnDeriv ref x) = k x := by
    filter_upwards [hk] with x hx
    have he := Kernel.withDensity_rnDeriv_eq (κ := k) (η := ref) (hx.trans hττ')
    simpa only [Kernel.withDensity_apply ref (k.measurable_rnDeriv ref), ref,
      Kernel.const_apply] using he
  exact totalVariation_weighted_compProd_le μ τ' k ν hρ
    (k.measurable_rnDeriv ref) (Measure.measurable_rnDeriv ν τ') hdensity
    (ν.withDensity_rnDeriv_eq τ' (hν.trans hττ')) hρ₀ hη hclose hmark

end OTSelector.Reconstruction

end
