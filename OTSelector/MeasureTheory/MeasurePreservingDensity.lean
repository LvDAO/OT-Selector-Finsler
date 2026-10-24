import Mathlib.MeasureTheory.Measure.WithDensity

/-!
## Lemma skeleton

* **Conditions:** A measure-preserving map and a measurable nonnegative density.
* **Objects:** The weighted pushforward measure.
* **Proof detail:** Test against nonnegative measurable functions and apply change of variables.

## Mathematical sources

* D. H. Fremlin, *Measure Theory, Volume 2*, Section 235G, integration along an inverse-measure-preserving map.
  https://www1.essex.ac.uk/maths/people/fremlin/chap23.pdf
* D. H. Fremlin, *Measure Theory, Volume 2*, Sections 232E–232I, Radon–Nikodym and Lebesgue decomposition; Section 235K, change of measure.
  https://www1.essex.ac.uk/maths/people/fremlin/chap23.pdf

**Relationship to the sources:** The withDensity/map equation is the formal weighted change-of-variables corollary.
-/

/-!
# Transporting a density along a measure-preserving map

This common change-of-variables lemma is used by both exponential occupation and
the simplex total-mass coordinates.
-/

open MeasureTheory
open scoped ENNReal

namespace OTSelector

theorem map_withDensity_comp_of_measurePreserving
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {ν : Measure β} {T : α → β} (hT : MeasurePreserving T μ ν)
    {f : β → ℝ≥0∞} (hf : Measurable f) :
    (μ.withDensity (f ∘ T)).map T = ν.withDensity f := by
  refine Measure.ext_of_lintegral _ fun φ hφ ↦ ?_
  rw [lintegral_map hφ hT.measurable]
  change (∫⁻ a, (φ ∘ T) a ∂μ.withDensity (f ∘ T)) = ∫⁻ a, φ a ∂ν.withDensity f
  rw [lintegral_withDensity_eq_lintegral_mul _ (hf.comp hT.measurable) (hφ.comp hT.measurable),
    lintegral_withDensity_eq_lintegral_mul _ hf hφ]
  exact hT.lintegral_comp (hf.mul hφ)

end OTSelector
