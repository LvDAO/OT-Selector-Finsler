import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.Probability.Kernel.Composition.MeasureCompProd

/-!
## Lemma skeleton

* **Conditions:** Sigma-finite label and mark references; a jointly measurable nonnegative weight.
* **Objects:** The density of a weighted product law, allowing a singular label component.
* **Proof detail:** Split the label law into absolutely continuous and singular parts, apply product integration and RN uniqueness.

## Mathematical sources

* D. H. Fremlin, *Measure Theory, Volume 2*, Sections 232E–232I, Radon–Nikodym and Lebesgue decomposition; Section 235K, change of measure.
  https://www1.essex.ac.uk/maths/people/fremlin/chap23.pdf
* Sheldon Axler, *Measure, Integration & Real Analysis (author PDF, 12 June 2026)*, Section 3A (integration), Theorem 3.31 (dominated convergence); Section 5B, Theorems 5.28/5.32 (Tonelli/Fubini).
  https://measure.axler.net/MIRA.pdf

**Relationship to the sources:** The formula for rnDeriv of a weighted product is a combination; singular components are not silently discarded.
-/

/-!
# Changing the label reference of a weighted product measure

The label reference may have a singular part. Its Lebesgue decomposition still
identifies the density of every weighted product against the original label law.
No finite-value assumption on the weight or absolute continuity of the label
reference is needed.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal

namespace OTSelector.Reconstruction

/-- The density of a weighted product changes only by the label reference's
Radon–Nikodym factor, including when that reference has a singular part. -/
theorem rnDeriv_prod_withDensity
    {Z S : Type*} [MeasurableSpace Z] [MeasurableSpace S]
    (lambda β : Measure Z) [SigmaFinite lambda] [SigmaFinite β]
    (τ : Measure S) [SigmaFinite τ]
    {G : Z × S → ℝ≥0∞} (hG : Measurable G) :
    ((β.prod τ).withDensity G).rnDeriv (lambda.prod τ) =ᵐ[lambda.prod τ]
      (fun y ↦ β.rnDeriv lambda y.1 * G y) := by
  have hA : Measurable (fun y : Z × S ↦ β.rnDeriv lambda y.1) :=
    (Measure.measurable_rnDeriv β lambda).comp measurable_fst
  have hsing : (β.singularPart lambda).prod τ ⟂ₘ lambda.prod τ := by
    simpa only [Measure.compProd_const] using
      (Measure.mutuallySingular_singularPart β lambda).compProd_of_left
        (Kernel.const Z τ) (Kernel.const Z τ)
  refine (Measure.eq_rnDeriv (μ := (β.prod τ).withDensity G)
    (s := ((β.singularPart lambda).prod τ).withDensity G)
    (hA.mul hG) hsing.withDensity ?_).symm
  calc
    (β.prod τ).withDensity G =
        ((β.singularPart lambda + lambda.withDensity (β.rnDeriv lambda)).prod τ).withDensity G := by
      congr 2
      exact β.haveLebesgueDecomposition_add lambda
    _ = ((β.singularPart lambda).prod τ).withDensity G +
        (lambda.prod τ).withDensity (fun y ↦ β.rnDeriv lambda y.1 * G y) := by
      rw [Measure.add_prod, withDensity_add_measure,
        prod_withDensity_left (Measure.measurable_rnDeriv β lambda),
        ← withDensity_mul _ hA hG]
      rfl

end OTSelector.Reconstruction
