import Mathlib.MeasureTheory.Function.L1Space.AEEqFun
import Mathlib.MeasureTheory.VectorMeasure.Variation.SignedMeasure
import Mathlib.MeasureTheory.VectorMeasure.WithDensityVec

/-!
## Lemma skeleton

* **Conditions:** Two finite laws represented by densities against one reference.
* **Objects:** The full signed-measure total variation and the L1 density distance.
* **Proof detail:** Use the variation formula for a signed density and identify its L1 norm.

## Mathematical sources

* Sheldon Axler, *Measure, Integration & Real Analysis (author PDF, 12 June 2026)*, Section 9A, Theorems 9.9–9.10, pp. 259–261 (total variation and density formula).
  https://measure.axler.net/MIRA.pdf#page=275

**Relationship to the sources:** The convention is full variation, not half the probability total-variation distance; quotient representatives are Lean adapters.
-/

/-!
# Total variation of the original laws from their L1 densities

The full total variation of two finite laws with a common density reference equals
the L1 distance of their density classes. The reference need not be finite, and the
nonnegative densities may take infinite values on null sets.
-/

open Set MeasureTheory
open scoped ENNReal

namespace OTSelector.Reconstruction

/-- The actual signed difference of two density laws has the L1 distance as its full
variation mass. No normalization or absolute-continuity lower bound is required. -/
theorem totalVariation_sub_eq_norm_L1_of_withDensity
    {X : Type*} [MeasurableSpace X] (τ μ ν : Measure X)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {f g : X → ℝ≥0∞} (hf : AEMeasurable f τ) (hg : AEMeasurable g τ)
    (hμ : τ.withDensity f = μ) (hν : τ.withDensity g = ν)
    (s t : Lp ℝ 1 τ)
    (hs : (⇑s) =ᵐ[τ] (fun x ↦ (f x).toReal))
    (ht : (⇑t) =ᵐ[τ] (fun x ↦ (g x).toReal)) :
    (μ.toSignedMeasure - ν.toSignedMeasure).totalVariation univ =
      ENNReal.ofReal ‖s - t‖ := by
  have hfi : (∫⁻ x, f x ∂τ) ≠ ∞ := by
    simpa only [← hμ, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
      using measure_ne_top μ univ
  have hgi : (∫⁻ x, g x ∂τ) ≠ ∞ := by
    simpa only [← hν, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
      using measure_ne_top ν univ
  have hsm : τ.withDensityᵥ (⇑s) = μ.toSignedMeasure := by
    rw [WithDensityᵥEq.congr_ae hs]
    simpa only [hμ] using withDensityᵥ_toReal hf hfi
  have htm : τ.withDensityᵥ (⇑t) = ν.toSignedMeasure := by
    rw [WithDensityᵥEq.congr_ae ht]
    simpa only [hν] using withDensityᵥ_toReal hg hgi
  rw [← hsm, ← htm, ← withDensityᵥ_sub (L1.integrable_coeFn s)
    (L1.integrable_coeFn t), SignedMeasure.totalVariation_eq_variation,
    Measure.variation_withDensityᵥ ((L1.integrable_coeFn s).sub (L1.integrable_coeFn t)),
    withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    L1.ofReal_norm_sub_eq_lintegral]
  rfl

end OTSelector.Reconstruction
