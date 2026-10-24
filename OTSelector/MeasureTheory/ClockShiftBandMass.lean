import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.WithDensity
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Reconstruction.ClockShiftBandMass.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Reconstruction.ClockShiftBandMass`; the selected original proof blocks follow. -/
section

/-!
# MeasureTheory.ClockShiftBandMass

## Lemma skeleton

* **Conditions:** An arbitrary real clock measure and a scalar origin shift; rectangle bound additionally uses the stated SFinite clock factor and an actual shifted band bound.
* **Objects:** Exact Ioc clock preimage identity and its product-rectangle mass bound.
* **Proof detail:** Compute the translation preimage of the half-open interval, apply map evaluation and the product rectangle formula, then the supplied band bound.

## Mathematical sources

- [D. H. Fremlin, Measure Theory, Volume 2](https://www1.essex.ac.uk/maths/people/fremlin/chap23.pdf): Section 235G, integration along an inverse-measure-preserving map.
- [D. H. Fremlin, Measure Theory, Volume 2](https://www1.essex.ac.uk/maths/people/fremlin/chap25.pdf#page=2): Sections 251A–251I, pp. 2–6: rectangular covers, product outer measures and the product-measure rectangle formula.

Source relation (composition): Direct measurable coordinate translation preserving the original clock measure.
-/

/-! A clock-origin change rewrites the original physical clock measure exactly. -/
open Set MeasureTheory
open scoped ENNReal
noncomputable section
namespace OTSelector.Reconstruction

/-- Relative half-open clock bands are the same original absolute-clock bands. -/
theorem map_clock_sub_Ioc (σ : Measure ℝ) (level a b : ℝ) :
    (σ.map (fun x : ℝ ↦ x - level)) (Ioc a b) = σ (Ioc (level + a) (level + b)) := by
  rw [Measure.map_apply (show Measurable (fun x : ℝ ↦ x - level) by fun_prop) measurableSet_Ioc]
  congr 1
  ext x
  change (a < x - level ∧ x - level ≤ b) ↔ (level + a < x ∧ x ≤ level + b)
  constructor <;> intro hx <;> constructor <;> linarith [hx.1, hx.2]

/-- The original physical product intensity of a spatial window times a relative
clock band keeps the exact Haar factor and the unchanged clock law. -/
theorem prod_clock_sub_Ioc_le {X : Type*} [MeasurableSpace X]
    (κ : Measure X) (σ : Measure ℝ) [SFinite σ] (A : Set X) {level a b B : ℝ}
    (hband : (σ.map (fun x : ℝ ↦ x - level)) (Ioc a b) ≤ ENNReal.ofReal B) :
    κ.prod σ (A ×ˢ Ioc (level + a) (level + b)) ≤ κ A * ENNReal.ofReal B := by
  rw [Measure.prod_prod, ← map_clock_sub_Ioc]
  gcongr

end OTSelector.Reconstruction

end
end
