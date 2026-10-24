import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.WithDensity
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Reconstruction.ClockReflectedBandMass.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Reconstruction.ClockReflectedBandMass`; the selected original proof blocks follow. -/
section

/-!
# MeasureTheory.ClockReflectedBandMass

## Lemma skeleton

* **Conditions:** An arbitrary original scalar measure, a clock origin/upper endpoint and half-open bands; a product bound has the displayed SFinite factor hypothesis.
* **Objects:** Exact translation and right-inward-reflection preimage formulas and rectangle band bounds.
* **Proof detail:** Compute affine interval preimages, reversing Ioc to Ico under reflection, then evaluate the original pushforward and product rectangle measure.

## Mathematical sources

- [D. H. Fremlin, Measure Theory, Volume 2](https://www1.essex.ac.uk/maths/people/fremlin/chap23.pdf): Section 235G, integration along an inverse-measure-preserving map.
- [D. H. Fremlin, Measure Theory, Volume 2](https://www1.essex.ac.uk/maths/people/fremlin/chap25.pdf#page=2): Sections 251A–251I, pp. 2–6: rectangular covers, product outer measures and the product-measure rectangle formula.

Source relation (composition): Exact coordinate and boundary bookkeeping; no physical endpoint is discarded.
-/

/-! Exact original clock coordinates for inward right-end half-open bands.
The reflected physical band is Ico and no actual endpoint is discarded. -/
open Set MeasureTheory
open scoped ENNReal
noncomputable section
namespace OTSelector.Reconstruction

/-- Relative reflected half-open bands are the same original absolute bands. -/
theorem map_clock_sub_Ico (σ : Measure ℝ) (level a b : ℝ) :
    (σ.map (fun x : ℝ ↦ x - level)) (Ico a b) = σ (Ico (level + a) (level + b)) := by
  rw [Measure.map_apply (show Measurable (fun x : ℝ ↦ x - level) by fun_prop) measurableSet_Ico]
  congr 1
  ext x
  change (a ≤ x - level ∧ x - level < b) ↔ (level + a ≤ x ∧ x < level + b)
  constructor <;> intro hx <;> constructor <;> linarith [hx.1, hx.2]

/-- The original right-inward Ioc band is exactly its reflected physical Ico
band; this identity is pointwise and does not need an atomlessness premise. -/
theorem map_clock_right_inward_Ioc (σ : Measure ℝ) (level hi a b : ℝ) :
    (σ.map (fun x : ℝ ↦ hi - (x - level))) (Ioc a b) =
      σ (Ico (level + hi - b) (level + hi - a)) := by
  rw [Measure.map_apply (show Measurable (fun x : ℝ ↦ hi - (x - level)) by fun_prop)
    measurableSet_Ioc]
  congr 1
  ext x
  change (a < hi - (x - level) ∧ hi - (x - level) ≤ b) ↔
    (level + hi - b ≤ x ∧ x < level + hi - a)
  constructor <;> intro hx <;> constructor <;> linarith [hx.1, hx.2]

/-- The literal original reflected-band spatial intensity retains exactly its
physical Haar factor and original target clock law. -/
theorem prod_clock_sub_Ico_le {X : Type*} [MeasurableSpace X]
    (κ : Measure X) (σ : Measure ℝ) [SFinite σ] (A : Set X) {level a b B : ℝ}
    (hband : (σ.map (fun x : ℝ ↦ x - level)) (Ico a b) ≤ ENNReal.ofReal B) :
    κ.prod σ (A ×ˢ Ico (level + a) (level + b)) ≤ κ A * ENNReal.ofReal B := by
  rw [Measure.prod_prod, ← map_clock_sub_Ico]
  gcongr

end OTSelector.Reconstruction

end
end
