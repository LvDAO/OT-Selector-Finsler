import Mathlib.MeasureTheory.Measure.SubFinite
import Mathlib.MeasureTheory.VectorMeasure.Decomposition.JordanSub
import Mathlib.MeasureTheory.VectorMeasure.Variation.SignedMeasure
import Mathlib.Tactic
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Reconstruction.OriginalVariationObservation.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Reconstruction.OriginalVariationObservation`; the selected original proof blocks follow. -/
section

/-!
# MeasureTheory.VariationObservation

## Lemma skeleton

* **Conditions:** Two finite measures and a measurable observation; equality of variation additionally requires a measurable embedding.
* **Objects:** Signed difference pushforward, contraction of full variation and equality under an embedding.
* **Proof detail:** Commute finite signed conversion with map. Pull target partitions back for contraction; measurable inverse images of source partitions under an embedding give the reverse bound.

## Mathematical sources

- [Sheldon Axler, Measure, Integration & Real Analysis (author PDF, 12 June 2026)](https://measure.axler.net/MIRA.pdf#page=275): Section 9A, Theorems 9.9–9.10, pp. 259–261 (total variation and density formula).
- [D. H. Fremlin, Measure Theory, Volume 2](https://www1.essex.ac.uk/maths/people/fremlin/chap23.pdf): Section 235G, integration along an inverse-measure-preserving map.

Source relation (composition): Full signed variation, with no probability normalization or invertibility of a general observation.
-/

/-! Signed variation under exact original measurable observations. A compact
clock-range lift preserves variation, and arbitrary observations contract it. -/
open Set Function MeasureTheory Filter
open scoped Topology ENNReal
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000
set_option linter.style.haveILetI false

/-- The signed difference of observed original laws is their observed signed
difference, using the actual measures on both sides. -/
theorem original_signed_difference_map
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (μ ν : Measure X) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (f : X → Y) (hf : Measurable f) :
    (μ.map f).toSignedMeasure - (ν.map f).toSignedMeasure =
      (μ.toSignedMeasure - ν.toSignedMeasure).map f := by
  ext S hS
  simp only [_root_.sub_apply,Measure.toSignedMeasure_apply_measurable hS,
    VectorMeasure.map_apply _ hf hS,Measure.toSignedMeasure_apply_measurable (hf hS),
    map_measureReal_apply hf hS]

/-- Observing original laws cannot increase their actual signed variation. -/
theorem original_totalVariation_real_map_le
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (μ ν : Measure X) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (f : X → Y) (hf : Measurable f) :
    ((μ.map f).toSignedMeasure - (ν.map f).toSignedMeasure).totalVariation.real univ ≤
      (μ.toSignedMeasure - ν.toSignedMeasure).totalVariation.real univ := by
  rw [original_signed_difference_map μ ν f hf]
  simp only [SignedMeasure.totalVariation_eq_variation]
  letI : IsFiniteMeasure (μ.toSignedMeasure - ν.toSignedMeasure).variation := by
    rw [← SignedMeasure.totalVariation_eq_variation]
    infer_instance
  have hb := ENNReal.toReal_mono (measure_ne_top ((μ.toSignedMeasure - ν.toSignedMeasure).variation.map f) univ)
    (VectorMeasure.variation_map_le (μ := μ.toSignedMeasure - ν.toSignedMeasure) (φ := f) univ)
  rw [← measureReal_def,← measureReal_def,map_measureReal_apply hf MeasurableSet.univ,preimage_univ] at hb
  exact hb

/-- An exact measurable embedding of original marks preserves signed
variation; in particular a compact scalar-range lift loses no law accuracy. -/
theorem original_totalVariation_real_map_eq
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (μ ν : Measure X) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (f : X → Y) (hf : MeasurableEmbedding f) :
    ((μ.map f).toSignedMeasure - (ν.map f).toSignedMeasure).totalVariation.real univ =
      (μ.toSignedMeasure - ν.toSignedMeasure).totalVariation.real univ := by
  rw [original_signed_difference_map μ ν f hf.measurable]
  simp only [SignedMeasure.totalVariation_eq_variation,hf.variation_map,
    map_measureReal_apply hf.measurable MeasurableSet.univ,preimage_univ]

end OTSelector.Reconstruction

end
end
