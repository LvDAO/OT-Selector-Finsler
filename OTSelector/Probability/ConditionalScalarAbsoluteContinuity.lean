import Mathlib.MeasureTheory.Measure.WithDensityFinite
import Mathlib.Probability.Kernel.Composition.AbsolutelyContinuous
import Mathlib.Probability.Kernel.CondDistrib
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Reconstruction.ConditionalScalarAbsoluteContinuity.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Reconstruction.ConditionalScalarAbsoluteContinuity`; the selected original proof blocks follow. -/
section

/-!
# Probability.ConditionalScalarAbsoluteContinuity

## Lemma skeleton

* **Conditions:** A finite original measure and joint label-clock absolute continuity against its own label marginal times scalar volume.
* **Objects:** Almost-everywhere Lebesgue absolute continuity of the actual scalar conditional distributions and their mapped physical-kernel version.
* **Proof detail:** Replace volume by an equivalent finite positive reference, apply uniqueness and absolute-continuity transfer for disintegrations, then use conditional pushforward identities.

## Mathematical sources

- [D. H. Fremlin, Measure Theory, Volume 4](https://www1.essex.ac.uk/maths/people/fremlin/chap45.pdf#page=18): Section 452A–452F (integration of families and disintegrations), 452M (product disintegration).
- [D. H. Fremlin, Measure Theory, Volume 2](https://www1.essex.ac.uk/maths/people/fremlin/chap23.pdf): Sections 232E–232I, Radon–Nikodym and Lebesgue decomposition; Section 235K, change of measure.

Source relation (composition): Conditional absolute-continuity corollary; the finite equivalent reference does not change the null sets.
-/

/-!
# Scalar conditional absolute continuity from the actual joint law

An original joint label-clock law dominated by its own label marginal times Lebesgue
measure has Lebesgue absolutely continuous scalar conditional laws. An equivalent
finite reference measure lets the existing finite-kernel disintegration theorem apply.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal

namespace OTSelector.Reconstruction

variable {M Z : Type*} [MeasurableSpace M] [MeasurableSpace Z]

/-- Joint absolute continuity implies absolute continuity of the actual scalar
conditional distribution at almost every original label. -/
theorem ae_condDistrib_clock_absolutelyContinuous_of_joint
    (ν : Measure M) [IsFiniteMeasure ν] {a : M → Z} {u : M → ℝ}
    (hu : Measurable u)
    (hjoint : ν.map (fun x ↦ (a x, u x)) ≪ (ν.map a).prod volume) :
    ∀ᵐ z ∂ν.map a, condDistrib u a ν z ≪ volume := by
  have href : (ν.map a).prod volume ≪ (ν.map a).prod (volume : Measure ℝ).toFinite :=
    Measure.AbsolutelyContinuous.rfl.prod (absolutelyContinuous_toFinite volume)
  have hcomp := hjoint.trans href
  rw [← compProd_map_condDistrib hu.aemeasurable, ← Measure.compProd_const] at hcomp
  filter_upwards [hcomp.kernel_of_compProd] with z hz
  exact hz.trans (toFinite_absolutelyContinuous volume)

/-- The clock pushforward of the original conditional position law is absolutely
continuous, using the same original label law as the joint representation. -/
theorem ae_condDistrib_map_clock_absolutelyContinuous_of_joint
    [StandardBorelSpace M] [Nonempty M]
    (ν : Measure M) [IsFiniteMeasure ν] {a : M → Z} {u : M → ℝ}
    (hu : Measurable u)
    (hjoint : ν.map (fun x ↦ (a x, u x)) ≪ (ν.map a).prod volume) :
    ∀ᵐ z ∂ν.map a, (condDistrib id a ν z).map u ≪ volume := by
  have heq := condDistrib_comp (mβ := inferInstance) (Y := id) a
    (measurable_id.aemeasurable : AEMeasurable (id : M → M) ν) hu
  filter_upwards [ae_condDistrib_clock_absolutelyContinuous_of_joint ν hu hjoint, heq]
    with z hz he
  simp only [Function.comp_id, Kernel.map_apply _ hu] at he
  rw [← he]
  exact hz

end OTSelector.Reconstruction

end
