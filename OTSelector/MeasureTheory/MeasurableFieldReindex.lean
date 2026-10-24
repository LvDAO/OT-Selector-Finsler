import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousLinearMap
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable
import Mathlib.Tactic
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Reconstruction.MeasurablePhaseFieldReindex.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Reconstruction.MeasurablePhaseFieldReindex`; the selected original proof blocks follow. -/
section

/-!
# MeasureTheory.MeasurableFieldReindex

## Lemma skeleton

* **Conditions:** A jointly measurable field and measurable maps reindexing its environment and optionally its spatial argument.
* **Objects:** Joint measurability of the reindexed field and measurability of its evaluated readout.
* **Proof detail:** Compose the original uncurried field with the product of the measurable reindexing map and the identity or supplied argument.

## Mathematical sources

- [D. H. Fremlin, Measure Theory, Volume 4, Appendix](https://www1.essex.ac.uk/maths/people/fremlin/chap4a.pdf#page=32): Sections 4A3B(a)–(c), p. 32; 4A3C(a)–(f), pp. 32–33.

Source relation (composition): Measurable composition adapter retaining the full environment; no stationarity or conditional law is asserted.
-/

/-! Reindexing an unchanged jointly measurable field retains all environment parameters. -/
open MeasureTheory
namespace OTSelector.Reconstruction

/-- Reindex only the original environment, retaining the original observation point. -/
theorem measurable_phaseField_reindex
    {Ω : Type*} {Γ : Type*} {V : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Γ] [MeasurableSpace V]
    {P : Ω→V→V} (hP : Measurable (Function.uncurry P))
    {r : Γ→Ω} (hr : Measurable r) :
    Measurable (Function.uncurry (fun γ ↦ P (r γ))) :=
  hP.comp ((hr.comp measurable_fst).prodMk measurable_snd)

/-- Evaluate the same original joint field on measurable environment and point readouts. -/
theorem measurable_phaseField_apply
    {Ω : Type*} {Γ : Type*} {V : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Γ] [MeasurableSpace V]
    {P : Ω→V→V} (hP : Measurable (Function.uncurry P))
    {r : Γ→Ω} (hr : Measurable r) {z : Γ→V} (hz : Measurable z) :
    Measurable (fun γ ↦ P (r γ) (z γ)) := hP.comp (hr.prodMk hz)

end OTSelector.Reconstruction

end
