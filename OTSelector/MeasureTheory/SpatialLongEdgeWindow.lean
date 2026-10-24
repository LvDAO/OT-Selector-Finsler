import LeanPool.Vlasov.OT.Coupling
import Mathlib.Analysis.Convex.Birkhoff
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.MeasureTheory.Integral.Regular
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
import Mathlib.MeasureTheory.Measure.FiniteMeasureExt
import Mathlib.MeasureTheory.Measure.Support
import Mathlib.Probability.Distributions.Beta
import Mathlib.Probability.Distributions.Exponential
import Mathlib.Probability.Independence.Integration
import Mathlib.Probability.Kernel.CondDistrib
import Mathlib.Tactic
import Mathlib.Topology.Algebra.Module.Cardinality
import Mathlib.Topology.ContinuousMap.SecondCountableSpace
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Probability.CavitySemidiscreteEscapeMass.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Probability.CavitySemidiscreteEscapeMass`; the selected original proof blocks follow. -/
section

/-!
Conditions: A measurable spatial window and an extended nonnegative edge-length threshold.

Objects: The marked product-space long-edge window and its measurability.

Proof detail: Intersect the source spatial preimage with the measurable extended-distance threshold set.

Sources: D. H. Fremlin, Sections 418A–418C, measurable maps, products, and limits into metrizable/Polish spaces (https://www1.essex.ac.uk/maths/people/fremlin/chap41.pdf#page=106); D. H. Fremlin, Sections 4A3B(a)–(c), p. 32; 4A3C(a)–(f), pp. 32–33 (https://www1.essex.ac.uk/maths/people/fremlin/chap4a.pdf#page=32).
Relation: A measurable-window definition/adapter; no escape-mass or tail theorem from the original file is covered.
-/

/-!
# Actual rooted long-edge mass from original transport energy

The source-window tail is read from the full original allocation plan. Translating
both endpoints leaves displacement unchanged, so the Haar root estimate controls
escape in the noncompact target coordinate.
-/

open MeasureTheory Set
open scoped ENNReal Classical

noncomputable section
namespace OTSelector.Probability

variable {ι A B : Type*} [Fintype ι] [MeasurableSpace A] [MeasurableSpace B]

/-- Actual source-window edges whose squared spatial displacement exceeds a threshold. -/
def cavityLongEdgeWindow (U : Set (ι → ℝ)) (r : ℝ≥0∞) :
    Set (((ι → ℝ) × A) × ((ι → ℝ) × B)) :=
  {e | e.1.1 ∈ U ∧ r ≤ ENNReal.ofReal (‖e.2.1 - e.1.1‖ ^ 2)}

theorem measurableSet_cavityLongEdgeWindow {U : Set (ι → ℝ)} (hU : MeasurableSet U)
    (r : ℝ≥0∞) : MeasurableSet (cavityLongEdgeWindow (A := A) (B := B) U r) :=
  (hU.preimage measurable_fst.fst).inter
    (measurableSet_le measurable_const
      ((measurable_snd.fst.sub measurable_fst.fst).norm.pow_const 2).ennreal_ofReal)





end OTSelector.Probability

end
end
