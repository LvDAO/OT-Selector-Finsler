import LeanPool.Vlasov.OT.Coupling
import Mathlib.Analysis.Convex.Birkhoff
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.GroupTheory.Perm.ViaEmbedding
import Mathlib.MeasureTheory.Measure.FiniteMeasureExt
import Mathlib.Probability.Distributions.Beta
import Mathlib.Probability.Distributions.Exponential
import Mathlib.Probability.Independence.Integration
import Mathlib.Probability.Kernel.CondDistrib
import Mathlib.Topology.Algebra.Module.Cardinality
import OTSelector.MeasureTheory.LocalFiniteMeasure
import OTSelector.MeasureTheory.LocalFiniteMeasurePolish
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Probability.CavitySemidiscreteLocalPlan.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Probability.CavitySemidiscreteLocalPlan`; the selected original proof blocks follow. -/
section

/-!
Conditions: A family of locally finite measures is measurable as an ordinary measure-valued map in the stated topology/Borel setting.

Objects: Measurability of the same family as LocalFiniteMeasure.

Proof detail: Use the measurable embedding into a standard-Borel presentation and the actual measure/test-evaluation identities.

Sources: D. H. Fremlin, Section 424B(b)–(d), 424C–424D, pp. 30–31; Section 424G, p. 31 (https://www1.essex.ac.uk/maths/people/fremlin/chap42.pdf#page=30); D. H. Fremlin, Sections 418A–418C, measurable maps, products, and limits into metrizable/Polish spaces (https://www1.essex.ac.uk/maths/people/fremlin/chap41.pdf#page=106).
Relation: Borel-presentation adapter for the locally finite-measure encoding; no density or Markov structure is asserted.
-/

/-!
# Actual semidiscrete plans in the diffuse vague carrier

The measurable measure-valued plans built from original allocation coefficients
lift to the compact-test Borel space. Finite mass is derived from the exact
source marginal, and no separate scene measurability premise is needed.
-/

open MeasureTheory Set TopologicalSpace
open scoped BigOperators ENNReal CompactlySupported

noncomputable section
namespace OTSelector.Probability

variable {V X : Type*} [MeasurableSpace V]
  [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
  [T2Space X] [LocallyCompactSpace X] [PseudoMetrizableSpace X]
  [SigmaCompactSpace X] [SecondCountableTopology X]

/-- Giry-measurable actual locally finite measures are measurable for the proved
vague Borel structure. -/
theorem measurable_localFiniteMeasure_of_measurable_measure
    (π : V → LocalFiniteMeasure X)
    (hπ : Measurable (fun v ↦ (π v : Measure X))) : Measurable π := by
  apply LocalFiniteMeasure.measurable_of_testIntegral
  intro f
  have hpos := (Measure.measurable_lintegral f.continuous.measurable.ennreal_ofReal).comp hπ
  have hneg := (Measure.measurable_lintegral
    f.continuous.measurable.neg.ennreal_ofReal).comp hπ
  have heq (v : V) : LocalFiniteMeasure.testIntegral (π v) f =
      (∫⁻ x, ENNReal.ofReal (f x) ∂(π v : Measure X)).toReal -
        (∫⁻ x, ENNReal.ofReal (-f x) ∂(π v : Measure X)).toReal :=
    integral_eq_lintegral_pos_part_sub_lintegral_neg_part f.integrable
  simp_rw [heq]
  exact hpos.ennreal_toReal.sub hneg.ennreal_toReal




end OTSelector.Probability

end
end
