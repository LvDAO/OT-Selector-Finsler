import Mathlib.MeasureTheory.Measure.Support
import OTSelector.PointProcess.LocalConfiguration
import OTSelector.PointProcess.LocalConfigurationMeasure

/-!
Conditions: A metric Borel point space and the genuine locally finite shell-coded integer configuration; countability of occupied sites itself omits measurable/Borel assumptions.

Objects: Countable and closed occupied-site support, almost-everywhere concentration on it and equality with the topological support of the actual counting measure.

Proof detail: Cover occupied sites by the finite supports of integer windows, integrate each shell outside that set and use local finiteness to isolate every unoccupied site. Positive singleton mass gives the reverse support inclusion.

References: Günter Last; Mathew Penrose: Section 2.1, pp. 9–10, equations (2.1)–(2.2); multiplicities explicitly allowed on p. 10; Günter Last; Mathew Penrose: Section 2.4, Definition 2.11 and following integer-ball exhaustion criterion, p. 16.
Relation: The exact support identification is derived from this locally finite multiplicity representation and the measure-support neighborhood definition. No simplicity or diffuseness assumption is imposed.
-/

/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.PointProcess.LocalConfigurationSupport.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.PointProcess.LocalConfigurationSupport`; the selected original proof blocks follow. -/
section

/-!
# The support of an actual integer configuration

The original shell code has countably many occupied sites. They form a closed
set, and the actual counting measure is concentrated on precisely these sites.
These generic facts are shared by weighted target clouds and matching scenes.
-/

open MeasureTheory Set Function Filter Topology
open scoped Classical ENNReal

namespace OTSelector.PointProcess.LocalConfiguration

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] {base : X}

omit [MeasurableSpace X] [BorelSpace X] in
theorem countable_multiplicity_support (config : LocalConfiguration base) :
    (Function.support (multiplicity config)).Countable := by
  apply (Set.countable_iUnion (fun n ↦ (windowSupport config n).finite_toSet.countable)).mono
  intro x hx
  exact mem_iUnion.mpr ⟨shellIndex base x + 1,
    (mem_windowSupport_iff config _ x).mpr ⟨Nat.lt_succ_self _, hx⟩⟩

theorem ae_mem_multiplicity_support (config : LocalConfiguration base) :
    ∀ᵐ x ∂countingMeasure config, x ∈ Function.support (multiplicity config) := by
  rw [ae_iff]
  change countingMeasure config (Function.support (multiplicity config))ᶜ = 0
  rw [countingMeasure_apply config (countable_multiplicity_support config).measurableSet.compl]
  apply ENNReal.tsum_eq_zero.mpr
  intro n
  rw [shellMeasure_apply _ _ (countable_multiplicity_support config).measurableSet.compl]
  apply Multiset.sum_eq_zero
  intro v hv
  obtain ⟨x, hx, rfl⟩ := Multiset.mem_map.mp hv
  apply Set.indicator_of_notMem
  change ¬ ¬ multiplicity config x.val ≠ 0
  rw [multiplicity_shell]
  exact not_not.mpr (Multiset.count_ne_zero.mpr hx)

omit [MeasurableSpace X] [BorelSpace X] in
/-- Local finiteness makes the set of occupied sites closed. -/
theorem isClosed_multiplicity_support (config : LocalConfiguration base) :
    IsClosed (Function.support (multiplicity config)) := by
  have h := (locallyFiniteSupport_multiplicity config).locallyFinite_support
    (multiplicity config)
  have hc := h.isClosed_iUnion (fun _ ↦ isClosed_singleton)
  simpa only [iUnion_singleton_eq_range, Subtype.range_coe_subtype, ofPred_mem_eq] using hc

/-- The topological support of the original counting measure is exactly its
occupied-site set, with no closure or exceptional points added. -/
theorem support_countingMeasure (config : LocalConfiguration base) :
    (countingMeasure config).support = Function.support (multiplicity config) := by
  apply subset_antisymm
  · exact Measure.support_subset_of_isClosed (isClosed_multiplicity_support config)
      (ae_mem_multiplicity_support config)
  · intro x hx
    apply (Measure.mem_support_iff_forall x).mpr
    intro U hU
    have hpos : 0 < countingMeasure config {x} := by
      rw [countingMeasure_singleton]
      exact_mod_cast Nat.pos_of_ne_zero hx
    exact hpos.trans_le (measure_mono (singleton_subset_iff.mpr (mem_of_mem_nhds hU)))

end OTSelector.PointProcess.LocalConfiguration

end
