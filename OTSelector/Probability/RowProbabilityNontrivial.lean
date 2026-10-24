import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import OTSelector.Probability.RowProbabilityFilter

/-!
Conditions: Every row measure is a probability, on its own measurable sample space.

Objects: A NeBot instance for the previously constructed row-probability filter.

Proof detail: The impossible eventual predicate has failure probability one in every row, so cannot meet the vanishing-failure definition.

References: D. H. Fremlin: Section 245, especially 245A–245E, convergence in measure and its topology.
Relation: A normalization-sensitive local filter fact. Finite row measures alone cannot give this conclusion when their total masses tend to zero.
-/


/-!
# Nontriviality of the probability-row filter

Probability row laws give a nontrivial filter: the impossible event has failure probability one,
so it cannot hold eventually. This is needed to reconstruct a limiting measure from compactness.
Finite row measures alone do not suffice, since their total masses could tend to zero.
-/

open Filter MeasureTheory Set
open scoped Topology

namespace OTSelector.Probability

/-- Row laws of total mass one make convergence in row probability a nontrivial filter. -/
instance rowProbabilityFilter_neBot {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (P : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (P n)] :
    NeBot (rowProbabilityFilter P) := by
  refine ⟨fun hbot ↦ ?_⟩
  have hempty : (∅ : Set (Σ n, Ω n)) ∈ rowProbabilityFilter P :=
    empty_mem_iff_bot.mpr hbot
  simp [rowProbabilityFilter] at hempty

end OTSelector.Probability
