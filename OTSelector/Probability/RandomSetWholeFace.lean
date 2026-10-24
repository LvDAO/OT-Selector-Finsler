import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import OTSelector.Probability.RowProbabilityFilter

/-!
Conditions: Arbitrary source filter and sets of probability measures with a given candidate limit; the row corollaries need only finite row measures and use real outer measures of arbitrary failure sets.

Objects: Equivalence between whole-set weak-neighborhood convergence and uniform error of every bounded-continuous test over every member of each set.

Proof detail: Use the weak topology as the initial bounded-test topology, push principal filters of the whole sets through filter bind, and unfold the row-probability eventual-event characterization.

References: D. H. Fremlin: Sections 437J(d),(f),(g), 437K–437L, PDF p. 61 onward; D. H. Fremlin: Section 245, especially 245A–245E, convergence in measure and its topology.
Relation: A filter/topology reformulation for entire faces. It imposes no nonemptiness, metrization, countable test family or measurable optimizer choice, and does not construct the candidate limiting measure.
-/

/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Limit.WholeFace.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Limit.WholeFace`; the selected original proof blocks follow. -/
section

/-!
# Weak convergence of an entire face of probability measures

Uniform convergence of every bounded-continuous test integral is exactly convergence of
the full sets to the small-sets filter of a weak neighborhood filter. The proof uses the
principal-filter bind and works for an arbitrary source filter; no countable-generation,
metrizability, nonemptiness, or measurable optimizer choice is assumed.

For varying sample spaces, the failure event quantifies over every member of the face.
Its real measure is allowed on arbitrary sets, so the row corollary is an outer-measure
statement without a measurability assumption on the set-valued map.

The limit measure is given. This module proves no geometric pressure limits or existence
of the limiting measure.
-/

open Filter MeasureTheory Set
open scoped Topology BoundedContinuousFunction

namespace OTSelector.WholeFace

variable {E : Type*} [TopologicalSpace E] [MeasurableSpace E] [OpensMeasurableSpace E]

/-- Weak convergence of whole sets is equivalent to uniform convergence of every bounded
continuous test integral. The source filter is arbitrary. -/
theorem tendsto_smallSets_iff_forall_integral
    {ι : Type*} (face : ι → Set (ProbabilityMeasure E)) (l : Filter ι)
    (ν : ProbabilityMeasure E) :
    Tendsto face l (𝓝 ν).smallSets ↔
      ∀ (f : E →ᵇ ℝ) (ε : ℝ), 0 < ε → ∀ᶠ z in l, ∀ μ ∈ face z,
        |(∫ x, f x ∂(μ : Measure E)) - ∫ x, f x ∂(ν : Measure E)| < ε := by
  have hbind : Tendsto face l (𝓝 ν).smallSets ↔
      Tendsto (id : ProbabilityMeasure E → ProbabilityMeasure E)
        ((map face l).bind principal) (𝓝 ν) := by
    rw [tendsto_id']
    exact (bind_smallSets_gc (map face l) (𝓝 ν)).symm
  rw [hbind, ProbabilityMeasure.tendsto_iff_forall_integral_tendsto]
  simp only [Metric.tendsto_nhds, eventually_bind, eventually_map,
    eventually_principal, Real.dist_eq, id_eq]

/-- Uniform test bounds imply convergence of every member of the face simultaneously. -/
theorem tendsto_smallSets_of_forall_integral
    {ι : Type*} {l : Filter ι} (face : ι → Set (ProbabilityMeasure E))
    (ν : ProbabilityMeasure E)
    (htest : ∀ (f : E →ᵇ ℝ) (ε : ℝ), 0 < ε → ∀ᶠ z in l, ∀ μ ∈ face z,
      |(∫ x, f x ∂(μ : Measure E)) - ∫ x, f x ∂(ν : Measure E)| < ε) :
    Tendsto face l (𝓝 ν).smallSets :=
  (tendsto_smallSets_iff_forall_integral face l ν).mpr htest

/-- On row sample spaces, whole-face weak convergence is exactly vanishing outer failure
probability for every bounded continuous test. No member of the face is preselected. -/
theorem tendsto_smallSets_rowProbabilityFilter_iff
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (P : ∀ n, Measure (Ω n)) [∀ n, IsFiniteMeasure (P n)]
    (face : (Σ n, Ω n) → Set (ProbabilityMeasure E)) (ν : ProbabilityMeasure E) :
    Tendsto face (Probability.rowProbabilityFilter P) (𝓝 ν).smallSets ↔
      ∀ (f : E →ᵇ ℝ) (ε : ℝ), 0 < ε →
        Tendsto (fun n ↦ (P n).real {ω | ∃ μ ∈ face ⟨n, ω⟩,
          ε ≤ |(∫ x, f x ∂(μ : Measure E)) - ∫ x, f x ∂(ν : Measure E)|})
          atTop (𝓝 0) := by
  rw [tendsto_smallSets_iff_forall_integral]
  simp only [Probability.eventually_rowProbabilityFilter_iff,
    not_forall, not_lt, exists_prop]

/-- Uniform test convergence controls the event that any face member leaves a fixed weak
neighborhood. Arbitrary failure sets retain their outer-measure interpretation. -/
theorem tendsto_measureReal_exists_notMem_of_forall_integral
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (P : ∀ n, Measure (Ω n)) [∀ n, IsFiniteMeasure (P n)]
    (face : (Σ n, Ω n) → Set (ProbabilityMeasure E)) (ν : ProbabilityMeasure E)
    (htest : ∀ (f : E →ᵇ ℝ) (ε : ℝ), 0 < ε →
      Tendsto (fun n ↦ (P n).real {ω | ∃ μ ∈ face ⟨n, ω⟩,
        ε ≤ |(∫ x, f x ∂(μ : Measure E)) - ∫ x, f x ∂(ν : Measure E)|})
        atTop (𝓝 0))
    (U : Set (ProbabilityMeasure E)) (hU : U ∈ 𝓝 ν) :
    Tendsto (fun n ↦ (P n).real {ω | ∃ μ ∈ face ⟨n, ω⟩, μ ∉ U})
      atTop (𝓝 0) := by
  have hface := (tendsto_smallSets_rowProbabilityFilter_iff P face ν).mpr htest
  have hevent := (Filter.tendsto_smallSets_iff.mp hface) U hU
  have hprob := (Probability.eventually_rowProbabilityFilter_iff P _).mp hevent
  simpa only [Set.subset_def, not_forall, exists_prop] using hprob

end OTSelector.WholeFace

end
