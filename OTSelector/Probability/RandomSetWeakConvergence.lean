import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Topology.MetricSpace.Basic

/-!
# Random Set Weak Convergence

Conditions: A topological space, a distinguished point π, a readout d with d(π,π)=0 and positive-radius open balls around π; neighborhood escape probabilities vanish for the given random sets.

Objects: Vanishing outer probability that some selected point has d-distance above a fixed positive threshold.

Proof detail: Use the corresponding open ball as one of the assumed neighborhoods and compare the two escape events.

Relation to primary sources: An elementary neighborhood specialization. The actual d is not assumed to satisfy every metric axiom, and no extra measurability of the random set is required.

References:
* D. H. Fremlin, Measure Theory, Volume 4, Sections 437J(d),(f),(g), 437K–437L, PDF p. 61 onward. https://www1.essex.ac.uk/maths/people/fremlin/chap43.pdf#page=61
-/
/-!
# From weak-neighborhood convergence to metric supremum convergence

The selector endpoint states that the empirical optimal face eventually lies in
every weak neighborhood of the limit, in outer probability.  A metric inducing
weak convergence turns open balls into such neighborhoods, giving the
paper-literal `sup d_weak -> 0` statement.
-/

open Filter MeasureTheory Set Topology
open scoped Topology ENNReal

noncomputable section
namespace OTSelector

/-- Weak-neighborhood convergence of a random face implies convergence of the
metric distance of the face from the limit, in outer probability. -/
theorem tendsto_measureReal_exists_metric_le_of_forall_nhds
    {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (P : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (P n)]
    (face : (n : ℕ) → Ω n → Set (ProbabilityMeasure X))
    (π : ProbabilityMeasure X)
    (d : ProbabilityMeasure X → ProbabilityMeasure X → ℝ)
    (hd0 : d π π = 0)
    (hdopen : ∀ ε : ℝ, 0 < ε → IsOpen {γ : ProbabilityMeasure X | d γ π < ε})
    (hface : ∀ U ∈ 𝓝 π, Tendsto (fun n ↦ (P n).real
      {ω | ∃ γ ∈ face n ω, γ ∉ U}) atTop (𝓝 0)) :
    ∀ ε : ℝ, 0 < ε → Tendsto (fun n ↦ (P n).real
      {ω | ∃ γ ∈ face n ω, ε ≤ d γ π}) atTop (𝓝 0) := by
  intro ε hε
  let U : Set (ProbabilityMeasure X) := {γ | d γ π < ε}
  have hUopen : IsOpen U := hdopen ε hε
  have hπU : π ∈ U := by
    simp only [U, mem_ofPred_eq, hd0]
    exact hε
  have hU : U ∈ 𝓝 π := hUopen.mem_nhds hπU
  have h := hface U hU
  refine h.congr' (Filter.Eventually.of_forall fun n ↦ ?_)
  congr 1
  ext ω
  simp only [U, mem_ofPred_eq, not_lt]

end OTSelector
