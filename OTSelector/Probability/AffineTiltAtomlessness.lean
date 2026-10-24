import Mathlib.Analysis.Convex.Birkhoff
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.GroupTheory.Perm.ViaEmbedding
import Mathlib.MeasureTheory.Measure.FiniteMeasureExt
import Mathlib.Probability.Distributions.Beta
import Mathlib.Probability.Independence.Integration
import Mathlib.Topology.Algebra.Module.Cardinality

/-!
Conditions: A probability measure and a measurable real observable.

Objects: Equivalence, in its two directions, between atomlessness of the actual image law and zero collision mass for two independent samples.

Proof detail: A positive image singleton would give a positive product rectangle inside the collision event. Conversely integrate the zero singleton fiber measures by Tonelli.

References: Rick Durrett: Section 1.7, Theorem 1.7.2, p. 38; Rick Durrett: Section 2.1.2, Theorems 2.1.11–2.1.12, p. 48.
Relation: A direct elementary product-measure characterization, proved locally for the actual observable pushforward. No density assumption is needed.
-/

/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Probability.CavityTiltAtomlessness.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Probability.CavityTiltAtomlessness`; the selected original proof blocks follow. -/
section

/-!
# Only countably many perturbations destroy cost-difference atomlessness

On the actual independent source pair, equality of two tilted scores defines a collision
event. Events for distinct tilts intersect only inside the zero-probability base collision
event. The existing countability theorem for almost-disjoint positive-measure sets then
gives a countable exceptional set, without introducing an auxiliary sampling law.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators ENNReal

noncomputable section
namespace OTSelector.Probability

variable {S : Type*} [MeasurableSpace S]

/-- A null independent-pair collision event rules out every atom of the actual image law. -/
theorem nullSingletonClass_map_of_pair_collision_null
    (μ : Measure S) [IsProbabilityMeasure μ] (f : S → ℝ) (hf : Measurable f)
    (hcoll : μ.prod μ {q | f q.1 = f q.2} = 0) : NullSingletonClass (μ.map f) := by
  refine ⟨fun z ↦ ?_⟩
  rw [Measure.map_apply hf (measurableSet_singleton z)]
  have hz : μ (f ⁻¹' {z}) * μ (f ⁻¹' {z}) = 0 := by
    rw [← Measure.prod_prod]
    apply measure_mono_null _ hcoll
    intro q hq
    exact hq.1.trans hq.2.symm
  exact (mul_eq_zero.mp hz).elim id id

/-- An atomless original image law has no independent-pair collisions. -/
theorem measure_pair_collision_eq_zero
    (μ : Measure S) [IsProbabilityMeasure μ] (f : S → ℝ) (hf : Measurable f)
    [NullSingletonClass (μ.map f)] : μ.prod μ {q | f q.1 = f q.2} = 0 := by
  have hzero (x : S) : μ {s | f x = f s} = 0 := by
    have hz : μ (f ⁻¹' {f x}) = 0 := by
      rw [← Measure.map_apply hf (measurableSet_singleton _), measure_singleton]
    simpa only [preimage, mem_singleton_iff, eq_comm] using hz
  have hm : MeasurableSet {q : S × S | f q.1 = f q.2} :=
    measurableSet_eq_fun (hf.comp measurable_fst) (hf.comp measurable_snd)
  rw [Measure.prod_apply hm]
  change (∫⁻ x, μ {s | f x = f s} ∂μ) = 0
  simp_rw [hzero]
  simp







end OTSelector.Probability

end
end
