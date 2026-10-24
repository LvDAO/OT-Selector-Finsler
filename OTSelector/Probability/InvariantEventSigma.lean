import Mathlib.MeasureTheory.Measure.AEMeasurable

/-!
# Invariant Event Sigma

Conditions: An ambient measure and any indexed family of sample-space maps; no group, invertibility or measure-preservation premise is required to define the sigma-algebra.

Objects: The actual sub-sigma-algebra of ambient measurable events whose preimages agree almost everywhere under every map.

Proof detail: Close the defining event property under complement and countable union, prove containment in the ambient sigma-algebra and expose its exact measurable-set characterization.

Relation to primary sources: An indexed a.e.-invariant sigma-algebra generalization of the usual invariant-event field. Its definition itself does not assert stationarity or ergodicity.

References:
* Rick Durrett, Probability: Theory and Examples, fifth edition, author version 11 January 2019, Section 6.1, Example 6.1.4 and invariant-event/ergodicity definitions, pp. 331–332; Exercises 6.1.1–6.1.2, p. 334. https://sites.math.duke.edu/~rtd/PTE/PTE5_011119.pdf#page=340
-/
/-! The actual measurable events preserved almost surely by all rerootings. -/
open Set MeasureTheory Filter
noncomputable section
namespace OTSelector.Probability

/-- The event sigma algebra of all almost surely invariant measurable sets.
The transformations may form an uncountable family; each invariance identity
has its own null set. No ergodicity or decomposition assumption is made. -/
@[instance_reducible]
def aeInvariantEventSigma {Ω I : Type*} [m₀ : MeasurableSpace Ω]
    (P : Measure Ω) (T : I → Ω → Ω) : MeasurableSpace Ω where
  MeasurableSet' A := MeasurableSet A ∧ ∀ i, T i ⁻¹' A =ᵐ[P] A
  measurableSet_empty := ⟨MeasurableSet.empty, fun _ ↦ EventuallyEq.rfl⟩
  measurableSet_compl := by
    intro A hA
    refine ⟨hA.1.compl, fun i ↦ ?_⟩
    filter_upwards [hA.2 i] with x hx
    exact congrArg Not hx
  measurableSet_iUnion := by
    intro A hA
    refine ⟨MeasurableSet.iUnion (fun n ↦ (hA n).1), fun i ↦ ?_⟩
    filter_upwards [ae_all_iff.mpr (fun n ↦ (hA n).2 i)] with x hx
    apply propext
    change (T i x ∈ ⋃ n, A n) ↔ x ∈ ⋃ n, A n
    simp only [mem_iUnion]
    exact exists_congr fun n : ℕ ↦ Iff.of_eq (hx n)

/-- Invariant events are ambient measurable events. -/
theorem aeInvariantEventSigma_le {Ω I : Type*} [m₀ : MeasurableSpace Ω]
    (P : Measure Ω) (T : I → Ω → Ω) : aeInvariantEventSigma P T ≤ m₀ :=
  fun _ hA ↦ hA.1

/-- Membership in the invariant event sigma algebra records exactly the
measurability and almost sure invariance used by actual conditional laws. -/
@[simp]
theorem measurableSet_aeInvariantEventSigma_iff
    {Ω I : Type*} [m₀ : MeasurableSpace Ω] (P : Measure Ω) (T : I → Ω → Ω)
    (A : Set Ω) :
    MeasurableSet[aeInvariantEventSigma P T] A ↔
      MeasurableSet A ∧ ∀ i, T i ⁻¹' A =ᵐ[P] A := Iff.rfl

end OTSelector.Probability
